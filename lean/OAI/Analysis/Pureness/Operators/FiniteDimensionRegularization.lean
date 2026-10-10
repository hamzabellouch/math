import OAI.Analysis.Pureness.Cuntz.FiniteCuntzStates
import OAI.Analysis.Pureness.Divisibility.FiniteCutComparison

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped ENNReal NNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def finiteRegularizedValue (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (n : ℕ) (M : Positive (FinMatrix A n)) : ℝ≥0∞ :=
  ⨆ ε : ℝ≥0, ⨆ (_ : 0 < ε), d (finitePositiveClass n (Positive.cut ε M))

lemma finiteRegularizedValue_inclusion (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    {n m : ℕ} (h : n ≤ m) (M : Positive (FinMatrix A n)) :
    finiteRegularizedValue d m (Positive.map (matrixInclusion h) M) = finiteRegularizedValue d n M := by
  simp only [finiteRegularizedValue, ← Positive.map_cut, finitePositiveClass_inclusion]

lemma finiteRegularizedValue_mono_same (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (hd : Monotone d) (n : ℕ) (M N : Positive (FinMatrix A n))
    (h : CuntzTrace.CuntzBelow M N) : finiteRegularizedValue d n M ≤ finiteRegularizedValue d n N := by
  apply iSup_le
  intro ε
  apply iSup_le
  intro hε
  obtain ⟨δ,hδ,hcut⟩ := exists_cut_cuntzBelow_cut h ε hε
  apply le_iSup_of_le δ
  apply le_iSup_of_le hδ
  apply hd
  exact (finitePositiveClass_le_iff n _ _).mpr ((cuntzSubequiv_iff_shared _ _).mpr hcut)

theorem finiteRegularizedValue_mono (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (hd : Monotone d) {n m : ℕ} (M : Positive (FinMatrix A n)) (N : Positive (FinMatrix A m))
    (h : finitePositiveClass n M ≤ finitePositiveClass m N) :
    finiteRegularizedValue d n M ≤ finiteRegularizedValue d m N := by
  let l := max n m
  let M' := Positive.map (matrixInclusion (le_max_left n m)) M
  let N' := Positive.map (matrixInclusion (le_max_right n m)) N
  have hc : finitePositiveClass l M' ≤ finitePositiveClass l N' := by
    simpa only [M', N', finitePositiveClass_inclusion] using h
  have hab := (cuntzSubequiv_iff_shared M' N').mp ((finitePositiveClass_le_iff l M' N').mp hc)
  have hr := finiteRegularizedValue_mono_same d hd l M' N' hab
  simpa only [M', N', finiteRegularizedValue_inclusion] using hr

lemma finiteRegularizedValue_le (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (hd : Monotone d) (n : ℕ) (M : Positive (FinMatrix A n)) :
    finiteRegularizedValue d n M ≤ d (finitePositiveClass n M) := by
  apply iSup_le
  intro ε
  apply iSup_le
  intro _
  apply hd
  apply (finitePositiveClass_le_iff n _ _).mpr
  exact (cuntzSubequiv_iff_shared _ _).mpr (CuntzTrace.CuntzBelow.of_le _ _ (Positive.cut_le ε M))

lemma cut_class_value_le_regularized (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (n : ℕ) (M : Positive (FinMatrix A n)) (ε : ℝ≥0) (hε : 0 < ε) :
    d (finitePositiveClass n (Positive.cut ε M)) ≤ finiteRegularizedValue d n M :=
  le_iSup_of_le ε (le_iSup_of_le hε le_rfl)

lemma finiteRegularizedValue_zero (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (n : ℕ) :
    finiteRegularizedValue d n Positive.zero = 0 := by
  have hz (ε : ℝ≥0) : Positive.cut ε (Positive.zero : Positive (FinMatrix A n)) = Positive.zero := by
    apply Subtype.ext
    simp [Positive.cut, Positive.zero]
  simp only [finiteRegularizedValue, hz, finitePositiveClass_zero, map_zero]
  exact le_antisymm (iSup_le fun _ => iSup_le fun _ => le_rfl) bot_le

lemma finiteCutValue_antitone (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (hd : Monotone d) (n : ℕ) (M : Positive (FinMatrix A n)) :
    Antitone (fun ε : ℝ≥0 => d (finitePositiveClass n (Positive.cut ε M))) := by
  intro ε δ h
  apply hd
  apply (finitePositiveClass_le_iff n _ _).mpr
  exact (cuntzSubequiv_iff_shared _ _).mpr
    (CuntzTrace.CuntzBelow.of_le _ _ (positive_cut_antitone M h))
end CuntzPureness

end

end OAI
