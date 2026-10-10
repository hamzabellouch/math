import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CuntzSemigroup.FiniteCuntzStates
import OAI.Analysis.JiangSu.Comparison.FiniteCutComparison

namespace OAI

noncomputable section
namespace Pureness
open TraceCone
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
    (h : TraceCone.CuntzBelow M N) : finiteRegularizedValue d n M ≤ finiteRegularizedValue d n N := by
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
  exact (cuntzSubequiv_iff_shared _ _).mpr (TraceCone.CuntzBelow.of_le _ _ (Positive.cut_le ε M))

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
    (TraceCone.CuntzBelow.of_le _ _ (positive_cut_antitone M h))

lemma positiveProduct_cut {D : Type*} [NonUnitalCStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] (ε : ℝ≥0) (a b : Positive D) :
    Positive.cut ε (positiveProduct a b) = positiveProduct (Positive.cut ε a) (Positive.cut ε b) := by
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Subtype.val (Positive.map_cut (NonUnitalStarAlgHom.fst ℂ D D) ε (positiveProduct a b))
  · exact congrArg Subtype.val (Positive.map_cut (NonUnitalStarAlgHom.snd ℂ D D) ε (positiveProduct a b))

lemma finitePositiveClass_cut_add (n : ℕ) (M N : Positive (FinMatrix A n)) (ε : ℝ≥0) :
    finitePositiveClass (n*2) (Positive.cut ε (Positive.map (matrixInterleave n) (positiveProduct M N))) =
      finitePositiveClass n (Positive.cut ε M) + finitePositiveClass n (Positive.cut ε N) := by
  rw [← Positive.map_cut, positiveProduct_cut, finitePositiveClass_add]

theorem finiteRegularizedValue_add (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (hd : Monotone d) (n : ℕ) (M N : Positive (FinMatrix A n)) :
    finiteRegularizedValue d (n*2) (Positive.map (matrixInterleave n) (positiveProduct M N)) =
      finiteRegularizedValue d n M + finiteRegularizedValue d n N := by
  apply le_antisymm
  · apply iSup_le
    intro ε
    apply iSup_le
    intro hε
    rw [finitePositiveClass_cut_add, map_add]
    exact add_le_add (cut_class_value_le_regularized d n M ε hε)
      (cut_class_value_le_regularized d n N ε hε)
  · apply ENNReal.biSup_add_biSup_le' (show ∃ ε : ℝ≥0, 0 < ε from ⟨1,zero_lt_one⟩)
      (show ∃ ε : ℝ≥0, 0 < ε from ⟨1,zero_lt_one⟩)
    intro ε hε δ hδ
    apply le_iSup_of_le (min ε δ)
    apply le_iSup_of_le (lt_min hε hδ)
    rw [finitePositiveClass_cut_add, map_add]
    exact add_le_add (finiteCutValue_antitone d hd n M (min_le_left _ _))
      (finiteCutValue_antitone d hd n N (min_le_right _ _))

lemma finiteClass_has_representative (x : finiteCuntzSubmonoid (A := A)) :
    ∃ r : Σ n : ℕ, Positive (FinMatrix A n), finitePositiveClass r.1 r.2 = x := by
  obtain ⟨n,M,h⟩ := x.2
  exact ⟨⟨n,M⟩,Subtype.ext h.symm⟩

def finiteClassRepresentative (x : finiteCuntzSubmonoid (A := A)) :
    Σ n : ℕ, Positive (FinMatrix A n) := Classical.choose (finiteClass_has_representative x)

lemma finiteClassRepresentative_spec (x : finiteCuntzSubmonoid (A := A)) :
    finitePositiveClass (finiteClassRepresentative x).1 (finiteClassRepresentative x).2 = x :=
  Classical.choose_spec (finiteClass_has_representative x)

def finiteRegularizedFunction (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (x : finiteCuntzSubmonoid (A := A)) : ℝ≥0∞ :=
  finiteRegularizedValue d (finiteClassRepresentative x).1 (finiteClassRepresentative x).2

theorem finiteRegularizedFunction_eval (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (hd : Monotone d) (n : ℕ) (M : Positive (FinMatrix A n)) :
    finiteRegularizedFunction d (finitePositiveClass n M) = finiteRegularizedValue d n M := by
  apply le_antisymm
  · exact finiteRegularizedValue_mono d hd _ _ (finiteClassRepresentative_spec _).le
  · exact finiteRegularizedValue_mono d hd _ _ (finiteClassRepresentative_spec _).ge

lemma finiteRegularizedFunction_monotone (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (hd : Monotone d) : Monotone (finiteRegularizedFunction d) := by
  intro x y h
  exact finiteRegularizedValue_mono d hd _ _ (by simpa only [finiteClassRepresentative_spec] using h)

lemma finiteRegularizedFunction_add (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (hd : Monotone d) (x y : finiteCuntzSubmonoid (A := A)) :
    finiteRegularizedFunction d (x+y) = finiteRegularizedFunction d x + finiteRegularizedFunction d y := by
  obtain ⟨⟨n,M⟩,rfl⟩ := finiteClass_has_representative x
  obtain ⟨⟨m,N⟩,rfl⟩ := finiteClass_has_representative y
  have hM := finitePositiveClass_inclusion (le_max_left n m) M
  have hN := finitePositiveClass_inclusion (le_max_right n m) N
  rw [← hM, ← hN, ← finitePositiveClass_add]
  simp only [finiteRegularizedFunction_eval d hd]
  exact finiteRegularizedValue_add d hd _ _ _

def regularizedFiniteDimension (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (hd : Monotone d) : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞ where
  toFun := finiteRegularizedFunction d
  map_zero' := by
    rw [← finitePositiveClass_zero (A := A) 0, finiteRegularizedFunction_eval d hd,
      finiteRegularizedValue_zero]
  map_add' := finiteRegularizedFunction_add d hd

theorem regularizedFiniteDimension_monotone (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (hd : Monotone d) : Monotone (regularizedFiniteDimension d hd) := finiteRegularizedFunction_monotone d hd

theorem finiteRegularizedValue_lowerSemicontinuous
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d) (n : ℕ) :
    LowerSemicontinuous (finiteRegularizedValue d n) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro r
  apply Metric.isOpen_iff.mpr
  intro M hM
  change r < finiteRegularizedValue d n M at hM
  obtain ⟨ε,hε⟩ := lt_iSup_iff.mp hM
  obtain ⟨hεpos,hcut⟩ := lt_iSup_iff.mp hε
  refine ⟨(ε : ℝ)/2, half_pos hεpos, ?_⟩
  intro N hN
  have hdist : dist M N < (ε : ℝ)/2 := by simpa only [Metric.mem_ball, dist_comm] using hN
  have hc := cut_cuntzBelow_cut_of_dist ε hεpos hdist
  have horder : finitePositiveClass n (Positive.cut ε M) ≤
      finitePositiveClass n (Positive.cut (ε/2) N) :=
    (finitePositiveClass_le_iff n _ _).mpr ((cuntzSubequiv_iff_shared _ _).mpr hc)
  exact hcut.trans_le ((hd horder).trans (cut_class_value_le_regularized d n N (ε/2) (by positivity)))

@[simp] theorem regularizedFiniteDimension_eval
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n)) :
    regularizedFiniteDimension d hd (finitePositiveClass n M) = finiteRegularizedValue d n M :=
  finiteRegularizedFunction_eval d hd n M

theorem regularizedFiniteDimension_le
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (x : finiteCuntzSubmonoid (A := A)) : regularizedFiniteDimension d hd x ≤ d x := by
  obtain ⟨⟨n,M⟩,rfl⟩ := finiteClass_has_representative x
  rw [regularizedFiniteDimension_eval]
  exact finiteRegularizedValue_le d hd n M

lemma cut_value_le_twice_regularized
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n)) (ε : ℝ≥0) (hε : 0 < ε) :
    d (finitePositiveClass n (Positive.cut ε M)) ≤
      finiteRegularizedValue (regularizedFiniteDimension d hd) n M := by
  apply le_iSup_of_le (ε/2)
  apply le_iSup_of_le (show 0 < ε/2 from by positivity)
  rw [regularizedFiniteDimension_eval]
  apply le_iSup_of_le (ε/2)
  apply le_iSup_of_le (show 0 < ε/2 from by positivity)
  rw [Positive.cut_cut, add_halves]

theorem regularizedFiniteDimension_idempotent
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d) :
    regularizedFiniteDimension (regularizedFiniteDimension d hd)
      (regularizedFiniteDimension_monotone d hd) = regularizedFiniteDimension d hd := by
  ext x
  apply le_antisymm (regularizedFiniteDimension_le _ _ x)
  obtain ⟨⟨n,M⟩,rfl⟩ := finiteClass_has_representative x
  rw [regularizedFiniteDimension_eval, regularizedFiniteDimension_eval]
  exact iSup_le fun ε => iSup_le fun hε => cut_value_le_twice_regularized d hd n M ε hε

theorem regularizedFiniteDimension_eq_of_lowerSemicontinuous
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M))) :
    regularizedFiniteDimension d hd = d := by
  ext x
  apply le_antisymm (regularizedFiniteDimension_le d hd x)
  obtain ⟨⟨n,M⟩,rfl⟩ := finiteClass_has_representative x
  rw [regularizedFiniteDimension_eval]
  let ε : ℕ → ℝ≥0 := fun j => 1 / ((j : ℝ≥0)+1)
  have hε : Filter.Tendsto (fun j => (ε j : ℝ)) Filter.atTop (nhds 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Filter.Tendsto (fun j : ℕ => 1 / ((j : ℝ)+1)) Filter.atTop (nhds 0))
  exact ((hlsc n).isClosed_preimage (finiteRegularizedValue d n M)).mem_of_tendsto
    (Positive.tendsto_cut ε hε M) (Filter.Eventually.of_forall fun j =>
      cut_class_value_le_regularized d n M (ε j) (by dsimp [ε]; positivity))

end Pureness
end

end OAI
