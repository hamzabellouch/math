import Mathlib
import OAI.Probability.SphericalField.Positivity.Duplication

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
def patternMatrices {κ : Type*} {n : ℕ} (labels : Fin n → κ)
    (C : κ → κ → Set ℝ) : Set (OverlapBlock n) :=
  {B | ∀ i j, i ≠ j → B i j ∈ C (labels i) (labels j)}

lemma patternMatrices_measurable {κ : Type*} {n : ℕ} (labels : Fin n → κ)
    (C : κ → κ → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) :
    MeasurableSet (patternMatrices labels C) := by
  simp only [patternMatrices, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact (hC _ _).preimage ((measurable_pi_apply j).comp (measurable_pi_apply i))

def appendLabel {κ : Type*} {n : ℕ} (labels : Fin n → κ) (k : κ) : Fin (n + 1) → κ :=
  Fin.lastCases k labels

@[simp] lemma appendLabel_last {κ : Type*} {n : ℕ} (labels : Fin n → κ) (k : κ) :
    appendLabel labels k (Fin.last n) = k := Fin.lastCases_last

@[simp] lemma appendLabel_castSucc {κ : Type*} {n : ℕ} (labels : Fin n → κ) (k : κ)
    (i : Fin n) : appendLabel labels k i.castSucc = labels i := Fin.lastCases_castSucc i

lemma pattern_append_of_duplicate {κ : Type*} {n : ℕ} (labels : Fin n → κ)
    (C : κ → κ → Set ℝ) (p : Fin n) (t : ℝ) (hdiag : C (labels p) (labels p) = Iio t)
    (Q : OverlapArray) (hSym : ∀ i j, Q i j = Q j i)
    (hA : overlapBlock id n Q ∈ patternMatrices labels C)
    (hB : replaceBlock p n Q ∈ patternMatrices labels C) (hedge : Q p n < t) :
    overlapBlock id (n + 1) Q ∈ patternMatrices (appendLabel labels (labels p)) C := by
  intro i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · intro j
    refine Fin.lastCases (fun h => (h rfl).elim) (fun b _ => ?_) j
    by_cases hb : b = p
    · subst b
      simpa [overlapBlock, hdiag, hSym n p] using hedge
    · have h := hB p b (Ne.symm hb)
      simpa [replaceBlock, replaceIndex, hb, overlapBlock] using h
  · intro j
    refine Fin.lastCases (fun _ => ?_) (fun b hab => ?_) j
    · by_cases ha : a = p
      · subst a
        simpa [overlapBlock, hdiag] using hedge
      · have h := hB a p ha
        simpa [replaceBlock, replaceIndex, ha, overlapBlock] using h
    · have h := hA a b (fun h => hab (congrArg Fin.castSucc h))
      simpa [overlapBlock] using h

theorem gg_pattern_append (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    {κ : Type*} {r : ℕ} (hr : 1 ≤ r) (labels : Fin (r + 1) → κ)
    (C : κ → κ → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) (p : Fin (r + 1)) (t : ℝ)
    (hdiag : C (labels p) (labels p) = Iio t) (hcut : ∀ k l, C k l ⊆ Iio t)
    (hA : 0 < μ.real (overlapBlock id (r + 1) ⁻¹' patternMatrices labels C)) :
    0 < μ.real (overlapBlock id (r + 1 + 1) ⁻¹'
      patternMatrices (appendLabel labels (labels p)) C) := by
  have hd := gg_duplicate_index μ hEx hGG hr p (patternMatrices_measurable labels C hC) t hA
    (fun Q hQ j hj => hcut _ _ (hQ p j (Ne.symm hj)))
  apply hd.trans_le
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hSym] with Q hQ
  exact fun h => pattern_append_of_duplicate labels C p t hdiag Q hQ h.1.1 h.1.2 h.2

lemma gg_pattern_append_nat (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    {κ : Type*} {n : ℕ} (hn : 2 ≤ n) (labels : Fin n → κ)
    (C : κ → κ → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) (p : Fin n) (t : ℝ)
    (hdiag : C (labels p) (labels p) = Iio t) (hcut : ∀ k l, C k l ⊆ Iio t)
    (hA : 0 < μ.real (overlapBlock id n ⁻¹' patternMatrices labels C)) :
    0 < μ.real (overlapBlock id (n + 1) ⁻¹'
      patternMatrices (appendLabel labels (labels p)) C) := by
  cases n with
  | zero => omega
  | succ r => exact gg_pattern_append μ hEx hGG hSym (by omega) labels C hC p t hdiag hcut hA

def tripleLabels (n : ℕ) (i : Fin n) : Fin 3 := ⟨i.val % 3, Nat.mod_lt _ (by omega)⟩

lemma appendLabel_tripleLabels {n : ℕ} (hn : 3 ≤ n) :
    appendLabel (tripleLabels n) (tripleLabels n ⟨n % 3, (Nat.mod_lt _ (by omega)).trans_le hn⟩) =
      tripleLabels (n + 1) := by
  funext i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · apply Fin.ext
    simp [tripleLabels]
  · exact appendLabel_castSucc _ _ _

theorem gg_triple_pattern (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (C : Fin 3 → Fin 3 → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) (t : ℝ)
    (hdiag : ∀ k, C k k = Iio t) (hcut : ∀ k l, C k l ⊆ Iio t)
    (hA : 0 < μ.real (overlapBlock id 3 ⁻¹' patternMatrices (tripleLabels 3) C)) :
    ∀ n ≥ 3, 0 < μ.real (overlapBlock id n ⁻¹' patternMatrices (tripleLabels n) C) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hA
  | succ n hn ih =>
    have h := gg_pattern_append_nat μ hEx hGG hSym (by omega) (tripleLabels n) C hC
      ⟨n % 3, (Nat.mod_lt _ (by omega)).trans_le hn⟩ t (hdiag _) hcut ih
    rwa [appendLabel_tripleLabels hn] at h

open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

end SphericalPerceptron
end
end

end OAI
