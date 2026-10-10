import OAI.NumberTheory.CubicMoment.Estimates.PrimeIndicatorCollection
import OAI.NumberTheory.CubicMoment.Estimates.RepeatedPrimeCutoffMoments

namespace OAI

/-! Actual squarefree replacement errors in the two exceptional regions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def squarefreeCoordinateError (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ z ∈ coordinatePrimeCutoff W X Y,
    squarefreeConvolutionError (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) z*
      (mixedCubic a b z*V (norm z/Y))

 theorem first_squarefreeCoordinateError_moment {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (W : ι → ℝ → ℂ) (M X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ), 1 ≤ Y →
      (∀ i, q i ≠ 0) → (∀ i, 0 ≤ M i) → (∀ i x, ‖W i x‖ ≤ M i) →
      (∀ i x, x < 1 → W i x = 0) → (∀ i, (2*Y)^c < X i) →
      (∀ x, ‖V x‖ ≤ 1) → ∀ P : Finset Eisenstein,
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ (2*Y)^(1+c/32)) →
      (∑ a ∈ P, ‖squarefreeCoordinateError a 1 q η t W X V Y‖^2) ≤
        C*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2*(2*Y)^(7/3-c/4) := by
  obtain ⟨C,hC,hbound⟩ := repeatedPrime_first_shape_cutoff_moment (ι := ι) hc hc₁
  refine ⟨C,hC,?_⟩
  intro q η t W M X V Y hY hq hM hW hWlo hX hV P hP
  have hYp : 0 < 2*Y := by linarith
  have hXpos : ∀ i, 0 < X i := fun i => (Real.rpow_pos_of_pos hYp c).trans (hX i)
  have hS : ∀ i, ∀ p ∈ coordinatePrimeSupport W X Y i,
      primaryPrime p ∧ (2*Y)^c < norm p := by
    intro i p hp
    exact ⟨coordinatePrimeSupport_primary W X Y i p hp,
      (coordinateSupport_lower W X Y ((2*Y)^c) hWlo hXpos hX i p
        (Finset.mem_filter.mp hp).1).2⟩
  have hB := coordinatePrimeCutoff_spec W X Y
  have hQ : ∀ b ∈ ({1}:Finset Eisenstein), primary b ∧ norm b ≤ (2*Y)^(c/32) := by
    intro b hb
    have he : b = 1 := Finset.mem_singleton.mp hb
    subst b
    constructor
    · norm_num [primary]
    · simpa using Real.one_le_rpow (show 1 ≤ 2*Y by linarith) (show 0 ≤ c/32 by positivity)
  have hh := hbound (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) M (2*Y)
    (by linarith) hM hS (coordinatePrimeCutoff W X Y) hB.1 hB.2
    (fun i n _ => coordinateFactor_bound q hq η t W X M hW i n) P {1} hP hQ
    (fun z => V (norm z/Y)) (fun z _ => hV _)
  simp only [Finset.sum_singleton] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro a ha
  congr 2
  apply Finset.sum_congr rfl
  intro z hz
  ring

 theorem balanced_squarefreeCoordinateError_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (W : ι → ℝ → ℂ) (M X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ), 1 ≤ Y →
      (∀ i, q i ≠ 0) → (∀ i, 0 ≤ M i) → (∀ i x, ‖W i x‖ ≤ M i) →
      (∀ i x, x < 1 → W i x = 0) → (∀ i, (2*Y)^c < X i) →
      (∀ x, ‖V x‖ ≤ 1) → ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ (2*Y)^(1/3+c/32) ∧
        norm a.2 ≤ (2*Y)^(1/3+c/32)) →
      (∑ a ∈ P, ‖squarefreeCoordinateError a.1 a.2 q η t W X V Y‖^2) ≤
        C*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2*(2*Y)^(7/3-c/4) := by
  obtain ⟨C,hC,hbound⟩ := repeatedPrime_balanced_cutoff_moment (ι := ι) hHuxley hc hc₁
  refine ⟨C,hC,?_⟩
  intro q η t W M X V Y hY hq hM hW hWlo hX hV P hP
  have hYp : 0 < 2*Y := by linarith
  have hXpos : ∀ i, 0 < X i := fun i => (Real.rpow_pos_of_pos hYp c).trans (hX i)
  have hS : ∀ i, ∀ p ∈ coordinatePrimeSupport W X Y i,
      primaryPrime p ∧ (2*Y)^c < norm p := by
    intro i p hp
    exact ⟨coordinatePrimeSupport_primary W X Y i p hp,
      (coordinateSupport_lower W X Y ((2*Y)^c) hWlo hXpos hX i p
        (Finset.mem_filter.mp hp).1).2⟩
  have hB := coordinatePrimeCutoff_spec W X Y
  have hh := hbound (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) M (2*Y)
    (by linarith) hM hS (coordinatePrimeCutoff W X Y) hB.1 hB.2
    (fun i n _ => coordinateFactor_bound q hq η t W X M hW i n) P hP
    (fun z => V (norm z/Y)) (fun z _ => hV _)
  convert hh using 1
  apply Finset.sum_congr rfl
  intro a ha
  congr 2
  apply Finset.sum_congr rfl
  intro z hz
  ring

end CubicFirstMoment

end

end OAI
