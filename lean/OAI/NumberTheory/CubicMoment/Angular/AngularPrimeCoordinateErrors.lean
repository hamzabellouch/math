import OAI.NumberTheory.CubicMoment.Angular.AngularPrimeCoordinateCollection
import OAI.NumberTheory.CubicMoment.Estimates.PrimeLogCutoffMoments

namespace OAI

/-! The actual angular replacement errors obey the unchanged sparse
moment estimates; theta is included in the bounded outer coefficient. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem first_angular_primeCoordinateError_moment {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℤ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (W : ι → ℝ → ℂ) (M X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ), 1 ≤ Y →
      (∀ i, q i ≠ 0) → (∀ i, 0 ≤ M i) → (∀ i x, ‖W i x‖ ≤ M i) →
      (∀ i x, x < 1 → W i x = 0) → (∀ i, (2*Y)^c < X i) →
      (∀ x, ‖V x‖ ≤ 1) → ∀ P : Finset Eisenstein,
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ (2*Y)^(1+c/256)) →
      (∑ a ∈ P, ‖angularPrimeCoordinateError ℓ a 1 q η t W X V Y‖^2) ≤
        C*(∏ i, M i)^2*(2*Y)^(7/3-c/32) := by
  obtain ⟨C,hC,hbound⟩ := primeLogConvolution_first_shape_cutoff_moment (ι := ι) hc hc₁
  refine ⟨C,hC,?_⟩
  intro ℓ q η t W M X V Y hY hq hM hW hWlo hX hV P hP
  have hYp : 0 < 2*Y := by linarith
  have hXpos : ∀ i, 0 < X i := fun i => (Real.rpow_pos_of_pos hYp c).trans (hX i)
  have hS := coordinateSupport_lower W X Y ((2*Y)^c) hWlo hXpos hX
  have hB := coordinateProductCutoff_spec W X Y
  have hQ : ∀ b ∈ ({1}:Finset Eisenstein), primary b ∧ norm b ≤ (2*Y)^(c/256) := by
    intro b hb
    have he : b = 1 := Finset.mem_singleton.mp hb
    subst b
    constructor
    · norm_num [primary]
    · simpa using Real.one_le_rpow (show 1 ≤ 2*Y by linarith) (show 0 ≤ c/256 by positivity)
  have hχ (z : Eisenstein) (hz : z ∈ coordinateProductCutoff W X Y) :
      ‖theta ℓ z*V (norm z/Y)‖ ≤ 1 := by
    have hp := orderedPrimarySupport_primary (coordinateSupport W X Y)
        (coordinateSupport_primary W X Y) (hB.1 hz)
    rw [norm_mul,norm_theta (primary_ne_zero hp) ℓ,one_mul]
    exact hV _
  have hh := hbound (coordinateSupport W X Y) (coordinateFactor q η t W X) M (2*Y)
    (by linarith) hM hS (coordinateProductCutoff W X Y) hB.1 hB.2
    (fun i n _ => coordinateFactor_bound q hq η t W X M hW i n) P {1} hP hQ
    (fun z => theta ℓ z*V (norm z/Y)) hχ
  simp only [Finset.sum_singleton] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro a ha
  congr 2
  apply Finset.sum_congr rfl
  intro z hz
  ring

 theorem balanced_angular_primeCoordinateError_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℤ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (W : ι → ℝ → ℂ) (M X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ), 1 ≤ Y →
      (∀ i, q i ≠ 0) → (∀ i, 0 ≤ M i) → (∀ i x, ‖W i x‖ ≤ M i) →
      (∀ i x, x < 1 → W i x = 0) → (∀ i, (2*Y)^c < X i) →
      (∀ x, ‖V x‖ ≤ 1) → ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ (2*Y)^(1/3+c/256) ∧
        norm a.2 ≤ (2*Y)^(1/3+c/256)) →
      (∑ a ∈ P, ‖angularPrimeCoordinateError ℓ a.1 a.2 q η t W X V Y‖^2) ≤
        C*(∏ i, M i)^2*(2*Y)^(7/3-c/32) := by
  obtain ⟨C,hC,hbound⟩ := primeLogConvolution_balanced_cutoff_moment (ι := ι) hHuxley hc hc₁
  refine ⟨C,hC,?_⟩
  intro ℓ q η t W M X V Y hY hq hM hW hWlo hX hV P hP
  have hYp : 0 < 2*Y := by linarith
  have hXpos : ∀ i, 0 < X i := fun i => (Real.rpow_pos_of_pos hYp c).trans (hX i)
  have hS := coordinateSupport_lower W X Y ((2*Y)^c) hWlo hXpos hX
  have hB := coordinateProductCutoff_spec W X Y
  have hχ (z : Eisenstein) (hz : z ∈ coordinateProductCutoff W X Y) :
      ‖theta ℓ z*V (norm z/Y)‖ ≤ 1 := by
    have hp := orderedPrimarySupport_primary (coordinateSupport W X Y)
        (coordinateSupport_primary W X Y) (hB.1 hz)
    rw [norm_mul,norm_theta (primary_ne_zero hp) ℓ,one_mul]
    exact hV _
  have hh := hbound (coordinateSupport W X Y) (coordinateFactor q η t W X) M (2*Y)
    (by linarith) hM hS (coordinateProductCutoff W X Y) hB.1 hB.2
    (fun i n _ => coordinateFactor_bound q hq η t W X M hW i n) P hP
    (fun z => theta ℓ z*V (norm z/Y)) hχ
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
