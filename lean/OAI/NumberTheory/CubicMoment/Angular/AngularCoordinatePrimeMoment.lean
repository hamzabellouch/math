import OAI.NumberTheory.CubicMoment.Angular.AngularPrimeTupleSize
import OAI.NumberTheory.CubicMoment.Estimates.IndependentMellinMoment
import OAI.NumberTheory.CubicMoment.Estimates.PrimeCoordinatePowers

namespace OAI

/-! Coordinate Mellin transfer for the actual independently weighted
von Mangoldt tuple sum, with a polynomial bound for every tail row. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

 theorem angular_coordinate_vonMangoldt_moment_bound (r : κ → Eisenstein × Eisenstein)
    (hr : ∀ j, primary (r j).1 ∧ primary (r j).2)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hq : ∀ i, q i ≠ 0) (t : ι → ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i)
    (V : ℝ → ℂ) {M Y : ℝ} (hM : 0 ≤ M) (hV : ∀ x, ‖V x‖ ≤ M) (hY : 0 ≤ Y)
    (A : ℕ) {T B : ℝ} (hT : 0 < T) (hB : 0 ≤ B)
    (hbound : ∀ τ ∈ mellinHeightBox T,
      (∑ j, ‖primaryAngularUnsplitTuple ℓ (fun _ : ι => idealVonMangoldt)
        (r j).1 (r j).2 q η (fun i => t i-τ i) V Y‖^2) ≤ B) :
    (∑ j, ‖primaryAngularCoordinateWeightedTuple ℓ (fun _ : ι => idealVonMangoldt)
      (r j).1 (r j).2 q η t W X V Y‖^2) ≤
      2*(∏ i, zeroLineMellinMass (W i))^2*B+
        2*(Fintype.card κ:ℝ)*
          (((M*72^(Fintype.card ι))*Y^(2*Fintype.card ι)/T^A)*independentMellinMoment W A)^2 := by
  let f : κ → (ι → ℝ) → ℂ := fun j τ =>
    primaryAngularUnsplitTuple ℓ (fun _ : ι => idealVonMangoldt) (r j).1 (r j).2 q η
      (fun i => t i-τ i) V Y
  have hf (j : κ) : Continuous (f j) :=
    (continuous_primaryAngularUnsplitTuple ℓ _ _ _ q η V Y).comp (by fun_prop)
  have hsize (j : κ) (τ : ι → ℝ) :
      ‖f j τ‖ ≤ (M*72^(Fintype.card ι))*Y^(2*Fintype.card ι) :=
    angular_vonMangoldt_unsplit_size ℓ _ _ (hr j).1 (hr j).2 q η hq _ V hM hV hY
  have hm := independent_mellin_integral_moment f hf W X hW hpos hsm hX A hT
    (show 0 ≤ (M*72^(Fintype.card ι))*Y^(2*Fintype.card ι) by positivity) hB hsize hbound
  have he (j : κ) := primaryAngularCoordinateWeightedTuple_mellin ℓ (fun _ : ι => idealVonMangoldt)
    (r j).1 (r j).2 q η t W X V Y hW hpos hsm hX
  simpa only [he] using hm

end CubicFirstMoment

end

end OAI
