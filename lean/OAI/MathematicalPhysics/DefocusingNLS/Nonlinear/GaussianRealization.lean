import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.GaussianFourier
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.MeasureTheory.Group.Arithmetic

namespace OAI

/-!
# A measurable Hilbert-valued realization of the Fourier series

The weighted coefficients are realized in the standard `ℓ²` Hilbert model of
the Sobolev norm. The realization is a measurable sum of coordinate vectors,
and agrees almost surely with the prescribed coefficients.
-/

open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal

noncomputable section

namespace DefocusingNLS

abbrev FourierL2 := lp (fun _ : frequencyLattice => ℂ) (2 : ℝ≥0∞)

/-- Finite coordinate vectors have dense complex span, so this Hilbert model
is separable. -/
instance : SeparableSpace FourierL2 := by
  let S : Set FourierL2 := Set.range (fun n => lp.single 2 n (1 : ℂ))
  have hs : TopologicalSpace.IsSeparable S := (Set.countable_range _).isSeparable
  have hspan := hs.span (R := ℂ)
  apply TopologicalSpace.isSeparable_univ_iff.mp
  apply hspan.closure.mono
  intro f _
  change f ∈ (Submodule.span ℂ S).topologicalClosure
  apply (Submodule.isClosed_topologicalClosure (Submodule.span ℂ S)).mem_of_tendsto
    (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) f)
  apply Eventually.of_forall
  intro J
  apply Submodule.sum_mem
  intro n _
  apply (Submodule.span ℂ S).le_topologicalClosure
  have h : lp.single 2 n (1 : ℂ) ∈ Submodule.span ℂ S :=
    Submodule.subset_span ⟨n, rfl⟩
  simpa only [← lp.single_smul, smul_eq_mul, mul_one] using
    (Submodule.span ℂ S).smul_mem (f n) h

instance : MeasurableSpace FourierL2 := borel FourierL2
instance : BorelSpace FourierL2 := ⟨rfl⟩

/-- Measurable Hilbert-valued sum of the weighted Gaussian coordinates. -/
noncomputable def weightedGaussianVector (k α : ℝ)
    (g : frequencyLattice → ℂ) : FourierL2 :=
  ∑' n, lp.single 2 n (weightedGaussianCoefficient k α g n)

theorem measurable_weightedGaussianVector (k α : ℝ) :
    Measurable (weightedGaussianVector k α) := by
  apply Measurable.tsum
  intro n
  apply (lp.isometry_single (p := 2) n).continuous.measurable.comp
  unfold weightedGaussianCoefficient
  fun_prop

/-- In the summable range, the measurable realization has precisely the
prescribed Fourier coefficients almost surely. -/
theorem ae_weightedGaussianVector_coefficients (k α : ℝ) (hα : k + 6 < α) :
    ∀ᵐ g ∂fourierGaussianLaw, ∀ n,
      weightedGaussianVector k α g n = weightedGaussianCoefficient k α g n := by
  filter_upwards [ae_mem_l2_gaussian_coefficients k α hα] with g hg
  have hsum := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    (⟨weightedGaussianCoefficient k α g, hg⟩ : FourierL2)
  intro n
  exact congrArg (fun f : FourierL2 => f n) hsum.tsum_eq

/-- The unweighted Fourier coefficient of an element of the `H^k` model. -/
noncomputable def sobolevFourierCoefficient (k : ℝ) (f : FourierL2)
    (n : frequencyLattice) : ℂ :=
  (1 + ‖n‖ ^ 2) ^ (-k / 2) • f n

/-- Undoing the Sobolev weight gives exactly `gₙ / ⟨n⟩^α`. -/
theorem ae_sobolevFourierCoefficient (k α : ℝ) (hα : k + 6 < α) :
    ∀ᵐ g ∂fourierGaussianLaw, ∀ n,
      sobolevFourierCoefficient k (weightedGaussianVector k α g) n =
        (1 + ‖n‖ ^ 2) ^ (-α / 2) • g n := by
  filter_upwards [ae_weightedGaussianVector_coefficients k α hα] with g hg
  intro n
  rw [sobolevFourierCoefficient, hg, weightedGaussianCoefficient_eq_rpow,
    smul_smul, ← Real.rpow_add (by positivity)]
  congr 2
  ring

/-- The corresponding probability law in the Hilbert model. -/
noncomputable def weightedGaussianLaw (k α : ℝ) : Measure FourierL2 :=
  fourierGaussianLaw.map (weightedGaussianVector k α)

instance (k α : ℝ) : IsProbabilityMeasure (weightedGaussianLaw k α) := by
  unfold weightedGaussianLaw
  infer_instance

end DefocusingNLS

end

end OAI
