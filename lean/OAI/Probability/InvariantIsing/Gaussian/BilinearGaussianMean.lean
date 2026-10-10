import OAI.Probability.InvariantIsing.Gaussian.BilinearGaussianComparison
import OAI.Probability.InvariantIsing.Gaussian.IndexedGaussianIntegrability

namespace OAI

/-! The sharp expected maximum estimate for every finite family of unit bilinear tests. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing
variable {X : Type*} [Fintype X] [Nonempty X] {N m : ℕ}

lemma bilinearMatrix_maximum_eq
    (u : X → EuclideanSpace ℝ (Fin N)) (v : X → EuclideanSpace ℝ (Fin m))
    (g : BilinearGaussianIndex N m → ℝ) :
    indexedGaussianMaximum (bilinearMatrixCoefficient u v) g =
      indexedGaussianMaximum (fun x (ij : Fin N × Fin m) => u x ij.1*v x ij.2)
        (fun ij => g (.inl (.inl ij))) + g (.inl (.inr ())) := by
  unfold indexedGaussianMaximum
  simp only [Fintype.sum_sum_type,bilinearMatrixCoefficient,zero_mul,
    one_mul,Finset.sum_const_zero,Fintype.sum_unique,add_zero]
  exact indexedGaussianMaximum_add_constant _ _ _

theorem bilinear_gaussian_mean_le
    (u : X → EuclideanSpace ℝ (Fin N)) (v : X → EuclideanSpace ℝ (Fin m))
    (hu : ∀ x, ‖u x‖ = 1) (hv : ∀ x, ‖v x‖ = 1) :
    (∫ g, indexedGaussianMaximum (fun x (ij : Fin N × Fin m) => u x ij.1*v x ij.2) g
      ∂Measure.pi (fun _ : Fin N × Fin m => gaussianReal 0 1)) ≤
      Real.sqrt N + Real.sqrt m := by
  let μ := Measure.pi (fun _ : BilinearGaussianIndex N m => gaussianReal 0 1)
  let e : Fin N × Fin m → BilinearGaussianIndex N m := fun ij => .inl (.inl ij)
  let D : X → (Fin N × Fin m) → ℝ := fun x ij => u x ij.1*v x ij.2
  have he : Function.Injective e := fun _ _ h => Sum.inl.inj (Sum.inl.inj h)
  have hD := indexedGaussianMaximum_integrable D
  have hR := iidGaussian_restrict_hasLaw e he
  have hc : Integrable (fun g : BilinearGaussianIndex N m → ℝ => g (.inl (.inr ()))) μ :=
    (gaussianCoordinate_memLp _).integrable (by norm_num)
  have hzero : (∫ g : BilinearGaussianIndex N m → ℝ, g (.inl (.inr ())) ∂μ) = 0 := by
    simpa only [μ,integral_id_gaussianReal] using
      (measurePreserving_eval (fun _ : BilinearGaussianIndex N m => gaussianReal 0 1)
        (.inl (.inr ()))).hasLaw.integral_eq
  have hleft : (∫ g, indexedGaussianMaximum (bilinearMatrixCoefficient u v) g ∂μ) =
      ∫ g, indexedGaussianMaximum D g ∂Measure.pi (fun _ : Fin N × Fin m => gaussianReal 0 1) := by
    simp_rw [bilinearMatrix_maximum_eq]
    change (∫ g, (indexedGaussianMaximum D ∘ (fun g : BilinearGaussianIndex N m → ℝ =>
      fun j => g (e j))) g + g (.inl (.inr ())) ∂μ) = _
    rw [integral_add (hR.integrable_comp hD) hc,hzero,add_zero]
    exact hR.integral_comp hD.aestronglyMeasurable
  let eu : Fin N → BilinearGaussianIndex N m := fun i => .inr (.inl i)
  let ev : Fin m → BilinearGaussianIndex N m := fun j => .inr (.inr j)
  have hub := ((gaussianCoordinateVector_memLp eu).integrable (by norm_num)).norm
  have hvb := ((gaussianCoordinateVector_memLp ev).integrable (by norm_num)).norm
  have hright : (∫ g, indexedGaussianMaximum (bilinearVectorCoefficient u v) g ∂μ) ≤
      (∫ g, ‖gaussianCoordinateVector eu g‖ ∂μ) +
        ∫ g, ‖gaussianCoordinateVector ev g‖ ∂μ := by
    rw [← integral_add hub hvb]
    apply integral_mono (indexedGaussianMaximum_integrable _) (hub.add hvb)
    intro g
    apply Finset.sup'_le
    intro x _
    have hu' := real_inner_le_norm (u x) (gaussianCoordinateVector eu g)
    have hv' := real_inner_le_norm (v x) (gaussianCoordinateVector ev g)
    rw [hu,one_mul] at hu'
    rw [hv,one_mul] at hv'
    convert add_le_add hu' hv' using 1
    simp only [Fintype.sum_sum_type,bilinearVectorCoefficient,zero_mul,
      Finset.sum_const_zero,zero_add,EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct,star_trivial,gaussianCoordinateVector,eu,ev,mul_comm]
  calc
    _ = ∫ g, indexedGaussianMaximum (bilinearMatrixCoefficient u v) g ∂μ := hleft.symm
    _ ≤ ∫ g, indexedGaussianMaximum (bilinearVectorCoefficient u v) g ∂μ :=
      bilinear_gaussian_maximum_comparison u v hu hv
    _ ≤ _ := hright
    _ ≤ Real.sqrt N + Real.sqrt m := by
      simpa only [Fintype.card_fin] using add_le_add
        (gaussianCoordinateVector_norm_integral_le eu) (gaussianCoordinateVector_norm_integral_le ev)

end InvariantIsing

end

end OAI
