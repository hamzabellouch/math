import OAI.Analysis.BernoulliCone.HarmonicCaccioppoli

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff BigOperators
namespace Bernoulli
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)}
namespace Test
lemma directional {φ : Space d → ℝ} (hφ : Test D φ) (e : Space d) :
    Test D (fun x => fderiv ℝ φ x e) := by
  refine ⟨(hφ.1.fderiv_right (by simp)).clm_apply contDiff_const,
    hφ.2.1.fderiv_apply ℝ e, (tsupport_fderiv_apply_subset ℝ e).trans hφ.2.2⟩
end Test

/-- Distributional integration by parts against the Euclidean Laplacian;
no second derivatives of the Sobolev function occur in this statement. -/
lemma H1.laplacian_ibp {u : Space d → ℝ} {G : Space d → Space d}
    (hu : H1 D u G) {φ : Space d → ℝ} (hφ : Test D φ) :
    (∫ x in D, u x * Laplacian.laplacian φ x) =
      -(∫ x in D, inner ℝ (G x) (gradient φ x)) := by
  let b := stdOrthonormalBasis ℝ (Space d)
  have hi (i : Fin (Module.finrank ℝ (Space d))) :=
    hu.2.2 _ (hφ.directional (b i)) (b i)
  have hs (x : Space d) : Laplacian.laplacian φ x =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ φ y (b i)) x (b i) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ b]
    apply Finset.sum_congr rfl
    intro i _
    rw [iteratedFDeriv_two_apply]
    -- evaluation of a continuously differentiable map into continuous linear maps
    have hd := (hφ.1.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
    rw [fderiv_clm_apply hd (differentiableAt_const (b i))]
    simp
  simp_rw [hs,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ =>
    integrable_deriv_product hu.1 (hφ.directional (b i)) (b i))]
  simp_rw [hi]
  rw [Finset.sum_neg_distrib,← integral_finsetSum _ (fun i _ =>
    integrable_inner_test hu.2.1 (hφ.directional (b i)) (b i))]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    calc
      _ = ∑ i, inner ℝ (G x) (b i) * inner ℝ (b i) (gradient φ x) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [real_inner_comm (gradient φ x) (b i),inner_gradient_left]
      _ = _ := b.sum_inner_mul_inner (G x) (gradient φ x)

namespace HarmonicReplacement
lemma weak_laplacian_zero {u : Space d → ℝ} {G : Space d → Space d}
    (hu : H1 D u G)
    (ho : ∀ v V, H10 D v V → (∫ x in D, inner ℝ (G x) (V x)) = 0)
    {φ : Space d → ℝ} (hφ : Test D φ) :
    (∫ x in D, u x * Laplacian.laplacian φ x) = 0 := by
  rw [hu.laplacian_ibp hφ,ho _ _ hφ.h10,neg_zero]
end HarmonicReplacement
end Bernoulli

end
end

end OAI
