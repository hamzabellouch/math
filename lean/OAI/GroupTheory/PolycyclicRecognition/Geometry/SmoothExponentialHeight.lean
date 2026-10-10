import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBasisSection
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LocalParameterSmoothness

namespace OAI

/-! # Smoothness of a height specified on exponential curves -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {E G W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem contMDiff_height_of_exponential_linear
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (π : G →* Multiplicative W) (d : E →ₗ[ℝ] W)
    (he : ∀ x, (π (Exp x)).toAdd = d x) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, W)) ∞ (fun g => (π g).toAdd) := by
  let b := Module.finBasis ℝ E
  let e := b.equivFun.symm.toContinuousLinearEquiv
  have hd : HasMFDerivAt (𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ)) (𝓘(ℝ, E))
      (exponentialProduct Exp b) 0 e.toContinuousLinearMap := by
    apply (hExp.hasMFDerivAt_exponentialProduct_zero b).congr_mfderiv
    ext x
    simp only [tangentCombination_apply]
    exact (b.equivFun_symm_apply x).symm
  have hcomp : (fun g => (π g).toAdd) ∘ exponentialProduct Exp b =
      d ∘ b.equivFun.symm := by
    funext x
    change (π (exponentialProduct Exp b x)).toAdd = d (b.equivFun.symm x)
    rw [exponentialProduct_linear_quotient d π he, b.equivFun_symm_apply, map_sum]
    simp only [map_smul]
  have hbase : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, W)) ∞
      (fun g => (π g).toAdd) 1 := by
    have hh := contMDiffAt_of_local_parameterization
      (hExp.contMDiff_exponentialProduct b).contMDiffAt hd
      (show ContDiffAt ℝ ∞ ((fun g => (π g).toAdd) ∘ exponentialProduct Exp b) 0 from by
        rw [hcomp]
        exact (d.toContinuousLinearMap.contDiff.comp
          e.toContinuousLinearMap.contDiff).contDiffAt)
    simpa only [hExp.exponentialProduct_zero] using hh
  intro g
  have hl : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun x : G => g⁻¹ * x) g :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := g⁻¹)).contMDiffAt
  have hh : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, W)) ∞
      (fun x => (π g).toAdd + (π (g⁻¹ * x)).toAdd) g :=
    contMDiffAt_const.add (hbase.comp_of_eq hl (inv_mul_cancel g))
  have heq : (fun x => (π g).toAdd + (π (g⁻¹ * x)).toAdd) =
      (fun x => (π x).toAdd) := by
    funext x
    rw [← toAdd_mul, ← map_mul, mul_inv_cancel_left]
  change ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, W)) ∞
    (fun x => (π g).toAdd + (π (g⁻¹ * x)).toAdd) g at hh
  rwa [heq] at hh

end PolycyclicRecognition

end

end OAI
