import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarWeakConstant

namespace OAI

/-! The two coordinate distributional derivatives determine the full planar
weak gradient. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

local instance instPlanarDistributionAxesMeasurable : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instPlanarDistributionAxesBorel : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instPlanarDistributionAxesMeasure : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

theorem planar_axis_expansion (e : PlanarPosition) :
    e = ∑ a : Fin 2, e a • planarAxis a := by
  ext j
  fin_cases j <;> simp [planarAxis]

theorem planar_zero_axis_distribution_constant (f : PlanarPosition → ℝ)
    (hf : LocallyIntegrable f)
    (hw : ∀ (ψ : PlanarPosition → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∀ a : Fin 2, (∫ x, f x*planarPartial ψ (planarAxis a) x) = 0) :
    ∃ c : ℝ, f =ᵐ[volume] fun _ => c := by
  apply planar_weak_gradient_zero_constant f hf
  intro ψ hψ hc e
  have hi (a : Fin 2) : Integrable (fun x => f x*planarPartial ψ (planarAxis a) x) := by
    simpa only [smul_eq_mul] using hf.integrable_smul_right_of_hasCompactSupport
      (planarPartial_continuous (hψ.of_le (by simp)) _)
      (hc.fderiv_apply ℝ (planarAxis a))
  have he : (fun x => f x*fderiv ℝ ψ x e) =
      (fun x => ∑ a : Fin 2, e a*(f x*planarPartial ψ (planarAxis a) x)) := by
    funext x
    have hd : fderiv ℝ ψ x e = ∑ a : Fin 2, e a*planarPartial ψ (planarAxis a) x := by
      calc
        _ = fderiv ℝ ψ x (∑ a : Fin 2, e a • planarAxis a) :=
          congrArg (fderiv ℝ ψ x) (planar_axis_expansion e)
        _ = _ := by simp only [map_sum,map_smul,smul_eq_mul,planarPartial]
    rw [hd,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he,integral_finsetSum _ (fun a _ => (hi a).const_mul _)]
  simp_rw [integral_const_mul,hw ψ hψ hc,mul_zero]
  simp

end ContinuumCoulomb

end

end OAI
