import OAI.Analysis.CircleDomains.Topology.ExteriorJordanCore

namespace OAI

/-! The image of an exterior source circle is the actual smooth regular
parametrization of its target Jordan boundary. -/
open Set Filter Function Metric Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exterior_image_circle_regular {F : ℂ → ℂ} {R a : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) (hi : InjOn F {z | R < ‖z‖})
    (ha : R < a) (H : ℂ ≃ₜ ℂ)
    (hH : frontier (jordanInterior H) = range (fun z : Circle => F ((a : ℂ)*(z : ℂ)))) :
    RegularJordanParametrization H (fun t => F (unitCircleParam 0 a t)) := by
  have hap : 0 < a := hR.trans ha
  have hO : IsOpen {z : ℂ | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hs := unitCircleParam_regular a hap
  have hin (t : ℝ) : unitCircleParam 0 a t ∈ {z : ℂ | R < ‖z‖} := by
    simpa only [mem_ofPred_eq, unitCircleParam, norm_circleMap_zero, abs_of_pos hap] using ha
  have hγ : ContDiff ℝ (⊤ : ℕ∞) (fun t => F (unitCircleParam 0 a t)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    exact ((hF.analyticAt (hO.mem_nhds (hin t))).contDiffAt.restrict_scalars ℝ).comp t
      hs.smooth.contDiffAt
  refine ⟨hγ, fun t => congrArg F (hs.periodic t), ?_, ?_, ?_⟩
  · intro s hs' t ht' he
    exact hs.injective hs' ht' (hi (hin s) (hin t) he)
  · intro t
    have hf := ((hF _ (hin t)).differentiableAt (hO.mem_nhds (hin t))).hasDerivAt
    have hd := (hf.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
      ((hs.smooth.differentiable (by simp) t).hasDerivAt)
    have he : deriv (fun t => F (unitCircleParam 0 a t)) t =
        deriv F (unitCircleParam 0 a t) * deriv (unitCircleParam 0 a) t := by
      change deriv (F ∘ unitCircleParam 0 a) t = _
      rw [hd.deriv]
      change deriv (unitCircleParam 0 a) t * deriv F (unitCircleParam 0 a t) = _
      exact mul_comm _ _
    rw [he]
    exact mul_ne_zero (holomorphicInjOn_deriv_ne_zero hO hF hi (hin t)) (hs.regular t)
  · have hc : range (fun z : Circle => (a : ℂ)*(z : ℂ)) =
        frontier (jordanInterior (roundDiskChart a hap)) := by
      symm
      exact frontier_jordanInterior_eq_circle_range (roundDiskChart a hap)
        (fun z : Circle => (a : ℂ)*(z : ℂ)) (by intro z; rfl)
    calc
      (fun t => F (unitCircleParam 0 a t)) '' Icc 0 1 =
          F '' (unitCircleParam 0 a '' Icc 0 1) := (image_image _ _ _).symm
      _ = F '' frontier (jordanInterior (roundDiskChart a hap)) := by rw [hs.boundary]
      _ = F '' range (fun z : Circle => (a : ℂ)*(z : ℂ)) := by rw [hc]
      _ = range (fun z : Circle => F ((a : ℂ)*(z : ℂ))) := (range_comp' _ _).symm
      _ = frontier (jordanInterior H) := hH.symm

end CircleDomainRigidity

end

end OAI
