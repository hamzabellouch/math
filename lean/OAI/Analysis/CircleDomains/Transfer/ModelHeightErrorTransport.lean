import OAI.Analysis.CircleDomains.Selection.LocalHeightDifference
import OAI.Analysis.CircleDomains.Topology.ModelCompactTransport

namespace OAI

/-! The actual flattened vertical error has a small source Sobolev
witness, by conformal transport of its compact target cutoff. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem compact_height_error_transport (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {R d : ℝ} (H : ControlledHeight R d) (A : ℝ) (T : ℝ → ℝ) (hTc : Continuous T)
    (W : DeGiorgi.MemW1pWitness 2 (fun x => T (H.height (complexPlaneCoordinates x))) (ball 0 A))
    {ε δ ζ C₀ C₁ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hζ : 0 ≤ ζ)
    (he : (∫⁻ x in ball 0 A,
      ENNReal.ofReal (‖W.weakGrad x-heightLimitGradient H.error₀ H.error₁ x‖^2)) < ENNReal.ofReal ε)
    (hT : ∀ t, |T t-t| ≤ ζ)
    (hclose : ∀ x ∈ ball (0 : EuclideanPlane) A,
      |H.height (complexPlaneCoordinates x)-x 1| ≤ δ)
    (η : EuclideanPlane → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : HasCompactSupport η) (hsub : tsupport η ⊆ ball 0 A)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hηb : ∀ x, |η x| ≤ C₀) (hηd : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁) :
    let v := fun x => η x*(T (H.height (complexPlaneCoordinates x))-x 1)
    ∃ E : DeGiorgi.MemW1pWitness 2
        (planeInverseTransport (extendAtInfinity M.function) v) (physicalPlaneDomain G),
      (∫ x in physicalPlaneDomain G, E.weakGrad x 0^2+E.weakGrad x 1^2) ≤
        2*C₀^2*(2*ε+4*Real.pi*d)+4*C₁^2*(ζ+δ)^2*(volume (ball (0 : EuclideanPlane) A)).toReal := by
  obtain ⟨V, hV⟩ := H.compact_flattened_error_energy A T W hε hδ hζ he hT hclose
    η hη hs hsub hC₀ hC₁ hηb hηd
  have hc : Continuous (fun x => η x*(T (H.height (complexPlaneCoordinates x))-x 1)) :=
    hη.continuous.mul ((hTc.comp (H.height.continuous.comp complexPlaneCoordinates.continuous)).sub
      verticalLinear.continuous)
  obtain ⟨E, hE⟩ := M.compact_target_pullback_energy hG hinf hc hs.mul_right V
  refine ⟨E, hE.trans (le_trans ?_ hV)⟩
  have hi : Integrable (fun x => ‖V.weakGrad x‖^2) volume := by
    simpa only [Measure.restrict_univ] using V.weakGrad_norm_memLp.integrable_sq
  have htarget := setIntegral_le_integral hi (Eventually.of_forall (fun _ => sq_nonneg _))
    (s := physicalPlaneDomain (extendAtInfinity M.function '' G))
  simpa only [plane_norm_sq] using htarget

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
