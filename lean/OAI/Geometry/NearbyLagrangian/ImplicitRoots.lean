import Mathlib
import OAI.Geometry.NearbyLagrangian.NearIdentity

namespace OAI

/-! Smooth parameter-dependent roots and near-identity inverses. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport
open Filter ContinuousLinearMap
open scoped ContDiff Topology NNReal
variable {P W Z : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

theorem contDiff_unique_root {F : P × W → Z} (hF : ContDiff ℝ ∞ F)
    {s : P → W} (hs : ∀ p, F (p,s p) = 0)
    (hu : ∀ p w, F (p,w) = 0 → w = s p)
    (hi : ∀ p, ((fderiv ℝ F (p,s p)).comp (inr ℝ P W)).IsInvertible) :
    ContDiff ℝ ∞ s := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have h := hF.contDiffAt (x:=(p,s p))
  let σ := h.implicitFunction (by simp) (hi p)
  have hσ : ContDiffAt ℝ ∞ σ p := h.contDiffAt_implicitFunction (by simp) (hi p)
  apply hσ.congr_of_eventuallyEq
  filter_upwards [h.eventually_apply_implicitFunction (by simp) (hi p)] with q hq
  exact (hu q (σ q) (hq.trans (hs p))).symm

omit [CompleteSpace P] [CompleteSpace W] [CompleteSpace Z] in
lemma fderiv_slice_right {F : P × W → Z} {p : P} {w : W}
    (hF : DifferentiableAt ℝ F (p,w)) :
    fderiv ℝ (fun v => F (p,v)) w = (fderiv ℝ F (p,w)).comp (inr ℝ P W) := by
  have hpair : HasFDerivAt (fun v : W => (p,v)) (inr ℝ P W) w := by
    exact (hasFDerivAt_const p w).prodMk (hasFDerivAt_id w)
  exact (hF.hasFDerivAt.comp w hpair).fderiv

theorem contDiff_nearIdentity_inverse {F : P × W → W} (hF : ContDiff ℝ ∞ F)
    (c : ℝ≥0) (hc : c < 1)
    (hb : ∀ p w, ‖fderiv ℝ (fun v => F (p,v)) w - ContinuousLinearMap.id ℝ W‖ ≤ c) :
    ContDiff ℝ ∞ (fun z : P × W =>
      (nearIdentityHomeomorph (fun v => F (z.1,v))
        (hF.comp (contDiff_const.prodMk contDiff_id)) c hc (hb z.1)).symm z.2) := by
  let h (p : P) := nearIdentityHomeomorph (fun v => F (p,v))
    (hF.comp (contDiff_const.prodMk contDiff_id)) c hc (hb p)
  let G : (P × W) × W → W := fun z => F (z.1.1,z.2) - z.1.2
  have hG : ContDiff ℝ ∞ G :=
    (hF.comp (contDiff_fst.fst.prodMk contDiff_snd)).sub contDiff_fst.snd
  apply contDiff_unique_root hG (s:=fun z => (h z.1).symm z.2)
  · intro z
    exact sub_eq_zero.mpr ((h z.1).apply_symm_apply z.2)
  · intro z w hw
    exact (h z.1).injective ((sub_eq_zero.mp hw).trans
      ((h z.1).apply_symm_apply z.2).symm)
  · intro z
    rw [← fderiv_slice_right (hG.differentiable (by simp) _)]
    change (fderiv ℝ (fun w => F (z.1,w) - z.2) _).IsInvertible
    rw [fderiv_sub_const]
    exact ⟨nearIdentityDerivative _ c hc (hb z.1) _,
      nearIdentityDerivative_coe _ c hc (hb z.1) _⟩

theorem exists_contDiff_nearIdentity_inverse {F : P × W → W} (hF : ContDiff ℝ ∞ F)
    (c : ℝ≥0) (hc : c < 1)
    (hb : ∀ p w, ‖fderiv ℝ (fun v => F (p,v)) w - ContinuousLinearMap.id ℝ W‖ ≤ c) :
    ∃ G : P × W → W, ContDiff ℝ ∞ G ∧
      (∀ p w, F (p,G (p,w)) = w) ∧
      ∀ p w v, F (p,v) = w → v = G (p,w) := by
  let H (p:P) := nearIdentityHomeomorph (fun v => F (p,v))
    (hF.comp (contDiff_const.prodMk contDiff_id)) c hc (hb p)
  refine ⟨fun z => (H z.1).symm z.2, contDiff_nearIdentity_inverse hF c hc hb, ?_, ?_⟩
  · intro p w
    exact (H p).apply_symm_apply w
  · intro p w v hv
    exact (H p).injective (hv.trans ((H p).apply_symm_apply w).symm)

end NearbyLagrangian.Transport

end

end OAI
