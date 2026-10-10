import OAI.Probability.SLE.Geometry.ClosedHalfPlaneCayley
import OAI.Probability.SLE.Geometry.PuncturedDiskHomeomorph

namespace OAI

/-! Transport a boundary-fixing disk homeomorphism through the fixed Cayley chart. -/
noncomputable section
open Set Complex Metric

namespace SLEExactGauge

def halfPlaneDiskTransport
    (e : closedBall (0:ℂ) 1 ≃ₜ closedBall (0:ℂ) 1)
    (h1 : e ⟨1,by norm_num⟩=⟨1,by norm_num⟩) :
    {z : ℂ // 0 ≤ z.im} ≃ₜ {z : ℂ // 0 ≤ z.im} :=
  (closedHalfPlaneCayley.trans (puncturedDiskHomeomorph e h1)).trans
    closedHalfPlaneCayley.symm

lemma halfPlaneDiskTransport_apply
    (e : closedBall (0:ℂ) 1 ≃ₜ closedBall (0:ℂ) 1)
    (h1 : e ⟨1,by norm_num⟩=⟨1,by norm_num⟩)
    (z : {z : ℂ // 0 ≤ z.im}) :
    (halfPlaneDiskTransport e h1 z : ℂ)=
      halfPlaneCayleyInv (e ⟨halfPlaneCayley z,by
        simpa only [mem_closedBall,dist_zero_right] using halfPlaneCayley_norm_le z.property⟩) := rfl

lemma halfPlaneDiskTransport_boundary
    (e : closedBall (0:ℂ) 1 ≃ₜ closedBall (0:ℂ) 1)
    (h1 : e ⟨1,by norm_num⟩=⟨1,by norm_num⟩)
    (hfix : ∀ z : closedBall (0:ℂ) 1, ‖(z:ℂ)‖=1 → (e z:ℂ)=z)
    (z : {z : ℂ // 0 ≤ z.im}) (hz : z.val.im=0) :
    (halfPlaneDiskTransport e h1 z : ℂ)=z := by
  rw [halfPlaneDiskTransport_apply]
  have hreal : (z:ℂ)=(z.val.re:ℂ) := Complex.ext rfl hz
  have hn : ‖halfPlaneCayley (z:ℂ)‖=1 := by
    rw [hreal]
    exact halfPlaneCayley_real_norm _
  rw [hfix _ hn]
  exact halfPlaneCayleyInv_cayley z.property

end SLEExactGauge

end

end OAI
