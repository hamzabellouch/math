import OAI.Geometry.Kahler.HartogsNormalTables

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

lemma complexHessian_lam_add_eventually {f g : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (hg : ContDiffAt ℝ 2 g p) (lam : ℝ) (c d : Fin 3) :
    (fun q => complexHessian (fun r => lam * f r + g r) q c d) =ᶠ[𝓝 p]
      (fun q => (lam : ℂ) * complexHessian f q c d + complexHessian g q c d) := by
  filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with q hq hq'
  rw [complexHessian_add (contDiffAt_const.mul hq) hq', complexHessian_const_mul hq]

lemma dz_complexHessian_lam_add {f g : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 3 f p) (hg : ContDiffAt ℝ 3 g p) (lam : ℝ) (a c d : Fin 3) :
    dz (fun q => complexHessian (fun r => lam * f r + g r) q c d) p a =
      (lam : ℂ) * dz (fun q => complexHessian f q c d) p a +
        dz (fun q => complexHessian g q c d) p a := by
  have hfd := (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 2) (by norm_num) d) (m := 1) (by norm_num) c).differentiableAt (by norm_num)
  have hgd := (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hg) (m := 2) (by norm_num) d) (m := 1) (by norm_num) c).differentiableAt (by norm_num)
  rw [dz_congr (complexHessian_lam_add_eventually (hf.of_le (by norm_num)) (hg.of_le (by norm_num)) lam c d)]
  exact (dz_add ((differentiableAt_const _).mul hfd) hgd a).trans (by erw [dz_const_mul hfd]; rfl)

lemma dbar_dz_complexHessian_lam_add {f g : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 4 f p) (hg : ContDiffAt ℝ 4 g p) (lam : ℝ) (a b c d : Fin 3) :
    dbar (fun q => dz (fun r => complexHessian (fun t => lam * f t + g t) r c d) q a) p b =
      (lam : ℂ) * dbar (fun q => dz (fun r => complexHessian f r c d) q a) p b +
        dbar (fun q => dz (fun r => complexHessian g r c d) q a) p b := by
  have he : (fun q => dz (fun r => complexHessian (fun t => lam * f t + g t) r c d) q a) =ᶠ[𝓝 p]
      (fun q => (lam : ℂ) * dz (fun r => complexHessian f r c d) q a + dz (fun r => complexHessian g r c d) q a) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with q hq hq'
    exact dz_complexHessian_lam_add (hq.of_le (by norm_num)) (hq'.of_le (by norm_num)) lam a c d
  have hfd := (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 3) (by norm_num) d) (m := 2) (by norm_num) c) (m := 1) (by norm_num) a).differentiableAt (by norm_num)
  have hgd := (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hg) (m := 3) (by norm_num) d) (m := 2) (by norm_num) c) (m := 1) (by norm_num) a).differentiableAt (by norm_num)
  rw [dbar_congr he]
  exact (dbar_add ((differentiableAt_const _).mul hfd) hgd b).trans (by erw [dbar_const_mul hfd]; rfl)

def normalPotential (f : Base → ℝ) (lam : ℝ) (w : ℂ) (q : Ambient) : ℝ :=
  lam * psi q.1 + logarithmicBarrier (normalLogWeight f w q)

lemma normalPotential_contDiffAt {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) :
    ContDiffAt ℝ ∞ (normalPotential f lam w) (0,w) :=
  (contDiffAt_const.mul ((psi_contDiffAt zero_mem_ball).comp (f := fun q : Ambient => q.1) (0,w) contDiffAt_fst)).add
    ((logarithmicBarrier_contDiffAt hn).comp (0,w) (normalLogWeight_contDiffAt (q := (0,w)) hf w))

lemma normalPotential_hessian {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) (i j : Fin 3) :
    complexHessian (normalPotential f lam w) (0,w) i j =
      (lam : ℂ) * horizontalIdentity i j +
      (barrierX (normalLogWeight f w (0,w)) : ℂ) * liftedHessian f (0,w) i j +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * verticalDelta i * verticalDelta j := by
  have hψ : ContDiffAt ℝ 2 (fun q : Ambient => psi q.1) (0,w) :=
    ((psi_contDiffAt zero_mem_ball).of_le (WithTop.coe_le_coe.mpr le_top)).comp (f := fun q : Ambient => q.1) (0,w) contDiffAt_fst
  have hB : ContDiffAt ℝ 2 (logarithmicBarrier ∘ normalLogWeight f w) (0,w) :=
    ((logarithmicBarrier_contDiffAt hn).comp (0,w) (normalLogWeight_contDiffAt (q := (0,w)) hf w)).of_le (WithTop.coe_le_coe.mpr le_top)
  change complexHessian (fun q : Ambient => lam * psi q.1 + (logarithmicBarrier ∘ normalLogWeight f w) q) (0,w) i j = _
  erw [complexHessian_add (contDiffAt_const.mul hψ) hB, complexHessian_const_mul hψ,
    psi_hessian_center, normalBarrier_hessian hf w hn]
  ring

lemma normalPotential_third {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) (a c d : Fin 3) :
    dz (fun q => complexHessian (normalPotential f lam w) q c d) (0,w) a =
      (barrierX (normalLogWeight f w (0,w)) : ℂ) * liftedThird f (0,w) a c d +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * verticalDelta a * liftedHessian f (0,w) c d +
      (barrierQ (normalLogWeight f w (0,w)) : ℂ) * verticalDelta c * liftedHessian f (0,w) a d +
      (barrierThird (normalLogWeight f w (0,w)) : ℂ) * verticalDelta a * verticalDelta c * verticalDelta d := by
  have hψ : ContDiffAt ℝ 3 (fun q : Ambient => psi q.1) (0,w) :=
    ((psi_contDiffAt zero_mem_ball).of_le (WithTop.coe_le_coe.mpr le_top)).comp (f := fun q : Ambient => q.1) (0,w) contDiffAt_fst
  have hB : ContDiffAt ℝ 3 (logarithmicBarrier ∘ normalLogWeight f w) (0,w) :=
    ((logarithmicBarrier_contDiffAt hn).comp (0,w) (normalLogWeight_contDiffAt (q := (0,w)) hf w)).of_le (WithTop.coe_le_coe.mpr le_top)
  change dz (fun q => complexHessian (fun r : Ambient => lam * psi r.1 + (logarithmicBarrier ∘ normalLogWeight f w) r) q c d) (0,w) a = _
  erw [dz_complexHessian_lam_add hψ hB, psi_third_center, mul_zero, zero_add]
  exact normalBarrier_third hf w hn a c d

lemma normalPotential_fourth {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) (a b c d : Fin 3) :
    dbar (fun q => dz (fun r => complexHessian (normalPotential f lam w) r c d) q a) (0,w) b =
      (lam : ℂ) * (horizontalIdentity a b * horizontalIdentity c d + horizontalIdentity a d * horizontalIdentity c b) +
      dbar (fun q => dz (fun r => complexHessian (logarithmicBarrier ∘ normalLogWeight f w) r c d) q a) (0,w) b := by
  have hψ : ContDiffAt ℝ 4 (fun q : Ambient => psi q.1) (0,w) :=
    ((psi_contDiffAt zero_mem_ball).of_le (WithTop.coe_le_coe.mpr le_top)).comp (f := fun q : Ambient => q.1) (0,w) contDiffAt_fst
  have hB : ContDiffAt ℝ 4 (logarithmicBarrier ∘ normalLogWeight f w) (0,w) :=
    ((logarithmicBarrier_contDiffAt hn).comp (0,w) (normalLogWeight_contDiffAt (q := (0,w)) hf w)).of_le (WithTop.coe_le_coe.mpr le_top)
  change dbar (fun q => dz (fun r => complexHessian (fun t : Ambient => lam * psi t.1 + (logarithmicBarrier ∘ normalLogWeight f w) t) r c d) q a) (0,w) b = _
  erw [dbar_dz_complexHessian_lam_add hψ hB, psi_fourth_center]
  ring

end PinchedHartogs

end

end OAI
