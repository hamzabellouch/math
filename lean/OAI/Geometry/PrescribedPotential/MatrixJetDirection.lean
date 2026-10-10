import Mathlib
import OAI.Geometry.PrescribedPotential.ChernLuLocalInequality

namespace OAI

/-! Matrix Jet Direction. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma wderiv_direction_smul (a : ℂ) (r : ℝ) (v : V n) (f : V n → ℂ) (z : V n) :
    wderiv a (r • v) f z = (r:ℂ)*wderiv a v f z := by
  simp only [wderiv,smul_comm Complex.I r v,map_smul,Complex.real_smul]
  ring

lemma wderiv_second_direction_smul {f : V n → ℂ} {z : V n}
    (hf : ContDiffAt ℝ ∞ f z) (a b : ℂ) (r : ℝ) (v : V n) :
    wderiv a (r • v) (wderiv b (r • v) f) z =
      (r:ℂ)^2*wderiv a v (wderiv b v f) z := by
  have he : wderiv b (r • v) f = fun y => (r:ℂ)*wderiv b v f y :=
    funext (fun y => wderiv_direction_smul b r v f y)
  rw [he,wderiv_direction_smul,
    wderiv_const_mul ((wderiv_smooth hf b v).differentiableAt (by simp))]
  ring

lemma mderiv_direction_smul (a : ℂ) (r : ℝ) (v : V n)
    (M : V n → Matrix (Fin n) (Fin n) ℂ) (z : V n) :
    mderiv a (r • v) M z = (r:ℂ) • mderiv a v M z := by
  ext i j
  exact wderiv_direction_smul a r v (fun y => M y i j) z

lemma mderiv_second_direction_smul {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) (a b : ℂ) (r : ℝ) (v : V n) :
    mderiv a (r • v) (mderiv b (r • v) M) z =
      (r:ℂ)^2 • mderiv a v (mderiv b v M) z := by
  ext i j
  exact wderiv_second_direction_smul (entry_smooth hM i j) a b r v

lemma curvatureDiagonal_smul {G : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hG : ContDiffAt ℝ ∞ G z) (r : ℝ) (v : V n) :
    curvatureDiagonal G z (r • v) = (r:ℂ)^2 • curvatureDiagonal G z v := by
  unfold curvatureDiagonal
  rw [mderiv_second_direction_smul hG,mderiv_direction_smul]
  simp only [Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_ofReal,
    smul_mul_assoc,mul_smul_comm,smul_smul,smul_sub,pow_two]

lemma wderiv_joint_smooth {f : V n → ℂ} {z v : V n}
    (hf : ContDiffAt ℝ ∞ f z) (a : ℂ) :
    ContDiffAt ℝ ∞ (fun q : V n × V n => wderiv a q.2 f q.1) (z,v) := by
  have hd := (hf.fderiv_right (m := ∞) (by simp)).comp (z,v) contDiffAt_fst
  have hi : ContDiffAt ℝ ∞ (fun q : V n × V n => Complex.I • q.2) (z,v) :=
    contDiffAt_snd.const_smul Complex.I
  exact ((hd.clm_apply contDiffAt_snd).add
    (contDiffAt_const.mul (hd.clm_apply hi))).div_const 2

lemma wderiv_second_joint_continuous {U : Set (V n)} (hU : IsOpen U)
    {f : V n → ℂ} (hf : ContDiffOn ℝ ∞ f U) (a b : ℂ) :
    ContinuousOn (fun q : V n × V n => wderiv a q.2 (wderiv b q.2 f) q.1) (U ×ˢ univ) := by
  intro q hq
  have hs := hf.contDiffAt (hU.mem_nhds hq.1)
  have hd := ((hs.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).comp q contDiffAt_fst
  have hi : ContDiffAt ℝ ∞ (fun q : V n × V n => Complex.I • q.2) q :=
    contDiffAt_snd.const_smul Complex.I
  have he : (fun q : V n × V n => wderiv a q.2 (wderiv b q.2 f) q.1) =ᶠ[𝓝 q]
      (fun q => ((fderiv ℝ (fderiv ℝ f) q.1 q.2 q.2 +
        b*fderiv ℝ (fderiv ℝ f) q.1 q.2 (Complex.I • q.2))/2 +
        a*((fderiv ℝ (fderiv ℝ f) q.1 (Complex.I • q.2) q.2 +
          b*fderiv ℝ (fderiv ℝ f) q.1 (Complex.I • q.2) (Complex.I • q.2))/2))/2) := by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (hU.mem_nhds hq.1)] with p hp
    change (fderiv ℝ (wderiv b p.2 f) p.1 p.2 + a*fderiv ℝ (wderiv b p.2 f) p.1 (Complex.I • p.2))/2 = _
    rw [fderiv_wderiv (hf.contDiffAt (hU.mem_nhds hp)),
      fderiv_wderiv (hf.contDiffAt (hU.mem_nhds hp))]
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.congr _ he.symm
  exact (((hd.clm_apply contDiffAt_snd).clm_apply contDiffAt_snd).add
    (contDiffAt_const.mul ((hd.clm_apply contDiffAt_snd).clm_apply hi))).div_const 2 |>.add
    (contDiffAt_const.mul ((((hd.clm_apply hi).clm_apply contDiffAt_snd).add
      (contDiffAt_const.mul ((hd.clm_apply hi).clm_apply hi))).div_const 2)) |>.div_const 2 |>.continuousAt

lemma curvatureDiagonal_joint_continuous {U : Set (V n)} (hU : IsOpen U)
    {G : V n → Matrix (Fin n) (Fin n) ℂ} (hG : ContDiffOn ℝ ∞ G U)
    (hn : ∀ z ∈ U, (G z).det ≠ 0) :
    ContinuousOn (fun q : V n × V n => curvatureDiagonal G q.1 q.2) (U ×ˢ univ) := by
  have hd : ContinuousOn (fun q : V n × V n => mderiv (-Complex.I) q.2 G q.1) (U ×ˢ univ) := by
    intro q hq
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact (wderiv_joint_smooth (entry_smooth (hG.contDiffAt (hU.mem_nhds hq.1)) i j) _).continuousAt
  have hdd : ContinuousOn (fun q : V n × V n => mderiv Complex.I q.2 (mderiv (-Complex.I) q.2 G) q.1) (U ×ˢ univ) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact wderiv_second_joint_continuous hU (contDiffOn_pi.mp (contDiffOn_pi.mp hG i) j) _ _
  have hinv : ContinuousOn (fun q : V n × V n => (G q.1)⁻¹) (U ×ˢ univ) :=
    (MatrixSmoothGeneral.inverse hG hn).continuousOn.comp continuous_fst.continuousOn (fun _ h => h.1)
  have hdstar : ContinuousOn (fun q : V n × V n => (mderiv (-Complex.I) q.2 G q.1)ᴴ) (U ×ˢ univ) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (continuousOn_pi.mp (continuousOn_pi.mp hd j) i).star
  exact hdd.sub ((hdstar.mul hinv).mul hd)
end KaehlerCalculus

end
end

end OAI
