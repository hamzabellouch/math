import OAI.Probability.SLE.Geometry.HalfPlaneCayleyCompactification
import OAI.Probability.SLE.DiskHalfPlane

namespace OAI

/-! The inverse Cayley chart on the compact disk with the point at
infinity removed. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace SLEExactGauge

def halfPlaneCayleyInv (w : ℂ) : ℂ := I*(1+w)/(1-w)

lemma halfPlaneCayleyInv_eq (w : ℂ) : halfPlaneCayleyInv w=diskToHalfPlane I w := by
  unfold halfPlaneCayleyInv diskToHalfPlane
  simp only [Complex.star_def,Complex.conj_I]
  congr 1
  ring

lemma halfPlaneCayleyInv_im (w : ℂ) :
    (halfPlaneCayleyInv w).im=(1-Complex.normSq w)/Complex.normSq (1-w) := by
  rw [halfPlaneCayleyInv_eq,diskToHalfPlane_im]
  simp

lemma halfPlaneCayleyInv_continuousOn :
    ContinuousOn halfPlaneCayleyInv {w : ℂ | w ≠ 1} := by
  apply (continuousOn_const.mul (continuousOn_const.add continuousOn_id)).div
    (continuousOn_const.sub continuousOn_id)
  intro w hw
  exact sub_ne_zero.mpr hw.symm

lemma halfPlaneCayleyInv_closed {w : ℂ} (hw : ‖w‖ ≤ 1) :
    0 ≤ (halfPlaneCayleyInv w).im := by
  rw [halfPlaneCayleyInv_im]
  have hs : Complex.normSq w ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  exact div_nonneg (sub_nonneg.mpr hs) (Complex.normSq_nonneg _)

lemma halfPlaneCayleyInv_open {w : ℂ} (hw : ‖w‖ < 1) :
    0 < (halfPlaneCayleyInv w).im := by
  rw [halfPlaneCayleyInv_im]
  have hs : Complex.normSq w < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  have hn : 1-w ≠ 0 := by
    intro he
    have hwe : w=1 := (sub_eq_zero.mp he).symm
    simp only [hwe,norm_one,lt_self_iff_false] at hw
  exact div_pos (sub_pos.mpr hs) (Complex.normSq_pos.mpr hn)

lemma halfPlaneCayleyInv_cayley {z : ℂ} (hz : 0 ≤ z.im) :
    halfPlaneCayleyInv (halfPlaneCayley z)=z := by
  have hd := halfPlaneCayley_den_ne hz
  have hn : 1-halfPlaneCayley z ≠ 0 := sub_ne_zero.mpr (halfPlaneCayley_ne_one hz).symm
  unfold halfPlaneCayleyInv
  apply (div_eq_iff hn).mpr
  unfold halfPlaneCayley
  field_simp
  ring

lemma halfPlaneCayley_cayleyInv {w : ℂ} (hw : w ≠ 1) :
    halfPlaneCayley (halfPlaneCayleyInv w)=w := by
  have hd : 1-w ≠ 0 := sub_ne_zero.mpr hw.symm
  have hn : halfPlaneCayleyInv w+I ≠ 0 := by
    intro he
    have hh : I*(1+w)+I*(1-w)=0 := by
      have hx := congrArg (fun z : ℂ => z*(1-w)) he
      simpa only [halfPlaneCayleyInv,add_mul,div_mul_cancel₀ _ hd,zero_mul] using hx
    have hi : (2:ℂ)*I=0 := by linear_combination hh
    norm_num at hi
  unfold halfPlaneCayley
  apply (div_eq_iff hn).mpr
  unfold halfPlaneCayleyInv
  field_simp
  ring

end SLEExactGauge

end

end OAI
