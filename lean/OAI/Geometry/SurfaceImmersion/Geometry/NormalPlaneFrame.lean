import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapFrameHomotopy

namespace OAI

/-! The reduced crosscap frame and its positive rescalings in the normal plane. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def normalPlaneFrame (w : Base) : Base →L[ℝ] (Base × ℝ) :=
  (ContinuousLinearMap.proj 0).smulRight ((0,1) : Base × ℝ) +
    (ContinuousLinearMap.proj 1).smulRight (w,0)

lemma normalPlaneFrame_apply (w v : Base) :
    normalPlaneFrame w v = (v 1 • w,v 0) := by
  apply Prod.ext <;> simp [normalPlaneFrame]

lemma normalPlaneFrame_smooth : ContDiff ℝ ∞ normalPlaneFrame := by
  exact contDiff_const.add (contDiff_const.smulRight (contDiff_id.prodMk contDiff_const))

lemma normalPlaneFrame_injective_iff (w : Base) :
    Function.Injective (normalPlaneFrame w) ↔ w ≠ 0 := by
  constructor
  · intro hi hw
    have he : normalPlaneFrame w (![0,1] : Base) = normalPlaneFrame w 0 := by
      simp [hw,normalPlaneFrame_apply]
    have hh := congrFun (hi he) 1
    norm_num at hh
  · intro hw u v he
    have h0 : u 0 = v 0 := by simpa only [normalPlaneFrame_apply] using congrArg Prod.snd he
    have hn : (u 1-v 1) • w = 0 := by
      rw [sub_smul,sub_eq_zero]
      simpa only [normalPlaneFrame_apply] using congrArg Prod.fst he
    have h1 : u 1 = v 1 := sub_eq_zero.mp ((smul_eq_zero.mp hn).resolve_right hw)
    ext i
    fin_cases i
    · exact h0
    · exact h1

lemma crosscapFrameHomotopy_zero_frame (x : Base) :
    crosscapFrameHomotopy 0 x = normalPlaneFrame ![x 0,2*x 1] := by
  ext v : 1
  rw [crosscapFrameHomotopy_zero,normalPlaneFrame_apply]

def positiveNormalFrame (k : ℝ) (x : Base) : Base →L[ℝ] (Base × ℝ) :=
  normalPlaneFrame ![x 0,k*x 1]

lemma positiveNormalFrame_injective {k : ℝ} (hk : 0 < k) (x : Base) :
    Function.Injective (positiveNormalFrame k x) ↔ x ≠ 0 := by
  rw [positiveNormalFrame,normalPlaneFrame_injective_iff]
  constructor
  · intro hn hx
    apply hn
    subst x
    ext i
    fin_cases i <;> simp
  · intro hx hn
    apply hx
    have h0 : x 0 = 0 := congrFun hn 0
    have h1 : k*x 1 = 0 := congrFun hn 1
    have hx1 : x 1 = 0 := (mul_eq_zero.mp h1).resolve_left hk.ne'
    ext i
    fin_cases i
    · exact h0
    · exact hx1

lemma positiveNormalFrame_homotopy (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (x : Base) :
    Function.Injective (positiveNormalFrame (2-s) x) ↔ x ≠ 0 :=
  positiveNormalFrame_injective (by linarith [hs.2]) x

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
