import OAI.Geometry.SurfaceImmersion.Whitney.StandardCrosscapDerivative

namespace OAI

/-! A concrete formal homotopy reduces the derivative of one standard
crosscap to its planar normal-defect frame. The homotopy is injective
away from the original singular point at every parameter. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def crosscapFrameHomotopy (s : ℝ) (x : Base) : Base →L[ℝ] (Base × ℝ) :=
  (ContinuousLinearMap.proj 0).smulRight ((![s*x 1,0],1) : Base × ℝ) +
    (ContinuousLinearMap.proj 1).smulRight ((![x 0,2*x 1],0) : Base × ℝ)

lemma crosscapFrameHomotopy_smooth :
    ContDiff ℝ ∞ (fun z : ℝ × Base => crosscapFrameHomotopy z.1 z.2) := by
  have hA : ContDiff ℝ ∞ (fun z : ℝ × Base => (![z.1*z.2 1,0] : Base)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun z : ℝ × Base => z.1*z.2 1)
      exact contDiff_fst.mul ((contDiff_apply ℝ ℝ 1).comp contDiff_snd)
    · exact contDiff_const
  have hB : ContDiff ℝ ∞ (fun z : ℝ × Base => (![z.2 0,2*z.2 1] : Base)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun z : ℝ × Base => z.2 0)
      exact (contDiff_apply ℝ ℝ 0).comp contDiff_snd
    · change ContDiff ℝ ∞ (fun z : ℝ × Base => 2*z.2 1)
      exact contDiff_const.mul ((contDiff_apply ℝ ℝ 1).comp contDiff_snd)
  exact (contDiff_const.smulRight (hA.prodMk contDiff_const)).add
    (contDiff_const.smulRight (hB.prodMk contDiff_const))

lemma crosscapFrameHomotopy_one (x : Base) :
    crosscapFrameHomotopy 1 x = fderiv ℝ standardCrosscap x := by
  rw [(standardCrosscap_hasFDerivAt x).fderiv]
  ext v : 1
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [crosscapFrameHomotopy,standardCrosscapDerivative] <;> ring
  · simp [crosscapFrameHomotopy,standardCrosscapDerivative]

lemma crosscapFrameHomotopy_zero (x v : Base) :
    crosscapFrameHomotopy 0 x v = (v 1 • (![x 0,2*x 1] : Base),v 0) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [crosscapFrameHomotopy]
  · simp [crosscapFrameHomotopy]

lemma crosscapFrameHomotopy_injective_iff (s : ℝ) (x : Base) :
    Function.Injective (crosscapFrameHomotopy s x) ↔ x ≠ 0 := by
  constructor
  · intro hi hx
    have he : crosscapFrameHomotopy s x (![0,1] : Base) =
        crosscapFrameHomotopy s x 0 := by
      subst x
      simp [crosscapFrameHomotopy]
    have hh := congrFun (hi he) 1
    norm_num at hh
  · intro hx u v he
    have h0 : u 0 = v 0 := by
      have h := congrArg Prod.snd he
      simpa [crosscapFrameHomotopy] using h
    have h1 : s*x 1*u 0+x 0*u 1 = s*x 1*v 0+x 0*v 1 := by
      have h := congrFun (congrArg Prod.fst he) 0
      simpa [crosscapFrameHomotopy,mul_comm,mul_left_comm,mul_assoc] using h
    have h2 : (2*x 1)*u 1 = (2*x 1)*v 1 := by
      have h := congrFun (congrArg Prod.fst he) 1
      simpa [crosscapFrameHomotopy,mul_comm,mul_left_comm,mul_assoc] using h
    have huv : u 1 = v 1 := by
      by_cases hx0 : x 0 = 0
      · have hx1 : x 1 ≠ 0 := by
          intro h
          apply hx
          ext i
          fin_cases i
          · exact hx0
          · exact h
        exact mul_left_cancel₀ (mul_ne_zero (by norm_num) hx1) h2
      · rw [h0] at h1
        exact mul_left_cancel₀ hx0 (add_left_cancel h1)
    ext i
    fin_cases i
    · exact h0
    · exact huv

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
