import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarLocalExistence
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellNorm
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace OAI

/-! Reflection of scalar Cauchy states and construction from terminal data. -/

open Set
namespace DefocusingNLS

noncomputable def spectralScalarReflect (a b : ℝ) (q : ℝ → ℂ × ℂ) (r : ℝ) : ℂ × ℂ :=
  ((q (a+b-r)).1,-(q (a+b-r)).2)

theorem spectralScalarReflect_hasDerivAt (a b r : ℝ) (q : ℝ → ℂ × ℂ) (V : ℂ)
    (hq : HasDerivAt q (spectralScalarField V (q (a+b-r))) (a+b-r)) :
    HasDerivAt (spectralScalarReflect a b q)
      (spectralScalarField V (spectralScalarReflect a b q r)) r := by
  have hd := hq.scomp r ((hasDerivAt_id r).const_sub (a+b))
  have h1 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hd
  have h2 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hd
  have hh := h1.prodMk h2.neg
  apply hh.congr_deriv
  apply Prod.ext
  · change (((-1 : ℝ) • spectralScalarField V (q (a+b-r))).1)=-(q (a+b-r)).2
    simp [spectralScalarField]
  · change -(((-1 : ℝ) • spectralScalarField V (q (a+b-r))).2)=-V*(q (a+b-r)).1
    simp [spectralScalarField]

theorem spectralScalarReflect_continuous (a b : ℝ) (q : ℝ → ℂ × ℂ) (hq : Continuous q) :
    Continuous (spectralScalarReflect a b q) := by
  have hc : Continuous (fun r => q (a+b-r)) := hq.comp (continuous_const.sub continuous_id)
  exact hc.fst.prodMk hc.snd.neg

theorem spectralScalarReflect_norm (a b r k : ℝ) (q : ℝ → ℂ × ℂ) :
    spectralShellNorm k (spectralScalarReflect a b q r)=spectralShellNorm k (q (a+b-r)) := by
  simp only [spectralScalarReflect,spectralShellNorm,norm_neg]

theorem spectralScalar_terminal_exists (a b : ℝ) (hab : a≤ b)
    (V : ℝ → ℂ) (hV : ContinuousOn V (Icc a b)) (x : ℂ × ℂ) :
    ∃ q : ℝ → ℂ × ℂ, Continuous q ∧ q b=x ∧
      ∀ r ∈ Icc a b, HasDerivAt q (spectralScalarField (V r) (q r)) r := by
  let W := fun t : ℝ => V (a+b-t)
  have hW : ContinuousOn W (Icc a b) := hV.comp
    (continuous_const.sub continuous_id).continuousOn (by
      intro t ht
      constructor <;> linarith [ht.1,ht.2])
  obtain ⟨z,hz,hza,hzd⟩ := spectralScalar_local_exists a b hab W hW (x.1,-x.2)
  refine ⟨spectralScalarReflect a b z,spectralScalarReflect_continuous a b z hz,?_,?_⟩
  · simp only [spectralScalarReflect,add_sub_cancel_right,hza,neg_neg,Prod.mk.eta]
  · intro r hr
    have hrr : a+b-r ∈ Icc a b := by constructor <;> linarith [hr.1,hr.2]
    have hh := spectralScalarReflect_hasDerivAt a b r z (W (a+b-r)) (hzd _ hrr)
    have he : W (a+b-r)=V r := by dsimp only [W]; congr 1; ring
    simpa only [he] using hh

end DefocusingNLS

end OAI
