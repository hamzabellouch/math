import OAI.Analysis.LipschitzHilbert.Fourier.SchwartzConjugation
import OAI.Analysis.LipschitzHilbert.Estimates.ShortSlopeOperator
import OAI.Analysis.LipschitzHilbert.Fourier.SharpKernelComparison

namespace OAI

/-! Negative vertical bands are conjugates of positive vertical bands. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

def conjugateReflectedCutoff (p : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  schwartzConj (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) p)

@[simp] theorem conjugateReflectedCutoff_apply (p : SchwartzMap ℝ ℂ) (s : ℝ) :
    conjugateReflectedCutoff p s=conj (p (-s)) := rfl

theorem conjugateReflectedCutoff_support (p : SchwartzMap ℝ ℂ)
    (hp : ∀ s, p s≠0 → 1≤s ∧ s≤2) :
    ∀ s, conjugateReflectedCutoff p s≠0 → -2≤s ∧ s≤ -1 := by
  intro s hs
  have hn : p (-s)≠0 := by
    intro hz
    exact hs (by simp only [conjugateReflectedCutoff_apply,hz,map_zero])
  have h := hp (-s) hn
  constructor <;> linarith only [h.1,h.2]

theorem conjugateReflectedCutoff_projection (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    schwartzVerticalProjection (conjugateReflectedCutoff p) w 0 f=
      schwartzConj (schwartzVerticalProjection p w 0 (schwartzConj f)) := by
  apply planar_schwartz_ext_fourier
  intro omega
  simp only [planarFourier_conj,schwartzVerticalProjection_fourier,
    conjugateReflectedCutoff_apply,sub_zero,Prod.snd_neg,mul_neg,map_mul,neg_neg,
    starRingEnd_apply,star_star]

theorem sharpTimeKernel_conj (epsilon R t : ℝ) :
    conj (sharpTimeKernel epsilon R t)=sharpTimeKernel epsilon R t := by
  unfold sharpTimeKernel
  split_ifs <;> simp

theorem shortSlopeOperator_conj (K : ℝ → ℂ) (hK : ∀ t, conj (K t)=K t)
    (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ) (z : ℝ×ℝ) :
    shortSlopeOperator K u (fun y => conj (f y)) z=conj (shortSlopeOperator K u f z) := by
  unfold shortSlopeOperator
  rw [←integral_conj]
  apply integral_congr_ae
  filter_upwards [] with t
  split_ifs <;> simp only [map_mul,hK,map_zero]

end LipschitzHilbert.PacketRepresentation

end

end OAI
