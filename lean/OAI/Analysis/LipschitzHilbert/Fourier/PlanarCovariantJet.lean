import OAI.Analysis.LipschitzHilbert.Fourier.PlanarSchwartzSlice

namespace OAI

/-! The first two covariant vertical derivatives of a general planar
Schwartz packet, restricted to a reference line. -/

noncomputable section
namespace LipschitzHilbert

def planarVerticalDerivative (f : SchwartzMap (ℝ × ℝ) ℂ) : SchwartzMap (ℝ × ℝ) ℂ :=
  SchwartzMap.evalCLM ℂ (ℝ × ℝ) ℂ (0,1) (SchwartzMap.fderivCLM ℂ (ℝ × ℝ) ℂ f)

@[simp] theorem planarVerticalDerivative_apply (f : SchwartzMap (ℝ × ℝ) ℂ) (z : ℝ × ℝ) :
    planarVerticalDerivative f z = fderiv ℝ f z (0,1) := rfl

def planarCovariantDerivative (f : SchwartzMap (ℝ × ℝ) ℂ) (frequency : ℝ) :
    SchwartzMap (ℝ × ℝ) ℂ :=
  planarVerticalDerivative f-((frequency:ℂ)*Complex.I) • f

theorem planarCovariantDerivative_slice (f : SchwartzMap (ℝ × ℝ) ℂ)
    (frequency scale b s x : ℝ) :
    (scale:ℂ)*(deriv (fun y => planarSchwartzSlice f y s x) b-
      (frequency:ℂ)*Complex.I*planarSchwartzSlice f b s x) =
      planarSchwartzSlice ((scale:ℂ) • planarCovariantDerivative f frequency) b s x := by
  rw [(planarSchwartzSlice_vertical_hasDerivAt f b s x).deriv]
  simp only [planarSchwartzSlice_apply,smul_apply,smul_eq_mul,
    planarCovariantDerivative,sub_apply,planarVerticalDerivative_apply]

def planarCovariantJet (f : SchwartzMap (ℝ × ℝ) ℂ) (frequency scale : ℝ)
    (i : Fin 3) : SchwartzMap (ℝ × ℝ) ℂ :=
  if i = 0 then f else if i = 1 then (scale:ℂ) • planarCovariantDerivative f frequency else
    (scale:ℂ) • planarCovariantDerivative ((scale:ℂ) • planarCovariantDerivative f frequency) frequency

theorem planarCovariantJet_slice_zero (f : SchwartzMap (ℝ × ℝ) ℂ)
    (frequency scale b s x : ℝ) :
    (scale:ℂ)*(deriv (fun y => planarSchwartzSlice (planarCovariantJet f frequency scale 0) y s x) b-
      (frequency:ℂ)*Complex.I*planarSchwartzSlice (planarCovariantJet f frequency scale 0) b s x) =
      planarSchwartzSlice (planarCovariantJet f frequency scale 1) b s x := by
  simpa [planarCovariantJet] using
    planarCovariantDerivative_slice f frequency scale b s x

theorem planarCovariantJet_slice_one (f : SchwartzMap (ℝ × ℝ) ℂ)
    (frequency scale b s x : ℝ) :
    (scale:ℂ)*(deriv (fun y => planarSchwartzSlice (planarCovariantJet f frequency scale 1) y s x) b-
      (frequency:ℂ)*Complex.I*planarSchwartzSlice (planarCovariantJet f frequency scale 1) b s x) =
      planarSchwartzSlice (planarCovariantJet f frequency scale 2) b s x := by
  simpa [planarCovariantJet] using
    planarCovariantDerivative_slice ((scale:ℂ) • planarCovariantDerivative f frequency)
      frequency scale b s x

theorem planarCovariantJet_slice_continuous (f : SchwartzMap (ℝ × ℝ) ℂ)
    (frequency scale s : ℝ) (i : Fin 3) :
    Continuous (fun z : ℝ × ℝ => planarSchwartzSlice (planarCovariantJet f frequency scale i) z.1 s z.2) :=
  planarSchwartzSlice_jointContinuous _ s

theorem planarCovariantJet_slice_differentiable (f : SchwartzMap (ℝ × ℝ) ℂ)
    (frequency scale b s x : ℝ) (i : Fin 3) :
    DifferentiableAt ℝ (fun y => planarSchwartzSlice (planarCovariantJet f frequency scale i) y s x) b :=
  (planarSchwartzSlice_vertical_hasDerivAt _ b s x).differentiableAt

end LipschitzHilbert

end

end OAI
