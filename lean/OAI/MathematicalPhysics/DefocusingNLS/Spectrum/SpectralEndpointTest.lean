import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactRadialTest
import Mathlib.Analysis.Calculus.BumpFunction.Basic

namespace OAI

/-! A smooth test equal to one at the outer endpoint and zero below an inner radius. -/

open Set
open scoped SchwartzMap ContDiff
namespace DefocusingNLS

theorem spectralEndpointTest (a b : ℝ) (hab : a < b) :
    ∃ f : 𝓢(ℝ,ℂ), f b=1 ∧ (∀ x ≤ a, f x=0) ∧ (∀ x ≤ a, deriv f x=0) := by
  let φ : ContDiffBump b :=
    { rIn := (b-a)/4
      rOut := (b-a)/2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  let f := spectralRealSchwartzTest φ φ.contDiff φ.hasCompactSupport
  have hz (x : ℝ) (hx : x < (a+b)/2) : φ x=0 := by
    apply φ.zero_of_le_dist
    rw [Real.dist_eq,abs_of_nonpos (by linarith : x-b ≤ 0)]
    dsimp only [φ]
    linarith
  refine ⟨f,?_,?_,?_⟩
  · have h1 : φ b=1 := φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le)
    simp only [f,spectralRealSchwartzTest_apply,h1,Complex.ofReal_one]
  · intro x hx
    have hzero := hz x (by linarith)
    simp only [f,spectralRealSchwartzTest_apply,hzero,Complex.ofReal_zero]
  · intro x hx
    have heq : (φ : ℝ → ℝ) =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show x < (a+b)/2 by linarith)] with y hy
      exact hz y hy
    have hd : deriv φ x=0 := by rw [heq.deriv_eq]; exact deriv_const x 0
    simp only [f,spectralRealSchwartzTest_deriv,hd,Complex.ofReal_zero]

end DefocusingNLS

end OAI
