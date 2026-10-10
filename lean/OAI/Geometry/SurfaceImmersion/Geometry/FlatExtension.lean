import Mathlib

namespace OAI

/-! Smooth zero extensions are flat at the boundary of their zero region. -/

noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Vanishing on an open region forces every derivative to vanish on its closure. -/
theorem iteratedFDeriv_zero_on_closure {F : A → E} (hF : ContDiff ℝ ∞ F)
    {O : Set A} (hO : IsOpen O) (hz : ∀ p ∈ O, F p = 0) (n : ℕ) :
    Set.EqOn (iteratedFDeriv ℝ n F) (fun _ => 0) (closure O) := by
  have ho : Set.EqOn (iteratedFDeriv ℝ n F) (fun _ => 0) O := by
    intro p hp
    have he : F =ᶠ[𝓝 p] (fun _ : A => (0 : E)) := by
      filter_upwards [hO.mem_nhds hp] with q hq
      exact hz q hq
    have hd := (he.iteratedFDeriv ℝ n).eq_of_nhds
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using hd
  exact ho.closure (hF.continuous_iteratedFDeriv (by simp)) continuous_const

end ClosedSurfaceR4

end

end OAI
