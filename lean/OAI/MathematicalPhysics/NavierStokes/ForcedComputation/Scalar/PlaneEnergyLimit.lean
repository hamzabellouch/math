import OAI.MathematicalPhysics.NavierStokes.ShearFlows.ClassicalUniqueness
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCutoffLimit

namespace OAI

/-! The limiting step in the noncompact energy argument. A vanishing
boundary error is allowed in each compactly localized energy estimate. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set Filter
open scoped Topology

theorem localized_energy_bound {E : ℝ → ℝ} {T C ε : ℝ} (hT : 0 ≤ T)
    (hε : 0 ≤ ε) (hc : ContinuousOn E (Icc 0 T)) (h0 : E 0 = 0)
    (hn : ∀ t ∈ Icc 0 T, 0 ≤ E t)
    (hd : ∀ t ∈ Ioo 0 T, ∃ e, HasDerivAt E e t ∧ e ≤ C * E t + ε) :
    E T ≤ ε * Real.exp ((|C| + 1) * T) := by
  let A := |C| + 1
  let W : ℝ → ℝ := fun t => Real.exp (-A * t) * (E t + ε)
  have hWc : ContinuousOn W (Icc 0 T) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      (hc.add continuousOn_const)
  have hWd (t : ℝ) (ht : t ∈ Ioo 0 T) :
      ∃ e, HasDerivAt W e t ∧ e ≤ 0 := by
    obtain ⟨e, he, heB⟩ := hd t ht
    have hn' := hn t ⟨ht.1.le, ht.2.le⟩
    have hCA : C ≤ A := by dsimp [A]; linarith [le_abs_self C]
    have hA : 1 ≤ A := by dsimp [A]; linarith [abs_nonneg C]
    have heA : e ≤ A * (E t + ε) := by
      have h1 := mul_le_mul_of_nonneg_right hCA hn'
      have h2 := mul_le_mul_of_nonneg_right hA hε
      nlinarith
    refine ⟨_, (((hasDerivAt_id t).const_mul (-A)).exp).mul (he.add_const ε), ?_⟩
    simp only [id_eq, mul_one]
    nlinarith [mul_nonneg (Real.exp_pos (-A * t)).le (sub_nonneg.mpr heA)]
  have hant : AntitoneOn W (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hWc
    · intro t ht
      obtain ⟨e, he, _⟩ := hWd t (by simpa only [interior_Icc] using ht)
      exact he.differentiableAt.differentiableWithinAt
    · intro t ht
      obtain ⟨e, he, he0⟩ := hWd t (by simpa only [interior_Icc] using ht)
      simpa only [he.deriv] using he0
  have hle := hant ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
  have hw : Real.exp (-A * T) * (E T + ε) ≤ ε := by
    simpa only [W, h0, mul_zero, Real.exp_zero, zero_add, one_mul] using hle
  have hh := mul_le_mul_of_nonneg_left hw (Real.exp_pos (A * T)).le
  have hexp : Real.exp (A * T) * Real.exp (-A * T) = 1 := by
    rw [← Real.exp_add, show A * T + -A * T = 0 by ring, Real.exp_zero]
  rw [← mul_assoc, hexp, one_mul] at hh
  dsimp only [A] at hh
  nlinarith

theorem zero_of_localized_energy_limit {E : ℕ → ℝ → ℝ} {ε : ℕ → ℝ}
    {T C limit : ℝ} (hT : 0 ≤ T) (hε : ∀ n, 0 ≤ ε n)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hc : ∀ n, ContinuousOn (E n) (Icc 0 T)) (h0 : ∀ n, E n 0 = 0)
    (hn : ∀ n t, t ∈ Icc 0 T → 0 ≤ E n t)
    (hd : ∀ n t, t ∈ Ioo 0 T →
      ∃ e, HasDerivAt (E n) e t ∧ e ≤ C * E n t + ε n)
    (hlim : Tendsto (fun n => E n T) atTop (𝓝 limit)) : limit = 0 := by
  have hnonneg : 0 ≤ limit := le_of_tendsto_of_tendsto
    tendsto_const_nhds hlim (Filter.Eventually.of_forall (fun n => hn n T ⟨hT, le_rfl⟩))
  have hupper : limit ≤ 0 := by
    have hlim' := hεlim.mul_const (Real.exp ((|C| + 1) * T))
    simp only [zero_mul] at hlim'
    exact le_of_tendsto_of_tendsto' hlim hlim' (fun n =>
      localized_energy_bound hT (hε n) (hc n) (h0 n) (hn n) (hd n))
  exact le_antisymm hupper hnonneg

end ForcedComputation.VelocityDetector

end

end OAI
