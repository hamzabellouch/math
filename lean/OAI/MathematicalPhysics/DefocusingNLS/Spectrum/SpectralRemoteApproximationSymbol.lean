import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteUniformInterpolation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteSymbol

namespace OAI

/-! Uniform finite expansions and coarse derivative growth imply the
order-zero symbol estimates on every escaping logarithmic half-line. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

theorem spectralRemote_approximation_symbol
    (F : ℕ → ℝ → ℂ) (P : ℕ → ℕ → ℝ → ℂ) (L : ℝ)
    (S : ℕ → ℝ) (hS : Tendsto S atTop atTop)
    (hF : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (F n) (Ioi L))
    (hP : ∀ n j, ContDiff ℝ ∞ (P n j))
    (hgrowth : ∀ k : ℕ, ∃ C B T : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ᶠ n in atTop,
      ∀ t, T ≤ t → ‖iteratedDeriv k (F n) t‖ ≤ B*Real.exp (C*t))
    (hpoly : ∀ j k : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n in atTop,
      ∀ t, 0 ≤ t → ‖iteratedDeriv k (P n j) t‖ ≤ D)
    (happrox : ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ A T : ℝ, 0 ≤ A ∧ ∀ᶠ n in atTop,
      ∀ t, T ≤ t → ‖F n t-P n j t‖ ≤ A*Real.exp (-(2*(j : ℝ))*t)) :
    HasUniformLogJetBound S 0 F := by
  refine ⟨?_,?_⟩
  · filter_upwards [hF,hS.eventually (eventually_ge_atTop L)] with n hn hSn
    exact hn.mono (Ioi_subset_Ioi hSn)
  · intro k
    obtain ⟨j,_,A,T,hA,hb⟩ := spectralRemote_uniform_expansion_derivatives F P L hF hP
      hgrowth hpoly happrox k 0 le_rfl 0
    obtain ⟨D,hD,hp⟩ := hpoly j k
    refine ⟨A+D,add_nonneg hA hD,?_⟩
    filter_upwards [hF,hb,hp,hS.eventually (eventually_ge_atTop (max T (max L 0)))]
      with n hFn hbn hpn hSn
    intro t ht
    have hTt : T ≤ t := (le_max_left T _).trans (hSn.trans ht.le)
    have hLt : L < t := ((le_max_left L 0).trans (le_max_right T _)).trans_lt (hSn.trans_lt ht)
    have ht0 : 0 ≤ t := ((le_max_right L 0).trans (le_max_right T _)).trans (hSn.trans ht.le)
    have hf : ContDiffAt ℝ k (F n) t := ((hFn t hLt).contDiffAt (Ioi_mem_nhds hLt)).of_le (by simp)
    have hpol : ContDiffAt ℝ k (P n j) t := (hP n j).contDiffAt.of_le (by simp)
    have hd : iteratedDeriv k (F n) t =
        iteratedDeriv k (fun s => F n s-P n j s) t+iteratedDeriv k (P n j) t := by
      rw [iteratedDeriv_fun_sub hf hpol]
      abel
    have hsmall := hbn t hTt
    simp only [neg_zero,zero_mul,Real.exp_zero,mul_one] at hsmall ⊢
    rw [hd]
    exact (norm_add_le _ _).trans (add_le_add hsmall (hpn t ht0))

end DefocusingNLS

end OAI
