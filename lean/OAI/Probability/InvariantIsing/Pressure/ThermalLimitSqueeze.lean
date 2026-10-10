import OAI.Probability.InvariantIsing.Spectral.SpectralApproximationSqueeze
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Integer temperatures determine a unique deterministic zero-temperature limit. -/

noncomputable section
open Filter
open scoped Topology

namespace InvariantIsing

lemma thermal_squeeze_tendsto (p : ℕ → ℕ → ℝ) (g v : ℕ → ℝ) (c L : ℝ)
    (hc : 0 ≤ c) (hv : Tendsto v atTop (𝓝 L))
    (hp : ∀ k, Tendsto (p k) atTop (𝓝 (v k)))
    (hb : ∀ k, ∀ᶠ N in atTop, p k N ≤ g N ∧ g N ≤ p k N+c/(k+1)) :
    Tendsto g atTop (𝓝 L) := by
  have hδ : Tendsto (fun k : ℕ => 2*(c/(k+1))) atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2*c)
    simp only [mul_zero] at hh
    convert hh using 1
    funext k
    ring
  apply spectral_approximation_squeeze g p p v (fun k => 2*(c/(k+1))) L hv hδ hp hp
  intro k
  filter_upwards [hb k] with N hN
  have hnonneg : 0 ≤ c/(k+1) := by positivity
  constructor <;> linarith [hN.1,hN.2]

lemma exists_thermal_ground_limit (p : ℕ → ℕ → ℝ) (g v : ℕ → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hp : ∀ k, Tendsto (p k) atTop (𝓝 (v k)))
    (hb : ∀ k, ∀ᶠ N in atTop, p k N ≤ g N ∧ g N ≤ p k N+c/(k+1)) :
    ∃ L : ℝ, Tendsto v atTop (𝓝 L) ∧ Tendsto g atTop (𝓝 L) := by
  have horder (k l : ℕ) : v k ≤ v l+c/(l+1) := by
    apply le_of_tendsto_of_tendsto (hp k) ((hp l).add_const _)
    filter_upwards [hb k,hb l] with N hk hl
    exact hk.1.trans hl.2
  have hδ : Tendsto (fun k : ℕ => c/(k+1)) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul c
  have hC : CauchySeq v := by
    apply cauchySeq_of_le_tendsto_0 (fun k : ℕ => c/(k+1)) _ hδ
    intro n m k hn hm
    have hn' : (k : ℝ)+1 ≤ (n : ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hn 1
    have hm' : (k : ℝ)+1 ≤ (m : ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hm 1
    have hen : c/((n : ℝ)+1) ≤ c/((k : ℝ)+1) :=
      div_le_div_of_nonneg_left hc (by positivity) hn'
    have hem : c/((m : ℝ)+1) ≤ c/((k : ℝ)+1) :=
      div_le_div_of_nonneg_left hc (by positivity) hm'
    rw [Real.dist_eq,abs_le]
    constructor <;> linarith [horder n m,horder m n]
  obtain ⟨L,hL⟩ := cauchySeq_tendsto_of_complete hC
  exact ⟨L,hL,thermal_squeeze_tendsto p g v c L hc hL hp hb⟩

end InvariantIsing

end

end OAI
