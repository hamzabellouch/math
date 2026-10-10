import OAI.Geometry.NodalSets.Elliptic.AffineRescalingJets
import OAI.Geometry.NodalSets.Waves.ExponentialWaveBounds
import OAI.Geometry.NodalSets.Waves.WaveSize

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma local_mul_jet_bound {U : Set Coord} (hU : IsOpen U)
    (f g : Coord → ℂ) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : Coord} (hx : x ∈ U) (k : ℕ) {A B : ℝ} (hA : 0 ≤ A)
    (hfa : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hgb : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun z ↦ f z*g z) x‖ ≤ 2^k*A*B := by
  obtain ⟨F,hF,heF⟩ := smoothOn_global_germ hU f hf hx
  obtain ⟨G,hG,heG⟩ := smoothOn_global_germ hU g hg hx
  have hprod : (fun z ↦ F z*G z) =ᶠ[𝓝 x] (fun z ↦ f z*g z) := heF.mul heG
  rw [← (hprod.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds]
  have hh := mul_derivative_power_bound hF hG k x hA (by norm_num : (0:ℝ) ≤ 1)
    (N := 1) (w := 1)
    (fun j hj ↦ by simpa only [one_pow,mul_one,(heF.iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds] using hfa j hj)
    (fun j hj ↦ by simpa only [one_pow,mul_one,(heG.iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds] using hgb j hj)
  simpa only [one_pow,mul_one] using hh

lemma small_exp_jet_threshold (d : ℕ) (e : ℝ) (he : 0 < e) :
    ∃ delta > 0, ∀ (U : Set Coord), IsOpen U → ∀ f : Coord → ℂ,
      ContDiffOn ℝ ∞ f U → ∀ x ∈ U,
      (∀ j, j ≤ d → ‖iteratedFDeriv ℝ j f x‖ ≤ delta) →
      ∀ k, k ≤ d → ‖iteratedFDeriv ℝ k (fun z ↦ Complex.exp (f z)-1) x‖ ≤ e := by
  let q := min 1 (e/(3*(d.factorial:ℝ)+2))
  have hq : 0 < q := lt_min zero_lt_one (by positivity)
  have hq1 : q ≤ 1 := min_le_left _ _
  have hqe : (3*(d.factorial:ℝ)+2)*q ≤ e := by
    have hh := (le_div_iff₀ (by positivity : 0 < 3*(d.factorial:ℝ)+2)).mp (min_le_right 1 (e/(3*(d.factorial:ℝ)+2)))
    nlinarith
  refine ⟨q^(d+1),by positivity,?_⟩
  intro U hU f hf x hx hb k hk
  obtain ⟨F,hF,heF⟩ := smoothOn_global_germ hU f hf hx
  have hbf (j : ℕ) (hj : j ≤ d) : ‖iteratedFDeriv ℝ j F x‖ ≤ q^(d+1) := by
    rw [(heF.iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds]
    exact hb j hj
  have hqp : q^(d+1) ≤ q := by
    simpa only [pow_one] using pow_le_pow_of_le_one hq.le hq1 (show 1 ≤ d+1 by omega)
  have hFx : ‖F x‖ ≤ q := by simpa only [norm_iteratedFDeriv_zero] using (hbf 0 (Nat.zero_le d)).trans hqp
  have hExp : ‖Complex.exp (F x)‖ ≤ 3 := by
    have hh := norm_add_le (Complex.exp (F x)-1) (1:ℂ)
    simp only [sub_add_cancel,norm_one] at hh
    have hh' := Complex.norm_exp_sub_one_le (hFx.trans hq1)
    linarith
  have hcomp : (fun z ↦ Complex.exp (F z)-1) =ᶠ[𝓝 x] (fun z ↦ Complex.exp (f z)-1) := by
    filter_upwards [heF] with z hz
    rw [hz]
  rw [← (hcomp.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds]
  by_cases hk0 : k = 0
  · subst k
    rw [norm_iteratedFDeriv_zero]
    exact (Complex.norm_exp_sub_one_le (hFx.trans hq1)).trans (by nlinarith [(show (0:ℝ) ≤ d.factorial from Nat.cast_nonneg _)])
  have hs : ContDiff ℝ ∞ (fun z ↦ Complex.exp (F z)) := Complex.contDiff_exp.comp hF
  change ‖iteratedFDeriv ℝ k ((fun z ↦ Complex.exp (F z)) - fun _ ↦ 1) x‖ ≤ e
  rw [iteratedFDeriv_sub_apply (hs.contDiffAt.of_le (by
      exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))) contDiffAt_const,
    iteratedFDeriv_const_of_ne hk0]
  simp only [Pi.zero_apply,sub_zero]
  have hh := norm_iteratedFDeriv_comp_le (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)) hF
    (n := k) (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)) x (C := 3) (D := q)
    (fun j hj ↦ by rw [norm_iteratedFDeriv_complex_exp,← Complex.norm_exp]; exact hExp)
    (fun j hj hjk ↦ (hbf j (hjk.trans hk)).trans (pow_le_pow_of_le_one hq.le hq1 (by omega)))
  have hkfact : (k.factorial:ℝ) ≤ d.factorial := by exact_mod_cast Nat.factorial_le hk
  have hkpow : q^k ≤ q := by simpa only [pow_one] using pow_le_pow_of_le_one hq.le hq1 (show 1 ≤ k by omega)
  apply hh.trans
  have hh' : (k.factorial:ℝ)*3*q^k ≤ (d.factorial:ℝ)*3*q := by gcongr
  exact hh'.trans (by nlinarith)

end
end Yau.Geometry

end OAI
