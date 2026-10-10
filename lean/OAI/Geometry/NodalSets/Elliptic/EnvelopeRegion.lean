import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.MetricSpace.Thickening
import OAI.Geometry.NodalSets.Elliptic.CoordinateNorm

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section

def highEnvelopeRegion (Ω : Set Coord) (S S0 : Coord → ℝ) (n : ℕ) : Set Coord :=
  {x | x ∈ Ω ∧ -8*Real.log (n:ℝ)/(n:ℝ) ≤ S x-S0 x}

theorem high_envelope_fixed_compact {Ω U : Set Coord} (hΩ : IsCompact Ω)
    (hU : IsOpen U) (S S0 : Coord → ℝ) (hS : Continuous S) (hS0 : Continuous S0)
    {d : ℝ} (hd : 0 < d) (hgap : ∀ x ∈ Ω, x ∉ U → S x-S0 x ≤ -d) :
    ∃ Q : Set Coord, IsCompact Q ∧ Q ⊆ U ∧
      (∃ ε > 0, Metric.cthickening ε Q ⊆ U) ∧
      ∀ᶠ n : ℕ in atTop, highEnvelopeRegion Ω S S0 n ⊆ Q := by
  let Q := Ω ∩ {x | -d/2 ≤ S x-S0 x}
  have hQ : IsCompact Q := hΩ.inter_right (isClosed_le continuous_const (hS.sub hS0))
  have hQU : Q ⊆ U := by
    intro x hx
    by_contra hxu
    have h := hgap x hx.1 hxu
    have hx' := hx.2
    dsimp at hx'
    linarith
  refine ⟨Q,hQ,hQU,hQ.exists_cthickening_subset_open hU hQU,?_⟩
  have ht : Tendsto (fun n : ℕ ↦ -8*Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [div_eq_mul_inv,mul_assoc] using h.const_mul (-8)
  filter_upwards [ht.eventually (lt_mem_nhds (by linarith : -d/2 < (0:ℝ)))] with n hn
  intro x hx
  exact ⟨hx.1,hn.le.trans hx.2⟩

lemma high_envelope_bound {Ω : Set Coord} {S S0 : Coord → ℝ} {n : ℕ}
    (hn : 0 < n) {x : Coord} (hx : x ∈ highEnvelopeRegion Ω S S0 n) :
    max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x)) ≤
      (n:ℝ)^8*Real.exp ((n:ℝ)*S x) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hb : -8*Real.log (n:ℝ) ≤ (S x-S0 x)*(n:ℝ) :=
    (div_le_iff₀ hnR).mp hx.2
  have he : (n:ℝ)*S0 x ≤ 8*Real.log (n:ℝ)+(n:ℝ)*S x := by nlinarith
  apply max_le
  · have hp : (1:ℝ) ≤ (n:ℝ)^8 := one_le_pow₀ hn1
    nlinarith [Real.exp_pos ((n:ℝ)*S x)]
  · have h := Real.exp_le_exp.mpr he
    have hlog : Real.exp (8*Real.log (n:ℝ)) = (n:ℝ)^8 := by
      rw [show (8:ℝ)*Real.log (n:ℝ) = (8:ℕ)*Real.log (n:ℝ) by norm_num,
        Real.exp_nat_mul,Real.exp_log hnR]
    rw [Real.exp_add,hlog] at h
    exact h

lemma high_envelope_neighborhood_bound {Ω : Set Coord} {S S0 : Coord → ℝ} {n : ℕ}
    (hn : 0 < n) {x z : Coord} (hx : x ∈ highEnvelopeRegion Ω S S0 n)
    {L : ℝ} (hL : 0 ≤ L) (hLn : L ≤ (n:ℝ))
    (hz : ‖z-x‖ ≤ ((n:ℝ)^2)⁻¹)
    (hgap : (S0 z-S z)-(S0 x-S x) ≤ L*‖z-x‖) :
    max (Real.exp ((n:ℝ)*S z)) (Real.exp ((n:ℝ)*S0 z))*Real.exp (-(n:ℝ)*S z) ≤
      Real.exp 1*(n:ℝ)^8 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hstep : L*‖z-x‖ ≤ 1/(n:ℝ) := by
    calc
      _ ≤ L*((n:ℝ)^2)⁻¹ := mul_le_mul_of_nonneg_left hz hL
      _ ≤ (n:ℝ)*((n:ℝ)^2)⁻¹ := mul_le_mul_of_nonneg_right hLn (by positivity)
      _ = _ := by field_simp
  have hdiff := hgap.trans hstep
  have hdiff' := (le_div_iff₀ hnR).mp hdiff
  have hb := (div_le_iff₀ hnR).mp hx.2
  have hpow : (1:ℝ) ≤ (n:ℝ)^8 := one_le_pow₀ hn1
  have hnum : (n:ℝ)*S0 z ≤ 1+8*Real.log (n:ℝ)+(n:ℝ)*S z := by nlinarith
  have hlog : Real.exp (8*Real.log (n:ℝ)) = (n:ℝ)^8 := by
    rw [show (8:ℝ)*Real.log (n:ℝ) = (8:ℕ)*Real.log (n:ℝ) by norm_num,
      Real.exp_nat_mul,Real.exp_log hnR]
  have hmax : max (Real.exp ((n:ℝ)*S z)) (Real.exp ((n:ℝ)*S0 z)) ≤
      (Real.exp 1*(n:ℝ)^8)*Real.exp ((n:ℝ)*S z) := by
    apply max_le
    · have he1 : 1 ≤ Real.exp (1:ℝ) := Real.one_le_exp_iff.mpr zero_le_one
      have hprod : 1 ≤ Real.exp 1*(n:ℝ)^8 := one_le_mul_of_one_le_of_one_le he1 hpow
      nlinarith [Real.exp_pos ((n:ℝ)*S z)]
    · have h := Real.exp_le_exp.mpr hnum
      rw [Real.exp_add,Real.exp_add,hlog] at h
      exact h
  have h := mul_le_mul_of_nonneg_right hmax (Real.exp_pos (-(n:ℝ)*S z)).le
  have he : Real.exp ((n:ℝ)*S z)*Real.exp (-(n:ℝ)*S z) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  simpa only [mul_assoc,he,mul_one] using h

end
end Yau.Geometry

end OAI
