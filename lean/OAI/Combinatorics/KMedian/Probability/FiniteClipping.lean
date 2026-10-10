import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteLaws
import OAI.Combinatorics.KMedian.Preparation.PreparationMoments

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω I : Type*} [Fintype Ω] [Fintype I]

omit [Fintype I] in
 theorem nonneg_expect_zero_support (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (hX : ∀ ω, 0 ≤ X ω) (hmean : μ.expect X=0) :
    ∀ ω, 0 < μ.weight ω → X ω=0 := by
  intro ω hω
  have hh := single_le_sum (s := univ) (f := fun ξ => μ.weight ξ*X ξ)
    (fun ξ _ => mul_nonneg (μ.nonneg ξ) (hX ξ)) (mem_univ ω)
  change μ.weight ω*X ω ≤ μ.expect X at hh
  rw [hmean] at hh
  exact le_antisymm (by nlinarith only [hh, hω]) (hX ω)

theorem half_clip_point {z m : ℝ} (hm : m ≤ 1/4) :
    z-min z (1/2) ≤ 4*(z-m)^2 := by
  by_cases hz : z ≤ 1/2
  · rw [min_eq_left hz, sub_self]
    positivity
  · rw [min_eq_right (le_of_not_ge hz)]
    nlinarith only [hm, sq_nonneg (2*(z-m)-1/4)]

omit [Fintype I] in
 theorem expected_half_clip (μ : FiniteLaw Ω) (Z : Ω → ℝ)
    {v : ℝ} (hmean : μ.expect Z ≤ 1/4) (hvar : μ.variance Z ≤ v) :
    μ.expect (fun ω => Z ω-min (Z ω) (1/2)) ≤ 4*v := by
  have he := μ.expect_mono (fun ω => half_clip_point (z := Z ω) hmean)
  rw [expect_mul] at he
  exact he.trans (mul_le_mul_of_nonneg_left hvar (by norm_num))

theorem clipping_budget (μ : FiniteLaw Ω) (Z : I → Ω → ℝ) (c : I → ℝ)
    {g γ : ℝ} (hg : 0 ≤ g) (hγ : 0 < γ)
    (hc : ∀ i, 0 ≤ c i)
    (hmean : ∀ i, μ.expect (Z i) ≤ 1/4)
    (hvar : ∀ i, μ.variance (Z i) ≤ g*(1+γ)*c i) :
    1-4*g*(1+γ)/γ ≤ μ.prob (fun ω =>
      (∑ i, (Z i ω-min (Z i ω) (1/2))) ≤ γ*∑ i, c i) := by
  classical
  let W : Ω → ℝ := fun ω => ∑ i, (Z i ω-min (Z i ω) (1/2))
  have hW : ∀ ω, 0 ≤ W ω := by
    intro ω
    exact sum_nonneg (fun i _ => sub_nonneg.mpr (min_le_left _ _))
  have hE : μ.expect W ≤ 4*g*(1+γ)*∑ i, c i := by
    change μ.expect (fun ω => ∑ i, (Z i ω-min (Z i ω) (1/2))) ≤ _
    rw [expect_sum, mul_sum]
    exact sum_le_sum (fun i _ => (expected_half_clip μ (Z i) (hmean i) (hvar i)).trans_eq (by ring))
  have hC : 0 ≤ ∑ i, c i := sum_nonneg (fun i _ => hc i)
  have hρ : 0 ≤ 4*g*(1+γ)/γ := by positivity
  have hfail : μ.prob (fun ω => γ*∑ i, c i < W ω) ≤ 4*g*(1+γ)/γ := by
    rcases hC.eq_or_lt with hz | hz
    · have hzero : μ.expect W=0 := le_antisymm (by simpa only [← hz, mul_zero] using hE)
        (μ.expect_nonneg hW)
      have hs := μ.nonneg_expect_zero_support W hW hzero
      have he0 : μ.prob (fun ω => γ*∑ i, c i < W ω)=0 := by
        change μ.expect (fun ω => if γ*∑ i, c i < W ω then 1 else 0)=0
        calc
          _ = μ.expect (fun _ => 0) := μ.expect_congr_support (fun ω hω => by
            rw [hs ω hω, ← hz, mul_zero, ite_eq_right (lt_irrefl 0)])
          _ = 0 := μ.expect_const _
      rw [he0]
      exact hρ
    · have he := μ.prob_le_expect_div W hW (mul_pos hγ hz)
      have hp := μ.prob_mono (E := fun ω => γ*∑ i, c i < W ω)
        (F := fun ω => γ*∑ i, c i ≤ W ω) (fun _ h => h.le)
      calc
        _ ≤ μ.expect W/(γ*∑ i, c i) := hp.trans he
        _ ≤ (4*g*(1+γ)*∑ i, c i)/(γ*∑ i, c i) := div_le_div_of_nonneg_right hE (by positivity)
        _ = _ := by field_simp
  have hcomp := μ.prob_compl (fun ω => γ*∑ i, c i < W ω)
  simp only [not_lt] at hcomp
  change 1-4*g*(1+γ)/γ ≤ μ.prob (fun ω => W ω ≤ γ*∑ i, c i)
  rw [hcomp]
  linarith only [hfail]

theorem abs_clip_le {z c b : ℝ} (hcb : c ≤ b) : |c-min z b| ≤ |c-z| := by
  by_cases hz : z ≤ b
  · rw [min_eq_left hz]
  · rw [min_eq_right (le_of_not_ge hz), abs_of_nonpos (sub_nonpos.mpr hcb),
      abs_of_nonpos (sub_nonpos.mpr (hcb.trans (le_of_not_ge hz)))]
    linarith only [hz]

omit [Fintype I] in
 theorem rescaling_noise (μ : FiniteLaw Ω) (Z : Ω → ℝ) {c γ g : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1/2) (hγ : 0 ≤ γ) (_hg : 0 ≤ g)
    (hmean : μ.expect Z=(1+γ)*c) (hvar : μ.variance Z ≤ g*(1+γ)*c) :
    μ.expect (fun ω => |c-min (Z ω) (1/2)|) ≤ γ*c+Real.sqrt (g*(1+γ)*c) := by
  have hp : ∀ ω, |c-min (Z ω) (1/2)| ≤ γ*c+|Z ω-μ.expect Z| := by
    intro ω
    calc
      _ ≤ |c-Z ω| := abs_clip_le hc1
      _ ≤ |c-μ.expect Z|+|μ.expect Z-Z ω| := by
        have he : c-Z ω=(c-μ.expect Z)+(μ.expect Z-Z ω) := by ring
        rw [he]
        exact abs_add_le _ _
      _ = γ*c+|Z ω-μ.expect Z| := by
        rw [hmean, abs_sub_comm ((1+γ)*c) (Z ω)]
        congr 1
        have he : c-(1+γ)*c= -(γ*c) := by ring
        rw [he, abs_neg, abs_of_nonneg (mul_nonneg hγ hc)]
  have he := μ.expect_mono hp
  simp only [expect_add, expect_const] at he
  exact he.trans (add_le_add_right ((μ.expect_abs_centered_le_sqrt Z).trans
    (Real.sqrt_le_sqrt hvar)) _)

end MetricKMedian.FiniteLaw
end
end

end OAI
