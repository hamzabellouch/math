import OAI.NumberTheory.TotientAsymptotic.PPTResidualComparison
import OAI.NumberTheory.TotientAsymptotic.PPTGridCount

namespace OAI

/-!
The grid separation used in the residual comparison follows from the
actual contraction of candidate prime coordinates.  Normality changes a
prime coordinate to its largest-predecessor-factor coordinate by at most
the doubled mesh.  The inverse-cube contraction still dominates all
paired-grid padding in the logarithmic local dimension range.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

/-- Uniform replacement of a normal prime by the largest factor of its
predecessor, on the local comparison scale. -/
theorem ppt_normal_factor_loss_mesh : ∀ᶠ z : ℝ in atTop,
    ∀ (p : ℕ) (S : ℝ), 3 ≤ p → 1 < S → 0 ≤ B S → S ≤ z →
      IsNormalPrime S p → (p-1 : ℕ) ≤ z →
      B p/B z-2*((Real.log (B z))^5/Real.sqrt (B z)) ≤
        B (largestPrimeFactor (p-1))/B z ∧
      B (largestPrimeFactor (p-1))/B z ≤ B p/B z := by
  filter_upwards [B_tendsto.eventually ppt_logarithmic_alignment_error,
    B_tendsto.eventually (eventually_ge_atTop (Real.exp 1))] with z herror hB
  intro p S hp3 hS hBS hSz hp hpz
  have hB0 : 0 < B z := (Real.exp_pos 1).trans_le hB
  have hp1 : (1 : ℝ) < (p-1 : ℕ) := by
    exact_mod_cast (show 1 < p-1 by omega)
  have hpred : B (p-1 : ℕ) ≤ B z :=
    Real.log_le_log (Real.log_pos hp1)
      (Real.log_le_log (zero_lt_one.trans hp1) hpz)
  have hBSz : B S ≤ B z :=
    Real.log_le_log (Real.log_pos hS)
      (Real.log_le_log (zero_lt_one.trans hS) hSz)
  have hband := normal_prime_largest_band hp hp3 hS hBS hBSz hB0 hpred le_rfl le_rfl
  have hlog : 1 ≤ Real.log (3*B z) := by
    have hmul : Real.exp 1 ≤ 3*B z := by linarith only [hB, Real.exp_pos 1]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hmul
  have hloss : (1+Real.log (3*B z))/B z ≤
      2*((Real.log (B z))^5/Real.sqrt (B z)) := by
    have hh := div_le_div_of_nonneg_right
      (show 1+Real.log (3*B z) ≤ 2*Real.log (3*B z) by linarith only [hlog]) hB0.le
    have hh' : (1+Real.log (3*B z))/B z ≤ 2*(Real.log (3*B z)/B z) := by
      convert hh using 1
      ring
    linarith only [hh', herror]
  constructor
  · have hh := div_le_div_of_nonneg_right hband.1 hB0.le
    have he : (B p-1-Real.log (3*B z))/B z =
        B p/B z-(1+Real.log (3*B z))/B z := by ring
    rw [he] at hh
    linarith only [hh, hloss]
  · exact div_le_div_of_nonneg_right hband.2 hB0.le

/-- A geometric contraction of prime coordinates gives a quantitative
gap after replacing them by predecessor-factor coordinates. -/
lemma ppt_contracted_factor_gap {t u u' v v' ω δ : ℝ} {H : ℕ}
    (ht : 0 < t) (hH : 1 ≤ H)
    (hlower : 1/t^(1/3 : ℝ) ≤ u)
    (hω : 1/(10*(H : ℝ)^3) ≤ ω) (hω1 : ω ≤ 1)
    (hcontract : u' ≤ u/(1+ω))
    (hfactor : u-δ ≤ v) (hfactor' : v' ≤ u') :
    1/(20*(H : ℝ)^3*t^(1/3 : ℝ))-δ ≤ v-v' := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast (zero_lt_one.trans_le hH)
  have htroot : 0 < t^(1/3 : ℝ) := Real.rpow_pos_of_pos ht _
  have hω0 : 0 < ω := (by positivity : 0 < 1/(10*(H : ℝ)^3)).trans_le hω
  have hu : 0 ≤ u := (one_div_pos.mpr htroot).le.trans hlower
  have hgap := ppt_contraction_gap hu hω0 hω1
    (show u' ≤ u/(1+ω)+(0 : ℝ) by simpa only [add_zero] using hcontract)
  have hprod := mul_le_mul hω hlower (one_div_pos.mpr htroot).le hω0.le
  have hsmall : 1/(20*(H : ℝ)^3*t^(1/3 : ℝ)) ≤ ω*u/2 := by
    have hh := div_le_div_of_nonneg_right hprod (by norm_num : (0 : ℝ) ≤ 2)
    convert hh using 1
    ring
  linarith only [hgap, hsmall, hfactor, hfactor']

/-- The same gap pays for both normality alignment errors and the
larger padding that also gives the published adjacent-cutoff gap. -/
lemma ppt_paired_gap_of_inverse_cube {u u' v v' δ G : ℝ} {H j : ℕ}
    (hδ : 0 ≤ δ) (hG : 0 < G) (hj : j ≤ H)
    (hsmall : (8*(H : ℝ)+20)*δ < G)
    (hgap : 2*G-δ ≤ u-u')
    (halign : |u-v| ≤ (2*(j : ℝ)+1)*δ)
    (halign' : |u'-v'| ≤ (2*(j : ℝ)+3)*δ) :
    max u' v'+(2*(j : ℝ)+8)*δ < min u v := by
  have hjR : (j : ℝ) ≤ H := by exact_mod_cast hj
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hcost : (6*(j : ℝ)+13)*δ < G := by
    apply lt_of_le_of_lt _ hsmall
    exact mul_le_mul_of_nonneg_right (by linarith only [hjR, hH0]) hδ
  apply ppt_paired_gap_of_left_gap halign halign'
  linarith only [hcost, hgap, hG]

/-- Uniform geometric and normality estimates imply the actual paired
grid separation for every retained adjacent coordinate. -/
theorem ppt_local_contracted_grid_separation {A : ℝ} (hA : 0 < A) :
    ∀ᶠ t : ℝ in atTop, ∀ (H j : ℕ) (u u' v v' ω : ℝ),
      1 ≤ H → (H : ℝ) ≤ A*Real.log t → j ≤ H →
      1/t^(1/3 : ℝ) ≤ u →
      1/(10*(H : ℝ)^3) ≤ ω → ω ≤ 1 → u' ≤ u/(1+ω) →
      u-2*((Real.log t)^5/Real.sqrt t) ≤ v → v' ≤ u' →
      ∀ (w w' : ℝ),
        |v-w| ≤ (2*(j : ℝ)+1)*(2*((Real.log t)^5/Real.sqrt t)) →
        |v'-w'| ≤ (2*(j : ℝ)+3)*(2*((Real.log t)^5/Real.sqrt t)) →
        max v' w'+(2*(j : ℝ)+8)*(2*((Real.log t)^5/Real.sqrt t)) < min v w := by
  filter_upwards [ppt_log_dimension_separation hA,
    eventually_gt_atTop (1 : ℝ)] with t hsmall ht
  intro H j u u' v v' ω hH hdim hj hlower hω hω1 hcontract hfactor hfactor'
    w w' halign halign'
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hδ : 0 ≤ 2*((Real.log t)^5/Real.sqrt t) := by
    have hlog : 0 < Real.log t := Real.log_pos ht
    positivity
  have hHr : (0 : ℝ) < H := by exact_mod_cast (zero_lt_one.trans_le hH)
  have hG : 0 < 1/(40*(H : ℝ)^3*t^(1/3 : ℝ)) := by
    exact one_div_pos.mpr (mul_pos (by positivity) (Real.rpow_pos_of_pos ht0 _))
  have hgap := ppt_contracted_factor_gap ht0 hH hlower hω hω1 hcontract hfactor hfactor'
  have hgap' : 2*(1/(40*(H : ℝ)^3*t^(1/3 : ℝ)))-
      2*((Real.log t)^5/Real.sqrt t) ≤ v-v' := by
    convert hgap using 1
    ring
  exact ppt_paired_gap_of_inverse_cube hδ hG hj
    (by simpa only [mul_div_assoc] using hsmall H hH hdim) hgap' halign halign'

/-- The first rounded coordinate keeps a fixed inverse-log-cube loss
from one.  This feeds both the published first-cutoff power restriction
and the common adaptive head endpoint. -/
theorem ppt_local_contracted_first_loss {A : ℝ} (hA : 0 < A) :
    ∀ᶠ t : ℝ in atTop, ∀ (H : ℕ) (ω u ν : ℝ),
      1 ≤ H → (H : ℝ) ≤ A*Real.log t →
      1/(10*(H : ℝ)^3) ≤ ω → ω ≤ 1 →
      u ≤ (1+1/t)/(1+ω) →
      ν ≤ u+(2*(H : ℝ)+3)*(2*((Real.log t)^5/Real.sqrt t)) →
      ν ≤ 1-(1/(80*A^3))/(Real.log t)^3 := by
  filter_upwards [ppt_log_dimension_mesh_budget hA,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with t hbudget hlog ht
  intro H ω u ν hH hdim hω hω1 hu hν
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := zero_lt_one.trans_le hHr
  have hω0 : 0 < ω := (by positivity : 0 < 1/(10*(H : ℝ)^3)).trans_le hω
  have hden : 0 < 1+ω := by linarith only [hω0]
  have hm0 : 0 ≤ (Real.log t)^5/Real.sqrt t := by positivity
  have hrec := ppt_mesh_reciprocal_lower ht0 hlog
  let e : ℝ := 1/t+(2*(H : ℝ)+3)*(2*((Real.log t)^5/Real.sqrt t))
  have hH3 : (H : ℝ) ≤ (H : ℝ)^3 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hHr (show 1 ≤ 3 by omega))
  have herr : e ≤ 1/(80*(H : ℝ)^3) := by
    apply le_trans _ (hbudget H hH hdim)
    dsimp only [e]
    have hmul := mul_le_mul_of_nonneg_right
      (show 4*(H : ℝ)+7 ≤ 32*(H : ℝ)^3 by nlinarith only [hHr, hH3]) hm0
    nlinarith only [hrec, hmul]
  have herrω : 4*e ≤ ω := by
    have hsmall : 4*(1/(80*(H : ℝ)^3)) ≤ 1/(10*(H : ℝ)^3) := by
      have hpos : 0 ≤ 1/(10*(H : ℝ)^3) := by positivity
      have he : 4*(1/(80*(H : ℝ)^3)) = (1/2 : ℝ)*(1/(10*(H : ℝ)^3)) := by ring
      rw [he]
      linarith only [hpos]
    nlinarith only [herr, hsmall, hω]
  have hu' : u ≤ 1/(1+ω)+1/t := by
    apply hu.trans
    rw [add_div]
    apply add_le_add le_rfl
    apply (div_le_iff₀ hden).mpr
    have hp : 0 ≤ (1/t)*ω := mul_nonneg (one_div_pos.mpr ht0).le hω0.le
    nlinarith only [hp]
  have hν' : ν ≤ 1/(1+ω)+e := by
    dsimp only [e]
    linarith only [hu', hν]
  have hrecω : 1/(1+ω) ≤ 1-ω/2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hω0, hω1]
  have hmargin : (1/(80*A^3))/(Real.log t)^3 ≤ 1/(80*(H : ℝ)^3) := by
    have hp := pow_le_pow_left₀ hH0.le hdim 3
    have hh : 1/(80*(A*Real.log t)^3) ≤ 1/(80*(H : ℝ)^3) :=
      one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left hp (by norm_num))
    convert hh using 1
    rw [div_div, mul_pow]
    ring
  have hsmall : 1/(80*(H : ℝ)^3) ≤ ω/4 := by
    have hnonneg : 0 ≤ 1/(80*(H : ℝ)^3) := by positivity
    have he : 1/(10*(H : ℝ)^3) = 8*(1/(80*(H : ℝ)^3)) := by ring
    rw [he] at hω
    linarith only [hω, hnonneg]
  linarith only [hν', hrecω, herrω, hmargin, hsmall]

end TotientAsymptotic

end

end OAI
