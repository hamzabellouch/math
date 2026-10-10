import Mathlib
import OAI.Combinatorics.TriangleRemoval.Asymptotics.OneAddLogRpow

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def prefixHorizon (n : ℕ) : ℝ := Real.log (1+2*prefixD n)/2

lemma prefixHorizon_bounds : ∀ᶠ n : ℕ in atTop,
    0 < prefixHorizon n ∧ prefixHorizon n ≤ Real.log n := by
  filter_upwards [prefix_scales_eventually_pos,eventually_ge_atTop (3 : ℕ)] with n hp hn
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : prefixD n ≤ n := by
    have hpl := prefixDensity_le_one n
    have hsq : (prefixDensity n)^2 ≤ 1 := by nlinarith [hp.1]
    exact (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg n)).trans_eq (mul_one _)
  have harg : 1+2*prefixD n ≤ (n : ℝ)^2 := by nlinarith
  have hl := Real.log_le_log (by linarith [hp.2] : 0 < 1+2*prefixD n) harg
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  unfold prefixHorizon
  exact ⟨div_pos (Real.log_pos (by linarith [hp.2])) (by norm_num),by linarith⟩

theorem prefix_bootstrap_numerics {c C₁ : ℝ} (hc : 0 < c) (hC₁ : 0 < C₁) (J : ℕ) :
    ∃ a : ℝ, 0 < a ∧ a < min c (1/1000 : ℝ) ∧ ∀ᶠ n : ℕ in atTop,
      let δ := (n : ℝ)^(-a)
      let S := prefixHorizon n
      let K := C₁*(1+Real.log n)^J
      0 < δ ∧ δ ≤ 1/2 ∧ 0 < S ∧ S ≤ Real.log n ∧
        12*S/prefixD n ≤ 1/4 ∧
        K*((n : ℝ)^(-c)+64*δ^2+1152*S/prefixD n)*S ≤ δ/2 := by
  let a := min c (1/1000 : ℝ)/3
  have ha : 0 < a := div_pos (lt_min hc (by norm_num)) (by norm_num)
  have hac : 2*a ≤ c := by dsimp [a]; linarith [min_le_left c (1/1000 : ℝ)]
  have had : 2*a ≤ (1/1000 : ℝ) := by dsimp [a]; linarith [min_le_right c (1/1000 : ℝ)]
  refine ⟨a,ha,by dsimp [a]; linarith [lt_min hc (by norm_num : (0 : ℝ) < 1/1000)],?_⟩
  have hδ := ((tendsto_rpow_neg_atTop ha).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_le_const
      (by norm_num : (0 : ℝ) < 1/2)
  have hb : 0 < 1/(2434*C₁) := by positivity
  filter_upwards [prefixHorizon_bounds,prefixD_eventual_envelope,prefix_scales_eventually_pos,
    prefixTemplateFactor_subpower (J+2) ha hb,
    prefixTemplateFactor_subpower 1 ha (by norm_num : (0 : ℝ) < 1/48),
    hδ,eventually_ge_atTop (1 : ℕ)] with n hS hD hp hpol hlog hδ hn
  dsimp only
  change (n : ℝ)^(-a) ≤ 1/2 at hδ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hL : 1 ≤ 1+Real.log n := by linarith
  have hna : 0 < (n : ℝ)^a := Real.rpow_pos_of_pos hn0 _
  have hn2a : 0 < (n : ℝ)^(-2*a) := Real.rpow_pos_of_pos hn0 _
  have hDa : (n : ℝ)^a ≤ prefixD n :=
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith : a ≤ (1/1000 : ℝ))).trans hD.1
  have hD2a : (n : ℝ)^(2*a) ≤ prefixD n :=
    (Real.rpow_le_rpow_of_exponent_le hn1 had).trans hD.1
  have hD0 : 0 < prefixD n := lt_of_lt_of_le zero_lt_one hp.2
  have hη : (n : ℝ)^(-c) ≤ (n : ℝ)^(-2*a) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hδsq : ((n : ℝ)^(-a))^2 = (n : ℝ)^(-2*a) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le]
    congr 1
    ring
  have hDinv : 1/prefixD n ≤ (n : ℝ)^(-2*a) := by
    calc
      _ ≤ 1/(n : ℝ)^(2*a) := div_le_div_of_nonneg_left zero_le_one
        (Real.rpow_pos_of_pos hn0 _) hD2a
      _ = _ := by rw [one_div,← Real.rpow_neg hn0.le]; congr 1; ring
  have hSD : prefixHorizon n/prefixD n ≤ (1+Real.log n)*(n : ℝ)^(-2*a) := by
    calc
      _ = prefixHorizon n*(1/prefixD n) := by ring
      _ ≤ (1+Real.log n)*(n : ℝ)^(-2*a) :=
        mul_le_mul (by linarith [hS.2]) hDinv (by positivity) (by linarith)
  have hsmall : 12*prefixHorizon n/prefixD n ≤ 1/4 := by
    have hlog' : 1+Real.log n ≤ (1/48 : ℝ)*(n : ℝ)^a := by
      simpa only [prefixTemplateFactor,Real.rpow_one] using hlog
    apply (div_le_iff₀ hD0).mpr
    nlinarith [hS.2,hDa]
  have hforce : (n : ℝ)^(-c)+64*((n : ℝ)^(-a))^2+
      1152*prefixHorizon n/prefixD n ≤ 1217*(1+Real.log n)*(n : ℝ)^(-2*a) := by
    rw [hδsq]
    have hhd := mul_le_mul_of_nonneg_left hSD (by norm_num : (0 : ℝ) ≤ 1152)
    have hhη := mul_le_mul_of_nonneg_right hL hn2a.le
    rw [mul_div_assoc]
    nlinarith only [hη,hhη,hhd]
  have hpol' : (1+Real.log n)^(J+2) ≤ 1/(2434*C₁)*(n : ℝ)^a := by
    unfold prefixTemplateFactor at hpol
    rw [show (J : ℝ)+2 = ((J+2 : ℕ) : ℝ) by norm_cast,Real.rpow_natCast] at hpol
    exact hpol
  have hm : C₁*(1+Real.log n)^J *
      ((n : ℝ)^(-c)+64*((n : ℝ)^(-a))^2+1152*prefixHorizon n/prefixD n)*
        prefixHorizon n ≤
        1217*C₁*(1+Real.log n)^(J+2)*(n : ℝ)^(-2*a) := by
    calc
      _ ≤ C₁*(1+Real.log n)^J * (1217*(1+Real.log n)*(n : ℝ)^(-2*a)) *
        (1+Real.log n) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hforce (by positivity))
          (by linarith [hS.2]) hS.1.le
        positivity
      _ = _ := by rw [pow_add]; ring
  have hident : (1217*C₁)*(1/(2434*C₁)) = (1/2 : ℝ) := by
    field_simp
    ring
  have hexp : (n : ℝ)^a*(n : ℝ)^(-2*a) = (n : ℝ)^(-a) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  refine ⟨Real.rpow_pos_of_pos hn0 _,hδ,hS.1,hS.2,hsmall,?_⟩
  calc
    _ ≤ 1217*C₁*(1+Real.log n)^(J+2)*(n : ℝ)^(-2*a) := hm
    _ ≤ 1217*C₁*(1/(2434*C₁)*(n : ℝ)^a)*(n : ℝ)^(-2*a) := by
      gcongr
    _ = (n : ℝ)^(-a)/2 := by
      rw [← mul_assoc (1217*C₁),hident,mul_assoc,hexp]
      ring
end SharpTerminalLeave

end

end OAI
