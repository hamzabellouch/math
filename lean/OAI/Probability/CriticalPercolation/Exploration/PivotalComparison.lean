import Mathlib

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.DFS

lemma pivotal_comparison {u v x a s : ℝ}
    (hu : 0 < u) (hv : 0 ≤ v) (ha : 0 ≤ a)
    (havoid : s*u ≤ x*a) (harris : (u+v)*(u+x) ≤ u) :
    (a+s)*(u+v) ≤ a := by
  have h1 := mul_le_mul_of_nonneg_right havoid (add_nonneg hu.le hv)
  have h2 := mul_le_mul_of_nonneg_left harris ha
  nlinarith

lemma tilted_increment {u v a b g : ℝ}
    (h0 : 0 < u+v) (h1 : 0 < u+v-b-g) (hc : u*g ≤ v*b) :
    a/(u+v-b-g) ≤ (v+a-g)/(u+v-b-g)-v/(u+v) := by
  have hid : (v+a-g)/(u+v-b-g)-v/(u+v)-a/(u+v-b-g) =
      (v*b-u*g)/((u+v)*(u+v-b-g)) := by
    field_simp
    ring
  have hn : 0 ≤ (v*b-u*g)/((u+v)*(u+v-b-g)) :=
    div_nonneg (sub_nonneg.mpr hc) (mul_pos h0 h1).le
  linarith

lemma converted_variance {p u v x a b g s : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hg : 0 ≤ g) (hs : 0 ≤ s)
    (hau : a ≤ u) (ha1 : a ≤ u+v-b-g)
    (havoid₁ : u*g ≤ v*b) (havoid₂ : s*u ≤ x*a)
    (harris : (u+v)*(u+x) ≤ u) :
    p*(1-p)*a*(a+s) ≤
      p*(1-p)*(u+v)*(u+v-b-g)/((1-p)*(u+v)+p*(u+v-b-g)) *
        ((v+a-g)/(u+v-b-g)-v/(u+v))^2 := by
  let U0 := u+v
  let U1 := u+v-b-g
  let U := (1-p)*U0+p*U1
  let r := (v+a-g)/U1-v/U0
  have hpq : 0 ≤ p*(1-p) := mul_nonneg hp.1.le (sub_nonneg.mpr hp.2.le)
  have h0 : 0 ≤ U0 := add_nonneg hu hv
  have h1 : 0 ≤ U1 := ha.trans ha1
  have hU : 0 ≤ U := add_nonneg (mul_nonneg (sub_nonneg.mpr hp.2.le) h0)
    (mul_nonneg hp.1.le h1)
  change p*(1-p)*a*(a+s) ≤ p*(1-p)*U0*U1/U*r^2
  rcases eq_or_lt_of_le ha with hz | ha
  · rw [← hz]
    simpa only [mul_zero, zero_mul] using
      mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg hpq h0) h1) hU) (sq_nonneg r)
  · have hup : 0 < u := ha.trans_le hau
    have h0p : 0 < U0 := add_pos_of_pos_of_nonneg hup hv
    have h1p : 0 < U1 := ha.trans_le ha1
    have hUp : 0 < U := add_pos
      (mul_pos (sub_pos.mpr hp.2) h0p) (mul_pos hp.1 h1p)
    have h10 : U1 ≤ U0 := by dsimp [U1,U0]; linarith
    have hU0 : U ≤ U0 := by
      dsimp [U]
      have ht := mul_le_mul_of_nonneg_left h10 hp.1.le
      nlinarith
    have hprod : U*U1 ≤ U0^2 := by
      have hh := mul_le_mul hU0 h10 h1 h0
      nlinarith
    have hcmp : (a+s)*U0 ≤ a := pivotal_comparison hup hv ha.le havoid₂ harris
    have hr : a/U1 ≤ r := tilted_increment h0p h1p havoid₁
    have hr0 : 0 ≤ r := (div_nonneg ha.le h1).trans hr
    have hsqr : (a/U1)^2 ≤ r^2 := by
      exact pow_le_pow_left₀ (div_nonneg ha.le h1) hr 2
    have hab : 0 ≤ a*(a+s) := mul_nonneg ha.le (add_nonneg ha.le hs)
    have hbase : a*(a+s) ≤ U0*a^2/(U*U1) := by
      apply (le_div_iff₀ (mul_pos hUp h1p)).mpr
      calc
        _ ≤ (a*(a+s))*U0^2 := mul_le_mul_of_nonneg_left hprod hab
        _ ≤ U0*a^2 := by
          have hh := mul_le_mul_of_nonneg_left hcmp (mul_nonneg ha.le h0)
          nlinarith
    calc
      _ = (p*(1-p))*(a*(a+s)) := by ring
      _ ≤ (p*(1-p))*(U0*a^2/(U*U1)) := mul_le_mul_of_nonneg_left hbase hpq
      _ = (p*(1-p)*U0*U1/U)*(a/U1)^2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqr
        (div_nonneg (mul_nonneg (mul_nonneg hpq h0) h1) hU)

end CriticalPercolation.DFS

end
end

end OAI
