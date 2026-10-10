import Mathlib
import OAI.Combinatorics.KMedian.Hardness.Partition

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage.Partitions
open Finset

theorem pow_tangent (t : ℝ) (ht : 0 < t) (D q : ℕ) :
    t^D + ((q:ℝ)-D)*(t^D*Real.log t) ≤ t^q := by
  have h := mul_le_mul_of_nonneg_right
    (Real.add_one_le_exp (((q:ℝ)-D)*Real.log t)) (pow_nonneg ht.le D)
  have he : Real.exp (((q:ℝ)-D)*Real.log t)*t^D = t^q := by
    calc
      _ = Real.exp (((q:ℝ)-D)*Real.log t) * Real.exp ((D:ℝ)*Real.log t) := by
        rw [Real.exp_nat_mul,Real.exp_log ht]
      _ = Real.exp ((q:ℝ)*Real.log t) := by rw [← Real.exp_add]; congr 1; ring
      _ = _ := by rw [Real.exp_nat_mul,Real.exp_log ht]
  rw [he] at h
  nlinarith

theorem sum_pow_ge {V : Type} [Fintype V] (q : V → ℕ) (D : ℕ)
    (hq : ∑ v, q v ≤ D*Fintype.card V)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (Fintype.card V:ℝ)*t^D ≤ ∑ v, t^(q v) := by
  have hc : t^D*Real.log t ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ht.le D) (Real.log_nonpos ht.le ht1)
  have hqr : (∑ v, (q v:ℝ)) - (Fintype.card V:ℝ)*D ≤ 0 := by
    have h := (show (∑ v, (q v:ℝ)) ≤ (D:ℝ)*Fintype.card V by exact_mod_cast hq)
    nlinarith
  have hprod := mul_nonneg_of_nonpos_of_nonpos hqr hc
  have hsum := Finset.sum_le_sum (s := (univ : Finset V))
    (fun v _ => pow_tangent t ht D (q v))
  have he : (∑ v, (t^D+((q v:ℝ)-D)*(t^D*Real.log t))) =
      (Fintype.card V:ℝ)*t^D+
        ((∑ v, (q v:ℝ))-(Fintype.card V:ℝ)*D)*(t^D*Real.log t) := by
    rw [sum_add_distrib, ← sum_mul, sum_sub_distrib]
    simp only [sum_const, card_univ, nsmul_eq_mul]
  rw [he] at hsum
  linarith

theorem total_hit_bound {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    [DecidableEq V] [DecidableEq A] [DecidableEq B]
    (H : V → A → Finset B) (bad : Finset V)
    (hB : 1 < Fintype.card B)
    (hgood : ∀ v, v ∉ bad → ∀ a, (H v a).card ≤ 1)
    (hbudget : ∑ v, (active (H v)).card ≤ Fintype.card B * Fintype.card V) :
    (∑ v, ((hit (H v)).card:ℝ)) ≤
      (Fintype.card B:ℝ)^Fintype.card A *
        ((Fintype.card V:ℝ)*(1-(1-1/(Fintype.card B:ℝ))^Fintype.card B)+bad.card) := by
  let t : ℝ := 1-1/(Fintype.card B:ℝ)
  let M : ℝ := (Fintype.card B:ℝ)^Fintype.card A
  have hB1 : (1:ℝ) < Fintype.card B := by exact_mod_cast hB
  have hB0 : (0:ℝ) < Fintype.card B := by linarith
  have ht : 0 < t := by
    dsimp [t]
    exact sub_pos.mpr ((div_lt_one hB0).mpr hB1)
  have ht1 : t ≤ 1 := by dsimp [t]; have := one_div_nonneg.mpr hB0.le; linarith
  have hM : 0 ≤ M := pow_nonneg hB0.le _
  have hpoint (v : V) : ((hit (H v)).card:ℝ) ≤
      M*(1-t^(active (H v)).card)+(if v ∈ bad then M else 0) := by
    by_cases hv : v ∈ bad
    · rw [ite_eq_left hv]
      have hh : ((hit (H v)).card:ℝ) ≤ M := by
        have hcard := Finset.card_le_univ (hit (H v))
        rw [Fintype.card_fun] at hcard
        dsimp [M]
        exact_mod_cast hcard
      have hp : 0 ≤ M*(1-t^(active (H v)).card) :=
        mul_nonneg hM (sub_nonneg.mpr (pow_le_one₀ ht.le ht1))
      linarith
    · rw [ite_eq_right hv,add_zero]
      exact le_of_eq (functional_hit_real (H v) (by omega) (hgood v hv))
  have hsum := Finset.sum_le_sum (s := (univ : Finset V)) (fun v _ => hpoint v)
  have he : (∑ v, (M*(1-t^(active (H v)).card)+(if v ∈ bad then M else 0))) =
      M*((Fintype.card V:ℝ)-∑ v, t^(active (H v)).card)+(bad.card:ℝ)*M := by
    rw [sum_add_distrib,← mul_sum]
    simp only [sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,mul_one,
      Finset.sum_ite_mem_eq,Finset.sum_const]
  rw [he] at hsum
  have hpow := sum_pow_ge (fun v => (active (H v)).card) (Fintype.card B) hbudget ht ht1
  have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_left hpow (Fintype.card V:ℝ)) hM
  change (∑ v, ((hit (H v)).card:ℝ)) ≤ M*((Fintype.card V:ℝ)*(1-t^Fintype.card B)+bad.card)
  nlinarith

end MetricKMedian.Coverage.Partitions

end Inline_PCPInherited

end OAI
