import OAI.NumberTheory.JointDickman.Analysis.PerronAtOne
import OAI.NumberTheory.JointDickman.Analysis.SquarefreePerronNormalization

namespace OAI

/-! # Perron inversion including integral endpoints -/
namespace JointDickman
open Complex MeasureTheory

theorem squarefree_perron_term_value_all (z : ℝ) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ)
    (n : ℕ) :
    VerticalIntegral' (fun s =>
      LSeries.term (fun n => (squarefreeWeight z n:ℂ)) s n * Perron.f x s) σ =
      if (n:ℝ) < x then (squarefreeWeight z n:ℂ)*(1-(n:ℂ)/(x:ℂ)) else 0 := by
  by_cases hxn : x ≠ (n:ℝ)
  · exact squarefree_perron_term_value z hx hσ n hxn
  have hxn : x = (n:ℝ) := not_ne_iff.mp hxn
  have hn : n ≠ 0 := by intro hn; simp [hn] at hxn; linarith
  have he : (fun s => LSeries.term (fun n => (squarefreeWeight z n:ℂ)) s n * Perron.f x s) =
      (fun s => (squarefreeWeight z n:ℂ)*Perron.f (x/(n:ℝ)) s) :=
    funext (squarefree_perron_term z hx hn)
  have hc : VerticalIntegral' (fun s => (squarefreeWeight z n:ℂ)*Perron.f (x/(n:ℝ)) s) σ =
      (squarefreeWeight z n:ℂ)*VerticalIntegral' (Perron.f (x/(n:ℝ))) σ := by
    simp only [VerticalIntegral',VerticalIntegral,integral_const_mul,smul_eq_mul]
    ring
  rw [he,hc,show x/(n:ℝ) = 1 by rw [←hxn]; exact div_self hx.ne',perron_formula_one hσ]
  simp only [mul_zero,hxn,lt_self_iff_false,ite_false]

theorem squarefree_perron_riesz_all {z x σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hx : 0 < x) (hσ : 1 < σ) :
    VerticalIntegral' (fun s => LSeries (fun n => (squarefreeWeight z n:ℂ)) s * Perron.f x s) σ =
      squarefreeRieszSum z x := by
  rw [squarefree_perron_interchange hz hz1 hx hσ]
  simp_rw [squarefree_perron_term_value_all z hx hσ]
  rw [tsum_eq_sum (s := Finset.range (⌊x⌋₊+1))]
  · apply Finset.sum_congr rfl
    intro n hn
    have hnle : n ≤ ⌊x⌋₊ := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hn
    have hnreal : (n:ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hnle
    rcases hnreal.lt_or_eq with hlt | heq
    · exact ite_eq_left hlt
    · rw [heq,ite_eq_right (lt_irrefl x)]
      have heqc : (n:ℂ) = (x:ℂ) := by exact_mod_cast heq
      rw [heqc,div_self (by exact_mod_cast hx.ne'),sub_self,mul_zero]
  · intro n hn
    have hnle : ¬ n ≤ ⌊x⌋₊ := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hn
    have hnreal : ¬ (n:ℝ) ≤ x := by simpa only [Nat.le_floor_iff hx.le] using hnle
    exact ite_eq_right (not_lt_of_ge (le_of_lt (lt_of_not_ge hnreal)))

theorem squarefreeNormalizedPerron_riesz_all {z L c : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hc : 0 < c) :
    (Real.exp L:ℂ)*VerticalIntegral' (squarefreeNormalizedPerron z L) c =
      squarefreeRieszSum z (Real.exp L) := by
  have hp := squarefree_perron_riesz_all hz hz1 (Real.exp_pos L)
    (show 1 < 1+c by linarith)
  rw [←hp]
  simp only [VerticalIntegral',VerticalIntegral,smul_eq_mul]
  have heq : (fun t : ℝ => (Real.exp L:ℂ)*squarefreeNormalizedPerron z L ((c:ℂ)+(t:ℂ)*I)) =
      (fun t : ℝ => LSeries (fun n => (squarefreeWeight z n:ℂ)) (((1+c:ℝ):ℂ)+(t:ℂ)*I) *
        Perron.f (Real.exp L) (((1+c:ℝ):ℂ)+(t:ℂ)*I)) := by
    funext t
    rw [squarefreeNormalizedPerron_eq]
    congr 2 <;> push_cast <;> ring
  rw [←heq,integral_const_mul]
  ring

end JointDickman

end OAI
