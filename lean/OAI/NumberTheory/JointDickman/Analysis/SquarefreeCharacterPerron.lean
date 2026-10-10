import OAI.NumberTheory.JointDickman.Analysis.SquarefreeCharacterFactorization
import OAI.NumberTheory.JointDickman.Analysis.SquarefreePerronAll

namespace OAI

/-! # Perron inversion for the character-weighted Riesz sum -/
namespace JointDickman
open Complex MeasureTheory Finset

noncomputable def squarefreeCharacterRieszSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z x : ℝ) : ℂ := ∑ n ∈ range (⌊x⌋₊+1),
      (squarefreeWeight z n:ℂ)*χ (n:ZMod q)*(1-(n:ℂ)/(x:ℂ))

private theorem twisted_term {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s n =
      χ (n:ZMod q)*LSeries.term (fun n => (squarefreeWeight z n:ℂ)) s n := by
  rw [←squarefreeCharacterDirichletSummand_term, ←squarefreeDirichletSummand_term]
  dsimp [squarefreeCharacterDirichletSummand]
  ring

private theorem character_perron_term_integrable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) (n : ℕ) :
    Integrable (fun t : ℝ =>
      LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q))
        ((σ:ℂ)+(t:ℂ)*I) n * Perron.f x ((σ:ℂ)+(t:ℂ)*I)) := by
  simp_rw [twisted_term, mul_assoc]
  exact (squarefree_perron_term_integrable z hx hσ n).const_mul _

theorem squarefreeCharacter_perron_interchange {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z x σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hx : 0 < x) (hσ : 1 < σ) :
    VerticalIntegral' (fun s =>
      LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s * Perron.f x s) σ =
    ∑' n : ℕ, VerticalIntegral' (fun s =>
      LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s n * Perron.f x s) σ := by
  have ha : LSeriesSummable (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) (σ:ℂ) := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ (by simpa using hσ)
    intro n _
    rw [norm_mul]
    apply (mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)).trans
    simpa only [Complex.norm_real, Real.norm_eq_abs] using squarefreeWeight_abs_le_one hz hz1 n
  have hn : Summable (fun n : ℕ => ∫ t : ℝ,
      ‖LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q))
          ((σ:ℂ)+(t:ℂ)*I) n * Perron.f x ((σ:ℂ)+(t:ℂ)*I)‖) := by
    have heq (n : ℕ) (t : ℝ) :
        ‖LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q))
          ((σ:ℂ)+(t:ℂ)*I) n * Perron.f x ((σ:ℂ)+(t:ℂ)*I)‖ =
        ‖LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) (σ:ℂ) n‖ *
          ‖Perron.f x ((σ:ℂ)+(t:ℂ)*I)‖ := by
      rw [norm_mul]
      congr 1
      simp [LSeries.norm_term_eq]
    simp_rw [heq, integral_const_mul]
    exact ha.norm.mul_right _
  have he := integral_tsum_of_summable_integral_norm
    (character_perron_term_integrable χ z hx hσ) hn
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
  rw [tsum_mul_left, tsum_mul_left, he]
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ => tsum_mul_right.symm)

theorem squarefreeCharacter_perron_term_value {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) (n : ℕ) :
    VerticalIntegral' (fun s =>
      LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s n * Perron.f x s) σ =
      if (n:ℝ) < x then (squarefreeWeight z n:ℂ)*χ (n:ZMod q)*(1-(n:ℂ)/(x:ℂ)) else 0 := by
  have hm : VerticalIntegral' (fun s =>
      LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s n * Perron.f x s) σ =
      χ (n:ZMod q)*VerticalIntegral' (fun s =>
        LSeries.term (fun n => (squarefreeWeight z n:ℂ)) s n * Perron.f x s) σ := by
    simp only [twisted_term, mul_assoc, VerticalIntegral', VerticalIntegral,
      smul_eq_mul, integral_const_mul]
    ring
  rw [hm, squarefree_perron_term_value_all z hx hσ n]
  split_ifs <;> ring

theorem squarefreeCharacter_perron_riesz {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z x σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hx : 0 < x) (hσ : 1 < σ) :
    VerticalIntegral' (fun s =>
      LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s * Perron.f x s) σ =
      squarefreeCharacterRieszSum χ z x := by
  rw [squarefreeCharacter_perron_interchange χ hz hz1 hx hσ]
  simp_rw [squarefreeCharacter_perron_term_value χ z hx hσ]
  rw [tsum_eq_sum (s := range (⌊x⌋₊+1))]
  · apply sum_congr rfl
    intro n hn
    have hnle : n ≤ ⌊x⌋₊ := by simpa only [mem_range, Nat.lt_succ_iff] using hn
    have hnreal : (n:ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hnle
    rcases hnreal.lt_or_eq with hlt | heq
    · exact ite_eq_left hlt
    · rw [heq, ite_eq_right (lt_irrefl x)]
      have heqc : (n:ℂ) = (x:ℂ) := by exact_mod_cast heq
      rw [heqc, div_self (by exact_mod_cast hx.ne'), sub_self, mul_zero]
  · intro n hn
    have hnle : ¬n ≤ ⌊x⌋₊ := by simpa only [mem_range, Nat.lt_succ_iff] using hn
    have hnreal : ¬(n:ℝ) ≤ x := by simpa only [Nat.le_floor_iff hx.le] using hnle
    exact ite_eq_right (not_lt_of_ge (le_of_lt (lt_of_not_ge hnreal)))

end JointDickman

end OAI
