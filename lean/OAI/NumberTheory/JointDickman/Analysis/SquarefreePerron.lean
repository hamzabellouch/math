import OAI.NumberTheory.JointDickman.Analysis.SquarefreeDirichletSeries
import PrimeNumberTheoremAnd.PerronFormula

namespace OAI

/-! # Absolutely convergent Perron inversion for the squarefree coefficients

The triangular Perron kernel gives an absolutely convergent representation
of the Riesz mean. Positivity permits removal of the smoothing after a
contour shift.
-/
namespace JointDickman
open Complex MeasureTheory

noncomputable def squarefreeRieszSum (z x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊x⌋₊+1), (squarefreeWeight z n:ℂ)*(1-(n:ℂ)/(x:ℂ))

theorem squarefree_perron_term (z : ℝ) {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0)
    (s : ℂ) :
    LSeries.term (fun n => (squarefreeWeight z n:ℂ)) s n * Perron.f x s =
      (squarefreeWeight z n:ℂ)*Perron.f (x/(n:ℝ)) s := by
  rw [←squarefreeDirichletSummand_term,squarefreeDirichletSummand]
  calc
    _ = (squarefreeWeight z n:ℂ)*(Perron.f x s*(n:ℂ)^(-s)) := by ring
    _ = _ := congrArg ((squarefreeWeight z n:ℂ) * ·) (by
      simpa only [Complex.ofReal_natCast] using
        (Perron.f_mul_eq_f hx (show 0 < (n:ℝ) by exact_mod_cast Nat.pos_of_ne_zero hn) s))

theorem squarefree_perron_term_integrable (z : ℝ) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ)
    (n : ℕ) :
    Integrable (fun t : ℝ => LSeries.term (fun n => (squarefreeWeight z n:ℂ))
      ((σ:ℂ)+(t:ℂ)*I) n * Perron.f x ((σ:ℂ)+(t:ℂ)*I)) := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp_rw [squarefree_perron_term z hx hn]
    exact (Perron.isIntegrable (div_pos hx (by exact_mod_cast Nat.pos_of_ne_zero hn))
      (by linarith : σ ≠ 0) (by linarith : σ ≠ -1)).const_mul _

theorem squarefree_perron_interchange {z x σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hx : 0 < x) (hσ : 1 < σ) :
    VerticalIntegral' (fun s => LSeries (fun n => (squarefreeWeight z n:ℂ)) s * Perron.f x s) σ =
      ∑' n : ℕ, VerticalIntegral' (fun s =>
        LSeries.term (fun n => (squarefreeWeight z n:ℂ)) s n * Perron.f x s) σ := by
  have hi := Perron.isIntegrable hx (by linarith : σ ≠ 0) (by linarith : σ ≠ -1)
  have ha : LSeriesSummable (fun n => (squarefreeWeight z n:ℂ)) (σ:ℂ) :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (fun n _ => by simpa only [Complex.norm_real,Real.norm_eq_abs] using squarefreeWeight_abs_le_one hz hz1 n)
      (by simpa only [Complex.ofReal_re] using hσ)
  have hn : Summable (fun n : ℕ => ∫ t : ℝ,
      ‖LSeries.term (fun n => (squarefreeWeight z n:ℂ)) ((σ:ℂ)+(t:ℂ)*I) n *
        Perron.f x ((σ:ℂ)+(t:ℂ)*I)‖) := by
    have heq (n : ℕ) (t : ℝ) :
        ‖LSeries.term (fun n => (squarefreeWeight z n:ℂ)) ((σ:ℂ)+(t:ℂ)*I) n *
          Perron.f x ((σ:ℂ)+(t:ℂ)*I)‖ =
        ‖LSeries.term (fun n => (squarefreeWeight z n:ℂ)) (σ:ℂ) n‖ *
          ‖Perron.f x ((σ:ℂ)+(t:ℂ)*I)‖ := by
      rw [norm_mul]
      congr 1
      simp [LSeries.norm_term_eq]
    simp_rw [heq]
    simp_rw [integral_const_mul]
    exact ha.norm.mul_right _
  have he := integral_tsum_of_summable_integral_norm
    (squarefree_perron_term_integrable z hx hσ) hn
  simp only [VerticalIntegral',VerticalIntegral,smul_eq_mul]
  rw [tsum_mul_left,tsum_mul_left,he]
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ => tsum_mul_right.symm)

theorem squarefree_perron_term_value (z : ℝ) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ)
    (n : ℕ) (hxn : x ≠ (n:ℝ)) :
    VerticalIntegral' (fun s =>
      LSeries.term (fun n => (squarefreeWeight z n:ℂ)) s n * Perron.f x s) σ =
      if (n:ℝ) < x then (squarefreeWeight z n:ℂ)*(1-(n:ℂ)/(x:ℂ)) else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [VerticalIntegral',VerticalIntegral]
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he : (fun s => LSeries.term (fun n => (squarefreeWeight z n:ℂ)) s n * Perron.f x s) =
      (fun s => (squarefreeWeight z n:ℂ)*Perron.f (x/(n:ℝ)) s) :=
    funext (squarefree_perron_term z hx hn)
  rw [he]
  have hc : VerticalIntegral' (fun s => (squarefreeWeight z n:ℂ)*Perron.f (x/(n:ℝ)) s) σ =
      (squarefreeWeight z n:ℂ)*VerticalIntegral' (Perron.f (x/(n:ℝ))) σ := by
    simp only [VerticalIntegral',VerticalIntegral,integral_const_mul,smul_eq_mul]
    ring
  rw [hc]
  by_cases hnx : (n:ℝ) < x
  · rw [ite_eq_left hnx,Perron.formulaGtOne ((one_lt_div hn0).mpr hnx) (by linarith : 0 < σ)]
    congr 1
    push_cast
    field_simp
  · rw [ite_eq_right hnx]
    have hlt : x < (n:ℝ) := lt_of_le_of_ne (le_of_not_gt hnx) hxn
    have hv := Perron.formulaLtOne (div_pos hx hn0) ((div_lt_one hn0).mpr hlt)
      (by linarith : 0 < σ)
    simp only [VerticalIntegral',hv,smul_zero,mul_zero]

theorem squarefree_perron_riesz {z x σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hx : 0 < x) (hσ : 1 < σ) (hxnat : ∀ n : ℕ, x ≠ (n:ℝ)) :
    VerticalIntegral' (fun s => LSeries (fun n => (squarefreeWeight z n:ℂ)) s * Perron.f x s) σ =
      squarefreeRieszSum z x := by
  rw [squarefree_perron_interchange hz hz1 hx hσ]
  simp_rw [squarefree_perron_term_value z hx hσ _ (hxnat _)]
  rw [tsum_eq_sum (s := Finset.range (⌊x⌋₊+1))]
  · apply Finset.sum_congr rfl
    intro n hn
    have hnle : n ≤ ⌊x⌋₊ := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hn
    have hnreal : (n:ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hnle
    rw [ite_eq_left (lt_of_le_of_ne hnreal (hxnat n).symm)]
  · intro n hn
    have hnle : ¬ n ≤ ⌊x⌋₊ := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hn
    have hnreal : ¬ (n:ℝ) ≤ x := by simpa only [Nat.le_floor_iff hx.le] using hnle
    exact ite_eq_right (not_lt_of_ge (le_of_lt (lt_of_not_ge hnreal)))

end JointDickman

end OAI
