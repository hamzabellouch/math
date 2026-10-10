import OAI.Analysis.TriangularHilbert.StrongLayer

namespace OAI

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

lemma truncated_average_lower (D : Finset ℤ) (f : ℤ → ℝ) (r : ℤ → ℕ) (n : ℤ)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hav : ρ*(2*(r n:ℝ)+1) ≤ ∑ m ∈ D ∩ intInterval n (r n), f m) :
    (ρ/2)*(2*(r n:ℝ)+1) ≤
      ∑ m ∈ D ∩ intInterval n (r n), if ρ < 2*f m then f m else 0 := by
  classical
  have he (m : ℤ) : f m ≤ (if ρ < 2*f m then f m else 0) + ρ/2 := by
    split_ifs <;> linarith
  have hsum := Finset.sum_le_sum (fun m (_ : m ∈ D ∩ intInterval n (r n)) => he m)
  have hc : ((D ∩ intInterval n (r n)).card:ℝ) ≤ 2*(r n:ℝ)+1 := by
    have ht := Finset.card_le_card (Finset.inter_subset_right : D ∩ intInterval n (r n) ⊆ intInterval n (r n))
    rw [card_intInterval] at ht
    exact_mod_cast ht
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hsum
  have hp := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ ρ/2)
  linarith

lemma int_intervals_strong (D s : Finset ℤ) (f g : ℤ → ℝ)
    (hf : ∀ m ∈ D, 0 ≤ f m) (hg : ∀ n ∈ s, 0 ≤ g n) (r : ℤ → ℕ)
    (hav : ∀ n ∈ s, g n*(2*(r n:ℝ)+1) ≤ ∑ m ∈ D ∩ intInterval n (r n), f m) :
    (∑ n ∈ s, g n*Real.sqrt (g n)) ≤
      18*Real.sqrt 2 * ∑ m ∈ D, f m*Real.sqrt (f m) := by
  classical
  have layer_bound (t : ℝ) : (∑ n ∈ s, 3*squareLayer (g n) t) ≤
      18 * ∑ m ∈ D, f m * oneLayer (2*f m) t := by
    by_cases ht : 0 < t
    · let u := s.filter (fun n => t^2 < g n)
      let f' := fun m => if t^2 < 2*f m then f m else 0
      have hw := int_intervals_weak D u f'
        (fun m hm => by unfold f'; split_ifs; exact hf m hm; exact le_rfl) r (by positivity : 0 ≤ t^2/2)
        (fun n hn => truncated_average_lower D f r n (sq_nonneg t)
          ((mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hn).2.le (by positivity)).trans
            (hav n (Finset.mem_filter.mp hn).1)))
      have hl : (∑ n ∈ s, 3*squareLayer (g n) t) = 3*t^2*(u.card:ℝ) := by
        simp only [squareLayer,Set.indicator_apply,layer_iff ht,mul_ite,mul_zero]
        rw [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const]
        simp only [u,nsmul_eq_mul]
        ring
      have hr : (∑ m ∈ D, f m*oneLayer (2*f m) t) = ∑ m ∈ D, f' m := by
        apply Finset.sum_congr rfl
        intro m _
        simp only [oneLayer,Set.indicator_apply,layer_iff ht,f']
        split_ifs <;> simp
      rw [hl,hr]
      linarith
    · have he (a : ℝ) : squareLayer a t = 0 ∧ oneLayer a t = 0 := by
        simp [squareLayer,oneLayer,Set.indicator_of_notMem,ht]
      simp only [(he _).1,(he _).2,mul_zero,Finset.sum_const_zero,le_refl]
  have hL : Integrable (fun t => ∑ n ∈ s, 3*squareLayer (g n) t) :=
    integrable_finsetSum _ (fun n _ => (squareLayer_integrable (g n)).const_mul 3)
  have hR : Integrable (fun t => 18*∑ m ∈ D, f m*oneLayer (2*f m) t) :=
    (integrable_finsetSum _ (fun m _ => (oneLayer_integrable (2*f m)).const_mul (f m))).const_mul 18
  have hi := integral_mono hL hR layer_bound
  rw [integral_finsetSum _ (fun n _ => (squareLayer_integrable (g n)).const_mul 3),
    integral_const_mul,integral_finsetSum _ (fun m _ => (oneLayer_integrable (2*f m)).const_mul (f m))] at hi
  have hl : (∑ n ∈ s, ∫ t, 3*squareLayer (g n) t) = ∑ n ∈ s, g n*Real.sqrt (g n) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [integral_const_mul,integral_squareLayer (hg n hn)]
    ring
  have hr : (∑ m ∈ D, ∫ t, f m*oneLayer (2*f m) t) =
      Real.sqrt 2 * ∑ m ∈ D, f m*Real.sqrt (f m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [integral_const_mul,integral_oneLayer,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    ring
  rw [hl,hr] at hi
  simpa only [mul_assoc] using hi
end
end TriangularHilbert
end

end OAI
