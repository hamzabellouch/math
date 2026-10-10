import OAI.Analysis.HyperbolicCones.PolynomialBasic

namespace OAI

noncomputable section

open Polynomial
open scoped BigOperators

universe u

namespace Paper256

theorem polynomial_prod_top {ι : Type u} (s : Finset ι)
    (f : ι → Polynomial ℝ) (d : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, d i ∧
      (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    intro h
    have hfa := h a (Finset.mem_insert_self a s)
    have hs := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    refine ⟨natDegree_mul_le_of_le hfa hs.1, ?_⟩
    rw [coeff_mul_add_eq_of_natDegree_le hfa hs.1, hs.2]

theorem affine_substitution_top {σ : Type u} [Fintype σ]
    (p : MvPolynomial σ ℝ) (d : ℕ) (hp : p.IsHomogeneous d) (e x : σ → ℝ) :
    let q := MvPolynomial.eval₂ Polynomial.C
      (fun i => Polynomial.C (e i) * Polynomial.X - Polynomial.C (x i)) p
    q.natDegree ≤ d ∧ q.coeff d = MvPolynomial.eval e p := by
  classical
  let l : σ → Polynomial ℝ := fun i => C (e i) * X - C (x i)
  have hl (i : σ) : (l i).natDegree ≤ 1 := by
    apply (natDegree_sub_le _ _).trans
    exact max_le (le_trans (natDegree_C_mul_le _ _) (by simp)) (by simp)
  have hc (i : σ) : (l i).coeff 1 = e i := by simp [l]
  have hm (a : σ →₀ ℕ) :
      (∏ i, l i ^ a i).natDegree ≤ a.degree ∧
        (∏ i, l i ^ a i).coeff a.degree = ∏ i, e i ^ a i := by
    have h := polynomial_prod_top Finset.univ (fun i => l i ^ a i) a
      (fun i _ => by simpa using natDegree_pow_le_of_le (a i) (hl i))
    rw [Finsupp.degree_eq_sum]
    refine ⟨h.1, h.2.trans ?_⟩
    apply Finset.prod_congr rfl
    intro i _
    simpa [hc] using (coeff_pow_of_natDegree_le (m := a i) (hl i))
  dsimp
  change (MvPolynomial.eval₂ C l p).natDegree ≤ d ∧
    (MvPolynomial.eval₂ C l p).coeff d = MvPolynomial.eval e p
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval_eq']
  constructor
  · apply natDegree_sum_le_of_forall_le
    intro a ha
    have hd : a.degree = d := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
        hp (MvPolynomial.mem_support_iff.mp ha)
    exact (natDegree_C_mul_le _ _).trans ((hm a).1.trans_eq hd)
  · rw [finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro a ha
    have hd : a.degree = d := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
        hp (MvPolynomial.mem_support_iff.mp ha)
    rw [coeff_C_mul, ← hd, (hm a).2]

theorem linePolynomial_top (x : Ambient) :
    (linePolynomial x).natDegree ≤ 20 ∧ (linePolynomial x).coeff 20 = 1 := by
  have h := affine_substitution_top polynomial 20 polynomial_homogeneous
    (coordinates basePoint) (coordinates x)
  simpa [linePolynomial, polynomial_basePoint] using h

theorem linePolynomial_natDegree (x : Ambient) : (linePolynomial x).natDegree = 20 := by
  apply le_antisymm (linePolynomial_top x).1
  exact le_natDegree_of_ne_zero (by rw [(linePolynomial_top x).2]; norm_num)

theorem linePolynomial_monic (x : Ambient) : (linePolynomial x).Monic := by
  change (linePolynomial x).leadingCoeff = 1
  rw [← coeff_natDegree, linePolynomial_natDegree, (linePolynomial_top x).2]

end Paper256

end

end OAI
