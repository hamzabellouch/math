import OAI.NumberTheory.Ostmann.Characters.LogCutoffPolynomial
import OAI.NumberTheory.Ostmann.Arithmetic.MovingGiantArchimedean

namespace OAI

/-! # All actual logarithmic node cutoffs as polynomial factors -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def MovingSlotData.nodeCutoffPolynomials {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → Polynomial ℝ → Polynomial ℝ → List (ℕ × Polynomial ℝ)
  | _, .leaf _ _, _, _ => []
  | n + 1, .node s CL CR u left right, L, R =>
      let P := (MovingSlotData.step s CL CR u left right false).pivotPolynomial value L R
      (n + 1, P) :: (left.nodeCutoffPolynomials value P L ++ right.nodeCutoffPolynomials value P R)

noncomputable def movingRealNodeCutoff {σ : Type*} (value : σ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ) :
    {n : ℕ} → MovingSlotData σ n → ℝ → ℝ → ℂ
  | _, .leaf _ _, _, _ => 1
  | n + 1, .node s CL CR u left right, L, R =>
      let p := (MovingSlotData.step s CL CR u left right false).realPivot value L R
      (positiveLogCutoff φ (G (n + 1)) p : ℂ) *
        movingRealNodeCutoff value φ G left p L * movingRealNodeCutoff value φ G right p R

theorem MovingSlotData.nodeCutoffPolynomials_length {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) :
    (T.nodeCutoffPolynomials value L R).length = 2 ^ n - 1 := by
  induction T generalizing L R with
  | leaf => rfl
  | @node n s CL CR u left right ihL ihR =>
    simp only [nodeCutoffPolynomials, List.length_cons, List.length_append, ihL, ihR, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

theorem MovingSlotData.nodeCutoffPolynomials_degree {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (d : ℕ)
    (hL : L.natDegree ≤ d) (hR : R.natDegree ≤ d) :
    ∀ f ∈ T.nodeCutoffPolynomials value L R, f.2.natDegree ≤ d := by
  induction T generalizing L R with
  | leaf => simp [nodeCutoffPolynomials]
  | node s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).pivotPolynomial_degree value L R d hL hR
    intro f hf
    rcases List.mem_cons.mp hf with h | h
    · subst f; exact hp
    · exact (List.mem_append.mp h).elim (ihL _ _ hp hL f) (ihR _ _ hp hR f)

theorem MovingSlotData.nodeCutoffPolynomials_value {σ : Type*} (value : σ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (z : ℝ) :
    ((T.nodeCutoffPolynomials value L R).map
      (fun f => (positiveLogCutoff φ (G f.1) (f.2.eval z) : ℂ))).prod =
      movingRealNodeCutoff value φ G T (L.eval z) (R.eval z) := by
  induction T generalizing L R with
  | leaf => rfl
  | node s CL CR u left right ihL ihR =>
    simp only [nodeCutoffPolynomials, List.map_cons, List.map_append, List.prod_cons,
      List.prod_append, ihL, ihR, MovingSlotReversal.pivotPolynomial_eval, movingRealNodeCutoff]
    ring

noncomputable def movingNodeCutoffFactors {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    Fin (T.nodeCutoffPolynomials value L R).length → ClippedPolynomialFactor := fun i =>
  let f := (T.nodeCutoffPolynomials value L R)[i]
  logCutoffPolynomialFactor f.2 φ (G f.1) B D hB hD hφ hlip

theorem movingNodeCutoffFactors_value {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (z : ℝ) :
    smoothPolynomialWeight (movingNodeCutoffFactors value T L R φ G B D hB hD hφ hlip) z =
      movingRealNodeCutoff value φ G T (L.eval z) (R.eval z) := by
  unfold smoothPolynomialWeight
  simp only [movingNodeCutoffFactors, logCutoffPolynomialFactor_value _ _ _ _ _ _ _ hφ hlip hout]
  rw [← T.nodeCutoffPolynomials_value value φ G L R z]
  exact (Fin.prod_ofFn _).symm.trans (congrArg List.prod
    (List.ofFn_getElem_eq_map (T.nodeCutoffPolynomials value L R)
      (fun f => (positiveLogCutoff φ (G f.1) (f.2.eval z) : ℂ))))

theorem movingNodeCutoffFactors_budget {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    smoothPolynomialBudget (movingNodeCutoffFactors value T L R φ G B D hB hD hφ hlip) =
      (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1) := by
  unfold smoothPolynomialBudget
  simp only [movingNodeCutoffFactors, logCutoffPolynomialFactor_budget, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, T.nodeCutoffPolynomials_length]

/-- With either top giant fixed, all node cutoff polynomials are affine.
Thus their derivatives have no roots and need no additional partition cuts. -/
theorem movingNodeCutoffFactors_no_derivative_roots {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ)
    (hL : L.natDegree ≤ 1) (hR : R.natDegree ≤ 1) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (i : Fin (T.nodeCutoffPolynomials value L R).length) :
    ((movingNodeCutoffFactors value T L R φ G B D hB hD hφ hlip i).polynomial.derivative).roots = 0 := by
  have hp := T.nodeCutoffPolynomials_degree value L R 1 hL hR _ (List.getElem_mem i.isLt)
  change (T.nodeCutoffPolynomials value L R)[i].2.natDegree ≤ 1 at hp
  have hd := Polynomial.natDegree_derivative_le (T.nodeCutoffPolynomials value L R)[i].2
  have hc := Polynomial.card_roots' ((T.nodeCutoffPolynomials value L R)[i].2.derivative)
  apply Multiset.card_eq_zero.mp
  change ((T.nodeCutoffPolynomials value L R)[i].2.derivative).roots.card = 0
  omega

end Ostmann

end OAI
