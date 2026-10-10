import OAI.NumberTheory.Ostmann.Arithmetic.BulkLeafPolynomials
import OAI.NumberTheory.Ostmann.Arithmetic.MovingCutoffPolynomials

namespace OAI

/-! # Every node cutoff in the same bulk-prime polynomial coordinate -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def MovingSlotData.bulkNodePolynomials {σ : Type*} (value : σ → ℝ) (i : σ) :
    {n : ℕ} → MovingSlotData σ n → Polynomial ℝ → Polynomial ℝ → List (ℕ × Polynomial ℝ)
  | _, .leaf _ _, _, _ => []
  | n + 1, .node s CL CR u left right, L, R =>
      let p := (MovingSlotData.step s CL CR u left right false).bulkPivotPolynomial value i L R
      (n + 1, p) :: (left.bulkNodePolynomials value i p L ++ right.bulkNodePolynomials value i p R)

theorem MovingSlotData.bulkNodePolynomials_length {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) :
    (T.bulkNodePolynomials value i L R).length = 2 ^ n - 1 := by
  induction T generalizing L R with
  | leaf => rfl
  | @node n s CL CR u left right ihL ihR =>
    simp only [bulkNodePolynomials, List.length_cons, List.length_append, ihL, ihR, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

theorem MovingSlotData.bulkNodePolynomials_degree {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (d e : ℕ)
    (hsize : T.SizeLE d) (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e) :
    ∀ f ∈ T.bulkNodePolynomials value i L R, f.2.natDegree ≤ n * d + e := by
  induction T generalizing L R e with
  | leaf => simp [bulkNodePolynomials]
  | @node n s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).bulkPivotPolynomial_degree
      value i L R d e ⟨hsize.2.1, hsize.1, hsize.2.2.1⟩ hL hR
    have hLe : L.natDegree ≤ d + e := hL.trans (Nat.le_add_left _ _)
    have hRe : R.natDegree ≤ d + e := hR.trans (Nat.le_add_left _ _)
    intro f hf
    rcases List.mem_cons.mp hf with hf | hf
    · subst f
      exact hp.trans (by rw [Nat.succ_mul]; omega)
    · have hn : n * d + (d + e) = (n + 1) * d + e := by ring
      rcases List.mem_append.mp hf with hf | hf
      · simpa only [hn] using ihL _ _ (d + e) hsize.2.2.2.1 hp hLe f hf
      · simpa only [hn] using ihR _ _ (d + e) hsize.2.2.2.2 hp hRe f hf

theorem MovingSlotData.bulkNodePolynomials_value {σ : Type*} (value : σ → ℝ) (i : σ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) {n : ℕ} (T : MovingSlotData σ n)
    (hT : T.CompensationAbsent i) (L R : Polynomial ℝ) (p : ℝ) :
    ((T.bulkNodePolynomials value i L R).map
      (fun f => (positiveLogCutoff φ (G f.1) (f.2.eval (p : ℝ)) : ℂ))).prod =
      realValueNodeCutoff (Function.update value i p) φ G T
        (L.eval (p : ℝ)) (R.eval (p : ℝ)) := by
  induction T generalizing L R with
  | leaf => rfl
  | node s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).bulkPivotPolynomial_eval
      value i hT.1 L R p
    simp only [bulkNodePolynomials, List.map_cons, List.map_append, List.prod_cons,
      List.prod_append, ihL hT.2.1, ihR hT.2.2, hp, realValueNodeCutoff]
    ring

end Ostmann

end OAI
