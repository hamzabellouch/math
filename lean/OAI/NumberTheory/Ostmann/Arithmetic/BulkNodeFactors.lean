import OAI.NumberTheory.Ostmann.Arithmetic.BulkNodePolynomials
import OAI.NumberTheory.Ostmann.Arithmetic.MovingNodeCutoffFactor

namespace OAI

/-! # The original node cutoffs with one free bulk coordinate -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def bulkNodeFactors {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    Fin (T.bulkNodePolynomials value i L R).length → ClippedPolynomialFactor := fun j =>
  let f := (T.bulkNodePolynomials value i L R)[j]
  logCutoffPolynomialFactor f.2 φ (G f.1) B D hB hD hφ hlip

theorem bulkNodeFactors_value {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : T.CompensationAbsent i)
    (L R : Polynomial ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (p : ℝ) :
    smoothPolynomialWeight (bulkNodeFactors value i T L R φ G B D hB hD hφ hlip) (p : ℝ) =
      realValueNodeCutoff (Function.update value i p) φ G T (L.eval (p : ℝ)) (R.eval (p : ℝ)) := by
  unfold smoothPolynomialWeight
  simp only [bulkNodeFactors, logCutoffPolynomialFactor_value _ _ _ _ _ _ _ hφ hlip hout]
  rw [← T.bulkNodePolynomials_value value i φ G hT L R p]
  exact (Fin.prod_ofFn _).symm.trans (congrArg List.prod
    (List.ofFn_getElem_eq_map (T.bulkNodePolynomials value i L R)
      (fun f => (positiveLogCutoff φ (G f.1) (f.2.eval (p : ℝ)) : ℂ))))

theorem bulkNodeFactors_budget {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    smoothPolynomialBudget (bulkNodeFactors value i T L R φ G B D hB hD hφ hlip) =
      (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1) := by
  unfold smoothPolynomialBudget
  simp only [bulkNodeFactors, logCutoffPolynomialFactor_budget, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, T.bulkNodePolynomials_length]

theorem bulkNodeFactors_degree {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (d e : ℕ) (hsize : T.SizeLE d) (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e)
    (j : Fin (T.bulkNodePolynomials value i L R).length) :
    (bulkNodeFactors value i T L R φ G B D hB hD hφ hlip j).polynomial.natDegree ≤ n * d + e :=
  T.bulkNodePolynomials_degree value i L R d e hsize hL hR _ (List.getElem_mem j.isLt)

end Ostmann

end OAI
