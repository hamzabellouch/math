import OAI.NumberTheory.Ostmann.Construction.HistoryCoefficientData
import OAI.NumberTheory.Ostmann.Arithmetic.ReconstructedPairGraphBound
import OAI.NumberTheory.Ostmann.Construction.OriginalHarmonicPair

namespace OAI

/-! # The explicit pair bound for global history coefficients under original priors -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def historyPairBound {V : Type*} (D D' : HistoryCoefficientData V)
    (frequencies : List ℤ) (C A E : ℕ) (P Q : Finset ℕ) (b : ℝ) (Bq : ℕ) : ℝ :=
  ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
    (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (2 * (D.budget * D'.budget) ^ 2) +
      (historyFrequencyPeriod frequencies (C ^ (D.steps.length + D'.steps.length) + 1) : ℝ) *
        ((3 ^ (2 * (D.complexity + D'.complexity)) : ℕ) *
          (2 * (A : ℝ)⁻¹ * (D.budget * D'.budget) ^ 2)) * (Bq : ℝ) ^ 2)

theorem selected_global_history_pair_bound {V : Type*} [Fintype V]
    (a b : V) (hab : a ≠ b) (D D' : HistoryCoefficientData V)
    (frequencies : List ℤ) (C : ℕ) (hC : 1 ≤ C)
    (hfreq : ∀ s ∈ frequencies, s ≠ 0)
    (hsteps : ∀ step ∈ D.steps, step.s ∈ frequencies)
    (hsteps' : ∀ step ∈ D'.steps, step.s ∈ frequencies)
    (hsize : ∀ step ∈ D.steps, step.left.length + step.right.length + 4 ≤ C)
    (hsize' : ∀ step ∈ D'.steps, step.left.length + step.right.length + 4 ≤ C)
    (hunits : ∀ i, (D.units i : ℤ) ∣ (historyFrequencyBase frequencies : ℤ))
    (hunits' : ∀ i, (D'.units i : ℤ) ∣ (historyFrequencyBase frequencies : ℤ))
    (χ : V → ∀ p : ℕ, DirichletCharacter ℂ p) (graph : V → V → ℤ)
    (unary : V → ℕ → ℂ) (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph a a = 0 ∧ graph b b = 0) (hreverse : graph b a = 0)
    (P Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hnonprincipal : ∀ q ∈ Q, χ a q ^ graph a b ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : historyFrequencyPeriod frequencies (C ^ (D.steps.length + D'.steps.length) + 1) ≤ A)
    (hsmall : ∀ q ∈ Q, ∀ s ∈ frequencies, s.natAbs < q)
    (hlow : ∀ p ∈ P, 2 * A ≤ p) (hhigh : ∀ p ∈ P, p ≤ E)
    (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q, lower ≤ (q : ℝ))
    (hPmass : 0 < ∑ p ∈ P, (p : ℝ)⁻¹) (hQmass : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹)
    (Bq : ℕ) (hBq : ∀ q : Q, (q : ℕ) ≤ Bq) (outside : OtherVertices a b → ℕ) :
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) *
      ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) *
        (let x := twoCoordinateAssignment a b hab outside (q : ℕ) (p : ℕ)
         finiteEdgeWeight (dirichletGraphEdge χ graph) unary x *
           (D.value (fun i => (x i : ℤ)) * conj (D'.value (fun i => (x i : ℤ)))))‖ ^ 2 ≤
      historyPairBound D D' frequencies C A E P Q lower Bq := by
  let e := twoVertexEquiv a b hab
  let fixed (q : Q) : V → ℤ := twoCoordinateAssignment a b hab (fun i => (outside i : ℤ)) (q : ℕ) 0
  have hx (q : Q) (p : P) :
      (fun i => ((twoCoordinateAssignment a b hab outside (q : ℕ) (p : ℕ) i : ℕ) : ℤ)) =
        Function.update (fixed q) b (p : ℕ) := by
    rw [twoCoordinateAssignment_map]
    exact (twoCoordinateAssignment_update_long a b hab
      (fun i => (outside i : ℤ)) (q : ℕ) 0 (p : ℕ)).symm
  have hgraph (q : Q) (p : P) :
      finiteEdgeWeight (dirichletGraphEdge χ graph) unary
          (twoCoordinateAssignment a b hab outside (q : ℕ) (p : ℕ)) =
        finiteEdgeWeight (dirichletGraphEdge (fun i => χ (e i)) (fun i j => graph (e i) (e j)))
          (fun i => unary (e i)) (twoVertexLabels outside q p) := by
    rw [finiteEdgeWeight_two_vertices]
    congr 1
    funext i
    unfold twoCoordinateAssignment
    cases (twoVertexEquiv a b hab).symm i with
    | inl t => cases t <;> rfl
    | inr v => rfl
  have hh := reconstructed_pair_dyadic_graph_bound D.steps D'.steps frequencies C hC hfreq
    hsteps hsteps' hsize hsize' D.units D'.units hunits hunits'
    (fun i => χ (e i)) (fun i j => graph (e i) (e j)) (fun i => unary (e i)) outside
    (fun i x => hunary (e i) x) hself hreverse P Q hprime hnonprincipal A E hA hMA hsmall
    hlow hhigh lower hlower hlowerQ hPmass hQmass fixed b
    (fun q => D.factors (fixed q) b) (fun q => D'.factors (fixed q) b)
    (fun q => D.polynomials (fixed q) b) (fun q => D'.polynomials (fixed q) b)
    (fun _ => D.keep) (fun _ => D'.keep) D.budget D'.budget D.complexity D'.complexity Bq
    D.budget_nonneg D'.budget_nonneg
    (fun q => (D.factors_budget (fixed q) b).le) (fun q => (D'.factors_budget (fixed q) b).le)
    (fun q => D.polynomials_complexity (fixed q) b) (fun q => D'.polynomials_complexity (fixed q) b) hBq
  simp_rw [hgraph, hx, D.value_local, D'.value_local]
  exact hh

/-- This is the full original-prior correlation estimate for the two
constructed coefficients. Its only remaining loss is the displayed numerical
bound, which is independent of the other sampled labels. -/
theorem global_history_pair_original_bound {V : Type*} [Fintype V]
    (a b : V) (hab : a ≠ b) (D D' : HistoryCoefficientData V)
    (frequencies : List ℤ) (C : ℕ) (hC : 1 ≤ C)
    (hfreq : ∀ s ∈ frequencies, s ≠ 0)
    (hsteps : ∀ step ∈ D.steps, step.s ∈ frequencies)
    (hsteps' : ∀ step ∈ D'.steps, step.s ∈ frequencies)
    (hsize : ∀ step ∈ D.steps, step.left.length + step.right.length + 4 ≤ C)
    (hsize' : ∀ step ∈ D'.steps, step.left.length + step.right.length + 4 ≤ C)
    (hunits : ∀ i, (D.units i : ℤ) ∣ (historyFrequencyBase frequencies : ℤ))
    (hunits' : ∀ i, (D'.units i : ℤ) ∣ (historyFrequencyBase frequencies : ℤ))
    (χ : V → ∀ p : ℕ, DirichletCharacter ℂ p) (graph : V → V → ℤ)
    (unary : V → ℕ → ℂ) (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph a a = 0 ∧ graph b b = 0) (hreverse : graph b a = 0)
    (P : Finset ℕ) (Q : V → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hprime : ∀ q ∈ Q a, q.Prime)
    (hnonprincipal : ∀ q ∈ Q a, χ a q ^ graph a b ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : historyFrequencyPeriod frequencies (C ^ (D.steps.length + D'.steps.length) + 1) ≤ A)
    (hsmall : ∀ q ∈ Q a, ∀ s ∈ frequencies, s.natAbs < q)
    (hlow : ∀ p ∈ Q b, 2 * A ≤ p) (hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : historyPairBound D D' frequencies C A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
    ‖∑ x : V → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      (finiteEdgeWeight (dirichletGraphEdge χ graph) unary (fun i => (x i : ℕ)) *
        (D.value (fun i => (x i : ℤ)) * conj (D'.value (fun i => (x i : ℤ)))))‖ ≤ δ := by
  apply original_harmonic_pair_bound a b hab P Q hQP (fun i => (hQmass i).ne')
    (fun x => finiteEdgeWeight (dirichletGraphEdge χ graph) unary x *
      (D.value (fun i => (x i : ℤ)) * conj (D'.value (fun i => (x i : ℤ))))) δ hδ
  intro outside
  have hs := selected_global_history_pair_bound a b hab D D' frequencies C hC hfreq
    hsteps hsteps' hsize hsize' hunits hunits' χ graph unary hunary hself hreverse
    (Q b) (Q a) hprime hnonprincipal A E hA hMA hsmall hlow hhigh lower hlower hlowerQ
    (hQmass b) (hQmass a) Bq hBq (fun i => (outside i : ℕ))
  exact (sq_le_sq₀ (norm_nonneg _) hδ).mp (hs.trans hnum)

end Ostmann

end OAI
