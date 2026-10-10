import OAI.NumberTheory.Ostmann.Construction.ExpandedScheduleWeight
import OAI.NumberTheory.Ostmann.Construction.WordTransferPairBound
import OAI.NumberTheory.Ostmann.Construction.OriginalHarmonicPair

namespace OAI

/-! # The constructed prime-word coefficient under the original product law -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- Unused internal coordinates start at one; each is overwritten before use. -/
def expandedPrimeValues {V : Type*} (n : ℕ) (x : V → ℤ) : ExpandedScheduledVariable V n → ℤ
  | .inl v => x v
  | .inr _ => 1

theorem expandedPrimeValues_update {V : Type*} [DecidableEq V]
    (n : ℕ) (x : V → ℤ) (v : V) (z : ℤ) :
    expandedPrimeValues n (Function.update x v z) =
      Function.update (expandedPrimeValues n x) (.inl v) z := by
  funext i
  cases i with
  | inl w =>
    by_cases hw : w = v <;> simp [expandedPrimeValues, hw]
  | inr w => simp [expandedPrimeValues]

noncomputable def wordCoordinateUpdate {σ : Type*} (x : σ → ℤ) (v : σ) (z : ℤ) : σ → ℤ :=
  Function.update x v z

theorem expandedPrimeValues_twoCoordinate {V : Type*} (a b : V) (hab : a ≠ b)
    (n : ℕ) (outside : OtherVertices a b → ℕ) (q p : ℕ) :
    expandedPrimeValues n
      (fun i => ((twoCoordinateAssignment a b hab outside q p i : ℕ) : ℤ)) =
      wordCoordinateUpdate (expandedPrimeValues n
        (twoCoordinateAssignment a b hab (fun i => (outside i : ℤ)) q 0)) (.inl b) p := by
  rw [twoCoordinateAssignment_map,
    ← twoCoordinateAssignment_update_long a b hab (fun i => (outside i : ℤ)) q 0 p]
  rw [expandedPrimeValues_update]
  funext i
  by_cases hi : i = Sum.inl b <;> simp only [wordCoordinateUpdate, Function.update_apply, hi, ite_true, ite_false]

theorem finiteEdgeWeight_twoCoordinate_reindex {V : Type*} [Fintype V]
    (a b : V) (hab : a ≠ b)
    (χ : V → ∀ p : ℕ, DirichletCharacter ℂ p) (graph : V → V → ℤ)
    (unary : V → ℕ → ℂ) (outside : OtherVertices a b → ℕ) (q p : ℕ) :
    finiteEdgeWeight (dirichletGraphEdge χ graph) unary
        (twoCoordinateAssignment a b hab outside q p) =
      finiteEdgeWeight
        (dirichletGraphEdge (fun i => χ (twoVertexEquiv a b hab i))
          (fun i j => graph (twoVertexEquiv a b hab i) (twoVertexEquiv a b hab j)))
        (fun i => unary (twoVertexEquiv a b hab i)) (twoVertexLabels outside q p) := by
  rw [finiteEdgeWeight_two_vertices]
  congr 1
  funext i
  unfold twoCoordinateAssignment
  cases (twoVertexEquiv a b hab).symm i with
  | inl v => cases v <;> rfl
  | inr v => rfl

noncomputable def wordTransferPairBound {σ : Type*} {n : ℕ}
    (template template' : WordTransferTemplate σ n) (t t' : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (hn' : NonzeroInternalFrequencies n t')
    (B : ℕ) (f f' : WordFourierParameters n) (A E : ℕ)
    (P Q : Finset ℕ) (b : ℝ) (Bq : ℕ) : ℝ :=
  let M := wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B
  let R := (3 * 2 ^ n + 3 * (2 ^ n - 1)) * B ^ (n + 1)
  let C := f.budget template t hn * f'.budget template' t' hn'
  ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
    (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (2 * C ^ 2) +
      (M : ℝ) * ((3 ^ (2 * (R + R)) : ℕ) * (2 * (A : ℝ)⁻¹ * C ^ 2)) * (Bq : ℝ) ^ 2)

theorem selected_expanded_word_pair_bound {V : Type*} [Fintype V]
    (a b : V) (hab : a ≠ b) {n : ℕ}
    (template template' : WordTransferTemplate (ExpandedScheduledVariable V n) n)
    (t t' : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (hn' : NonzeroInternalFrequencies n t')
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (hz : ∀ s ∈ allFrequencyList n t, s ≠ 0) (hz' : ∀ s ∈ allFrequencyList n t', s ≠ 0)
    (f f' : WordFourierParameters n)
    (χ : V → ∀ p : ℕ, DirichletCharacter ℂ p) (graph : V → V → ℤ)
    (unary : V → ℕ → ℂ) (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph a a = 0 ∧ graph b b = 0) (hreverse : graph b a = 0)
    (P Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hnonprincipal : ∀ q ∈ Q, χ a q ^ graph a b ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (hsmall : ∀ q ∈ Q, ∀ s ∈ allFrequencyList n t, s.natAbs < q)
    (hsmall' : ∀ q ∈ Q, ∀ s ∈ allFrequencyList n t', s.natAbs < q)
    (hlow : ∀ p ∈ P, 2 * A ≤ p) (hhigh : ∀ p ∈ P, p ≤ E)
    (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q, lower ≤ (q : ℝ))
    (hPmass : 0 < ∑ p ∈ P, (p : ℝ)⁻¹) (hQmass : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹)
    (Bq : ℕ) (hBq : ∀ q : Q, (q : ℕ) ≤ Bq) (outside : OtherVertices a b → ℕ) :
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) *
      ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) *
        (let x := twoCoordinateAssignment a b hab outside (q : ℕ) (p : ℕ)
         finiteEdgeWeight (dirichletGraphEdge χ graph) unary x *
           (f.coefficient template t hn (expandedPrimeValues n (fun i => (x i : ℤ))) *
             conj (f'.coefficient template' t' hn' (expandedPrimeValues n (fun i => (x i : ℤ))))))‖ ^ 2 ≤
      wordTransferPairBound template template' t t' hn hn' B f f' A E P Q lower Bq := by
  let e := twoVertexEquiv a b hab
  let fixed (q : Q) := expandedPrimeValues n
    (twoCoordinateAssignment a b hab (fun i => (outside i : ℤ)) (q : ℕ) 0)
  have hh := wordTransfer_pair_dyadic_bound template template' t t' hn hn' B hB hwords hwords'
    hz hz' f f' (fun i => χ (e i)) (fun i j => graph (e i) (e j))
    (fun i => unary (e i)) outside (fun i x => hunary (e i) x) hself hreverse
    P Q hprime hnonprincipal A E hA hMA hsmall hsmall' hlow hhigh lower hlower hlowerQ
    hPmass hQmass fixed (.inl b) Bq hBq
  simp_rw [finiteEdgeWeight_twoCoordinate_reindex a b hab,
    expandedPrimeValues_twoCoordinate a b hab n]
  exact hh

/-- Every remaining coordinate keeps its own original harmonic prior.
Only the displayed numerical estimate remains to be specialized. -/
theorem expanded_word_pair_original_bound {V : Type*} [Fintype V]
    (a b : V) (hab : a ≠ b) {n : ℕ}
    (template template' : WordTransferTemplate (ExpandedScheduledVariable V n) n)
    (t t' : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (hn' : NonzeroInternalFrequencies n t')
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (hz : ∀ s ∈ allFrequencyList n t, s ≠ 0) (hz' : ∀ s ∈ allFrequencyList n t', s ≠ 0)
    (f f' : WordFourierParameters n)
    (χ : V → ∀ p : ℕ, DirichletCharacter ℂ p) (graph : V → V → ℤ)
    (unary : V → ℕ → ℂ) (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph a a = 0 ∧ graph b b = 0) (hreverse : graph b a = 0)
    (P : Finset ℕ) (Q : V → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hprime : ∀ q ∈ Q a, q.Prime)
    (hnonprincipal : ∀ q ∈ Q a, χ a q ^ graph a b ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (hsmall : ∀ q ∈ Q a, ∀ s ∈ allFrequencyList n t, s.natAbs < q)
    (hsmall' : ∀ q ∈ Q a, ∀ s ∈ allFrequencyList n t', s.natAbs < q)
    (hlow : ∀ p ∈ Q b, 2 * A ≤ p) (hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : wordTransferPairBound template template' t t' hn hn' B f f' A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
    ‖∑ x : V → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      (finiteEdgeWeight (dirichletGraphEdge χ graph) unary (fun i => (x i : ℕ)) *
        (f.coefficient template t hn (expandedPrimeValues n (fun i => (x i : ℤ))) *
          conj (f'.coefficient template' t' hn' (expandedPrimeValues n (fun i => (x i : ℤ))))))‖ ≤ δ := by
  apply original_harmonic_pair_bound a b hab P Q hQP (fun i => (hQmass i).ne')
    (fun x => finiteEdgeWeight (dirichletGraphEdge χ graph) unary x *
      (f.coefficient template t hn (expandedPrimeValues n (fun i => (x i : ℤ))) *
        conj (f'.coefficient template' t' hn' (expandedPrimeValues n (fun i => (x i : ℤ)))))) δ hδ
  intro outside
  have hs := selected_expanded_word_pair_bound a b hab template template' t t' hn hn' B hB
    hwords hwords' hz hz' f f' χ graph unary hunary hself hreverse (Q b) (Q a) hprime
    hnonprincipal A E hA hMA hsmall hsmall' hlow hhigh lower hlower hlowerQ
    (hQmass b) (hQmass a) Bq hBq (fun i => (outside i : ℕ))
  exact (sq_le_sq₀ (norm_nonneg _) hδ).mp (hs.trans hnum)

end Ostmann

end OAI
