import OAI.NumberTheory.SiegelZeros.Selection.RowReplacement
import OAI.NumberTheory.SiegelZeros.Selection.RowSpan

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.W28

open WeightedTorusJets.W18 WeightedTorusJets.W19
open scoped BigOperators

variable {K ι ρ : Type*} [Field K] [Fintype ι] [Fintype ρ]

abbrev MonomialBox (N : ℕ) := Fin 4 → Fin N

noncomputable def boxExponent {N : ℕ} (n : MonomialBox N) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (n i).val)

theorem boxExponent_injective (N : ℕ) :
    Function.Injective (boxExponent (N := N)) := by
  intro n m h
  funext i
  apply Fin.ext
  exact congrArg (fun e : Fin 4 →₀ ℕ => e i) h

noncomputable def coefficientPolynomial (e : ι → Fin 4 →₀ ℕ) (c : ι → K) :
    MvPolynomial (Fin 4) K :=
  ∑ n, MvPolynomial.monomial (e n) (c n)

theorem coefficientPolynomial_coeff (e : ι → Fin 4 →₀ ℕ)
    (he : Function.Injective e) (c : ι → K) (n : ι) :
    (coefficientPolynomial e c).coeff (e n) = c n := by
  classical
  simp [coefficientPolynomial, MvPolynomial.coeff_monomial, he.eq_iff]

theorem coefficientPolynomial_eq_zero_iff (e : ι → Fin 4 →₀ ℕ)
    (he : Function.Injective e) (c : ι → K) :
    coefficientPolynomial e c = 0 ↔ c = 0 := by
  constructor
  · intro h
    funext n
    have hc := coefficientPolynomial_coeff e he c n
    rw [h] at hc
    simpa using hc.symm
  · intro h
    subst c
    simp [coefficientPolynomial]

noncomputable def derivativeMatrix (v : Fin 3 → Fin 4 → K)
    (e : ι → Fin 4 →₀ ℕ) (a : ρ → Fin 3 → ℕ) : Matrix ρ ι K :=
  fun r n => eigenvalue (v 0) (e n) ^ a r 0 *
    eigenvalue (v 1) (e n) ^ a r 1 * eigenvalue (v 2) (e n) ^ a r 2

omit [Fintype ι] [Fintype ρ] in
theorem derivativeMatrix_eq_actual_jet (v : Fin 3 → Fin 4 → K)
    (e : ι → Fin 4 →₀ ℕ) (a : ρ → Fin 3 → ℕ) (r : ρ) (n : ι) :
    derivativeMatrix v e a r n =
      MvPolynomial.eval (fun _ => (1 : K))
        (mixedInvariant v (a r) (MvPolynomial.monomial (e n) 1)) :=
  (derivative_row_at_one v (a r) (e n)).symm

omit [Fintype ρ] in
theorem derivativeMatrix_mulVec_eq_actual_jet (v : Fin 3 → Fin 4 → K)
    (e : ι → Fin 4 →₀ ℕ) (a : ρ → Fin 3 → ℕ) (c : ι → K) (r : ρ) :
    (derivativeMatrix v e a).mulVec c r =
      MvPolynomial.eval (fun _ => (1 : K))
        (mixedInvariant v (a r) (coefficientPolynomial e c)) := by
  classical
  simp [coefficientPolynomial, mixedInvariant_sum, mixedInvariant_monomial,
    MvPolynomial.eval_monomial, Matrix.mulVec, dotProduct, derivativeMatrix]

theorem actual_jet_annihilation_iff_rowSpan (v : Fin 3 → Fin 4 → K)
    (e : ι → Fin 4 →₀ ℕ) (he : Function.Injective e) (a : ρ → Fin 3 → ℕ) :
    (∀ c : ι → K,
      (∀ r, MvPolynomial.eval (fun _ => (1 : K))
        (mixedInvariant v (a r) (coefficientPolynomial e c)) = 0) →
      coefficientPolynomial e c = 0) ↔
      Submodule.span K (Set.range (derivativeMatrix v e a).row) = ⊤ := by
  rw [← annihilation_iff_rowSpan_eq_top]
  constructor
  · intro h c hc
    apply (coefficientPolynomial_eq_zero_iff e he c).mp
    apply h c
    intro r
    rw [← derivativeMatrix_mulVec_eq_actual_jet]
    exact congrFun hc r
  · intro h c hc
    apply (coefficientPolynomial_eq_zero_iff e he c).mpr
    apply h c
    funext r
    rw [derivativeMatrix_mulVec_eq_actual_jet]
    exact hc r

theorem derivative_rows_span_of_annihilation (v : Fin 3 → Fin 4 → K)
    (e : ι → Fin 4 →₀ ℕ) (a : ρ → Fin 3 → ℕ)
    (h : ∀ c : ι → K, (derivativeMatrix v e a).mulVec c = 0 → c = 0) :
    Submodule.span K (Set.range (derivativeMatrix v e a).row) = ⊤ :=
  (annihilation_iff_rowSpan_eq_top _).mp h

end WeightedTorusJets.W28


end SiegelZeros

end OAI
