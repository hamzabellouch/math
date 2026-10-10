import OAI.InformationTheory.QuantumCircuit.Degree

namespace OAI

/-! Finite Pauli expansions and spectral identities in product bases. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace QAC

structure LocalExpansionTerm (N : ℕ) where
  coeff : ℂ
  gates : LocalLayer N
  support : Finset (Fin N)
  outside : ∀ i ∉ support, gates i = 1

def LocalExpansionTerm.value {N : ℕ} (t : LocalExpansionTerm N) : Operator N :=
  t.coeff • localMatrix t.gates

def PublishedPauliExpansion : Prop :=
  ∀ (N ell : ℕ), 1 ≤ N → ∀ (E : Operator N), HasDegreeLE E (ell : ℝ) →
    ∃ terms : List (LocalExpansionTerm N),
      E = (terms.map LocalExpansionTerm.value).sum ∧
      (∀ t ∈ terms, t.support.card ≤ ell) ∧
      (terms.map (fun t => ‖t.coeff‖)).sum ≤
        ((ell + 1 : ℕ) : ℝ) * (3 * N : ℝ) ^ ell * ‖E‖

structure PublishedProductSpectralResolution : Prop where
  restriction : ∀ {N : ℕ} (M : Count N) (J : Finset (Fin N)) (r : ℝ),
    (M.restrict J).high r = ∑ F ∈ M.support.powerset,
      if r ≤ ((F ∩ J).card : ℝ) then M.pattern F else 0
  pythagoras : ∀ {N : ℕ} {ι : Type} (s : Finset ι) (P : ι → Operator N)
      (ψ : State N),
    (∀ i ∈ s, IsStarProjection (P i)) →
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → P i * P j = 0) →
    ‖act (∑ i ∈ s, P i) ψ‖ ^ 2 = ∑ i ∈ s, ‖act (P i) ψ‖ ^ 2

  restriction_moment : ∀ {N : ℕ} (M : Count N) (J : Finset (Fin N)) (ψ : State N),
    (∑ F ∈ (M.restrict J).support.powerset,
      (F.card : ℝ) * ‖act ((M.restrict J).pattern F) ψ‖^2) =
    ∑ F ∈ M.support.powerset,
      ((F ∩ J).card : ℝ) * ‖act (M.pattern F) ψ‖^2

end QAC

end

end OAI
