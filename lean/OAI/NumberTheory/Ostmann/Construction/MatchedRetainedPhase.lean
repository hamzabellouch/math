import OAI.NumberTheory.Ostmann.Construction.RetainedGroupedPhase
import OAI.NumberTheory.Ostmann.Construction.MatchedDirectedPhase

namespace OAI

/-! # Exact diagonal phase quotients with a fixed external pivot -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

def retainedInternalGraph {I : Type*} (b : Option I → Option I → ℤ) (i j : I) : ℤ :=
  b (some i) (some j)

noncomputable def externalPivotUnary {I : Type*}
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option I → Option I → ℤ) (ν : I → ℕ → ℂ) (M : ℕ)
    (i : I) (p : ℕ) : ℂ :=
  ν i p * χ i p (M : ZMod p) ^ b (some i) none

noncomputable def externalPivotCenter (M : ℕ) (t : ∀ p : ℕ, ZMod p) (p : ℕ) : ZMod p :=
  (M : ZMod p)⁻¹ * t p

theorem externalPivotUnary_norm_le_one {I : Type*}
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option I → Option I → ℤ) (ν : I → ℕ → ℂ) (M : ℕ)
    (hν : ∀ i p, ‖ν i p‖ ≤ 1) (i : I) (p : ℕ) :
    ‖externalPivotUnary χ b ν M i p‖ ≤ 1 := by
  rw [externalPivotUnary, norm_mul]
  exact (mul_le_mul (hν i p) (character_zpow_norm_le_one _ _ _)
    (norm_nonneg _) (by norm_num)).trans (by norm_num)

/-- At a fixed external pivot, both the translating center and the extra
incoming character power depend only on the actual prime. -/
theorem retainedGroupedPhase_eq_directed {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (t : ∀ p : ℕ, ZMod p) (ν : I → ℕ → ℂ)
    (b : Option I → Option I → ℤ) (M : ℕ) (v : ℤ) :
    retainedGroupedPhase p (fun i => χ i (p i)) (fun i => t (p i))
        (fun i => ν i (p i)) b M v =
      directedPrimePhase p (fun i => χ i (p i)) (fun i => externalPivotCenter M t (p i))
        (fun i => externalPivotUnary χ b ν M i (p i)) (retainedInternalGraph b) v := by
  have ha (i : I) : t (p i) * (((M * tupleCofactor p i : ℕ) : ZMod (p i))⁻¹ * (v : ZMod (p i))) =
      externalPivotCenter M t (p i) * ((tupleCofactor p i : ZMod (p i))⁻¹ * (v : ZMod (p i))) := by
    simp only [externalPivotCenter, Nat.cast_mul, mul_inv_rev]
    ring
  unfold retainedGroupedPhase directedPrimePhase
  apply Finset.prod_congr rfl
  intro i _
  rw [ha]
  simp only [retainedGraphRow, externalPivotUnary, retainedInternalGraph]
  ring

/-- The additive factors cancel on the diagonal with the external pivot
fixed. Its incoming character powers remain exactly in the unary factors. -/
theorem matched_retained_phase_quotient {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (χ : J → ∀ p : ℕ, DirichletCharacter ℂ p)
    (p : J → ℕ) [∀ j, Fact (p j).Prime] (t : ∀ p : ℕ, ZMod p)
    (ν : I → ℕ → ℂ) (ω : J → ℕ → ℂ)
    (b : Option I → Option I → ℤ) (c : Option J → Option J → ℤ) (M : ℕ) (v : ℤ)
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (hb : ∀ i, b (some i) (some i) = 0) (hcdiag : ∀ j, c (some j) (some j) = 0) :
    retainedGroupedPhase (fun i => p (e i)) (fun i => χ (e i) (p (e i)))
        (fun i => t (p (e i))) (fun i => ν i (p (e i))) b M v *
      conj (retainedGroupedPhase p (fun j => χ j (p j)) (fun j => t (p j))
        (fun j => ω j (p j)) c M v) =
      finiteEdgeWeight
        (dirichletGraphEdge χ
          (graphDifference (transportGraph e (retainedInternalGraph b)) (retainedInternalGraph c)))
        (fun j x => externalPivotUnary (fun i => χ (e i)) b ν M (e.symm j) x *
          conj (externalPivotUnary χ c ω M j x)) p := by
  rw [retainedGroupedPhase_eq_directed (fun i => p (e i)) (fun i => χ (e i)) t ν b M v,
    retainedGroupedPhase_eq_directed p χ t ω c M v]
  exact matched_directed_phase_quotient e χ p (fun j => (Fact.out : (p j).Prime).ne_zero)
    (externalPivotCenter M t) (externalPivotUnary (fun i => χ (e i)) b ν M)
    (externalPivotUnary χ c ω M) (retainedInternalGraph b) (retainedInternalGraph c) v hc hb hcdiag

end Ostmann

end OAI
