import OAI.GroupTheory.PolycyclicRecognition.Algebra.HigherExteriorFiniteRank

namespace OAI

/-! # The exterior-rank argument over an arbitrary infinite field -/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra
variable {K Q M : Type} [Field K] [Infinite K] [CommGroup Q] [Group.FG Q]
  [AddCommGroup M] [Module K M]

theorem no_free_orbit_of_finite_higher_exterior_infinite (ρ : Representation K Q M)
    (hext : ∀ n : ℕ, Module.Finite K[Q] (higherExteriorRepresentation ρ (n + 1)).asModule)
    (g : Q) (v : M) : ¬LinearIndependent K (fun i : ℕ => (ρ g ^ i) v) := by
  intro hv
  obtain ⟨r, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType K K[Q])
  let a : Fin r → K[Q] := fun i => f (MvPolynomial.X i)
  have ha : Algebra.adjoin K (Set.range a) = ⊤ := by
    have heq : MvPolynomial.aeval a = f := by ext i; simp [a]
    rw [Algebra.adjoin_range_eq_range_aeval, heq]
    exact (AlgHom.range_eq_top f).mpr hf
  let := hext r
  let c : Fin (r + 1 + 1) → K := Infinite.natEmbedding K ∘ Fin.val
  have hc : Function.Injective c := (Infinite.natEmbedding K).injective.comp Fin.val_injective
  have hbound : r + 1 ≤ r := higherExterior_free_orbit_bound ρ a ha c hc g v hv
  omega

theorem finite_rank_of_finite_higher_exterior_infinite (ρ : Representation K Q M)
    [Module.Finite K[Q] ρ.asModule]
    (hext : ∀ n : ℕ, Module.Finite K[Q] (higherExteriorRepresentation ρ (n + 1)).asModule) :
    FiniteDimensional K M :=
  finite_representation_of_no_free_orbit ρ
    (no_free_orbit_of_finite_higher_exterior_infinite ρ hext)

end PolycyclicRecognition

end

end OAI
