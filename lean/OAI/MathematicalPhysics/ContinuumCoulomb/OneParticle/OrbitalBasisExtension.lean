import OAI.Analysis.CoulombRadii.FormDomain.HilbertBasisContaining

namespace OAI

/-! Extending the finitely many chosen orbitals supplies Parseval for
arbitrary continuum states, including their orthogonal remainder. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem finite_orbitals_basis_extension {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SecondCountableTopology (Lp ℂ 2 μ)] {m : ℕ}
    (v : Fin m → Lp ℂ 2 μ) (hv : Orthonormal ℂ v) :
    ∃ (S : Set (Lp ℂ 2 μ)) (b : HilbertBasis S ℂ (Lp ℂ 2 μ)) (e : Fin m ↪ S),
      Countable S ∧ ∀ i, b (e i) = v i := by
  obtain ⟨S,b,hS,hb⟩ := hv.toSubtypeRange.exists_hilbertBasis_extension
  let e : Fin m ↪ S :=
    ⟨fun i => ⟨v i,hS (Set.mem_range_self i)⟩,
      fun i j hij => hv.linearIndependent.injective (congrArg Subtype.val hij)⟩
  refine ⟨S,b,e,?_,?_⟩
  · exact Coulomb.orthonormal_subtype_countable (by simpa only [hb] using b.orthonormal)
  · intro i
    exact congrFun hb (e i)

end ContinuumCoulomb

end

end OAI
