import OAI.Analysis.KadisonKastler.StateBicentralizerClosure
import OAI.Analysis.FactorGeneration.Bicommutant

namespace OAI

/-! # The faithful state bicentralizer as a concrete von Neumann algebra

The double commutant theorem supplies reference-vector approximations.
The state estimate then retains bicentralizer membership, without an
operator-norm bound on those approximations.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def concreteStateBicentralizer (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  (stateBicentralizerAlgebra ξ hsep).map M.toStarSubalgebra.subtype

theorem mem_concreteStateBicentralizer (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M) :
    a.val ∈ concreteStateBicentralizer ξ hsep ↔ stateBicentralizerMember ξ a := by
  constructor
  · intro ha
    obtain ⟨b,hb,hba⟩ := StarSubalgebra.mem_map.mp ha
    have he : b=a := Subtype.ext hba
    exact he ▸ hb
  · intro ha
    exact StarSubalgebra.mem_map.mpr ⟨a,ha,rfl⟩

theorem concreteStateBicentralizer_le (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) :
    concreteStateBicentralizer ξ hsep ≤ M.toStarSubalgebra := by
  intro a ha
  obtain ⟨b,_,rfl⟩ := StarSubalgebra.mem_map.mp ha
  exact b.property

theorem concreteStateBicentralizer_bicommutant (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) :
    Set.centralizer (Set.centralizer
      (concreteStateBicentralizer ξ hsep : Set (H →L[ℂ] H)))=
        concreteStateBicentralizer ξ hsep := by
  classical
  apply Set.Subset.antisymm
  · intro T hT
    have hTM : T ∈ M := by
      rw [← SetLike.mem_coe,← M.centralizer_centralizer]
      intro R hR
      exact hT R (fun a ha => hR a (concreteStateBicentralizer_le ξ hsep ha))
    let a : Algebra M := ⟨T,hTM⟩
    apply (mem_concreteStateBicentralizer ξ hsep a).mpr
    apply stateBicentralizerMember_of_reference_approximation ξ hsep a
    intro ε hε
    obtain ⟨b,hb⟩ := bicommutant_finite_strong_approximation
      (concreteStateBicentralizer ξ hsep) T hT {ξ} ε hε
    obtain ⟨c,hc,hcb⟩ := StarSubalgebra.mem_map.mp b.property
    refine ⟨c,hc,?_⟩
    have h := hb ξ (Finset.mem_singleton_self ξ)
    change ‖T ξ-c.val ξ‖ < ε
    change c.val=b.val at hcb
    rwa [hcb]
  · intro T hT R hR
    exact (hR T hT).symm

def stateBicentralizerVonNeumann (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) : VonNeumannAlgebra H where
  toStarSubalgebra := concreteStateBicentralizer ξ hsep
  centralizer_centralizer' := concreteStateBicentralizer_bicommutant ξ hsep

theorem mem_stateBicentralizerVonNeumann (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M) :
    a.val ∈ stateBicentralizerVonNeumann ξ hsep ↔ stateBicentralizerMember ξ a :=
  mem_concreteStateBicentralizer ξ hsep a

end

end KadisonKastler

end OAI
