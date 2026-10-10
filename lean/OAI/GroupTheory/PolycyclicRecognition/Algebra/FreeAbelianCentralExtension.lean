import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralCoordinateQuotient

namespace OAI

/-! # Lie realization of a central extension of two integral lattices

The coordinates and their bilinear multiplication law are constructed from
chosen lifts of a quotient basis; they are not supplied as a hypothesis.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G : Type*} [Group G] {d e : ℕ}

theorem freeAbelianCentralExtension_realization
    (q : G →* Multiplicative (Fin d → ℤ)) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center G)
    (ze : Multiplicative (Fin e → ℤ) ≃* q.ker) :
    ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
      IsUniformLattice Λ ∧ Nonempty (G ≃* Λ) := by
  let z : Multiplicative (Fin e → ℤ) →* G := q.ker.subtype.comp ze.toMonoidHom
  have hz : ∀ v, z v ∈ Subgroup.center G := fun v => hcentral (ze v).property
  have hqz : ∀ v, q (z v) = 1 := fun v => (ze v).property
  let a : Fin d → G := fun i =>
    (hq (Multiplicative.ofAdd (Pi.basisFun ℤ (Fin d) i))).choose
  have ha : ∀ i, q (a i) = Multiplicative.ofAdd (Pi.basisFun ℤ (Fin d) i) :=
    fun i => (hq (Multiplicative.ofAdd (Pi.basisFun ℤ (Fin d) i))).choose_spec
  have hcomm : ∀ i j, ⁅a i, a j⁆ ∈ q.ker := by
    intro i j
    change q ⁅a i, a j⁆ = 1
    rw [map_commutatorElement]
    exact (Commute.all _ _).commutator_eq
  let c : Fin d → Fin d → Fin e → ℤ := fun i j =>
    (ze.symm ⟨⁅a i, a j⁆, hcomm i j⟩).toAdd
  have hc : ∀ i j, ⁅a i, a j⁆ = z (Multiplicative.ofAdd (c i j)) := by
    intro i j
    change ⁅a i, a j⁆ = (ze (ze.symm ⟨⁅a i, a j⁆, hcomm i j⟩)).val
    rw [MulEquiv.apply_symm_apply]
  have hzinj : Function.Injective z := Subtype.val_injective.comp ze.injective
  have hzrange : z.range = q.ker := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact (ze v).property
    · intro g hg
      refine ⟨ze.symm ⟨g, hg⟩, ?_⟩
      change (ze (ze.symm ⟨g, hg⟩)).val = g
      rw [MulEquiv.apply_symm_apply]
  let E : BilinearCentralGroup (triangularBilinear c) ≃* G :=
    MulEquiv.ofBijective (centralCoordinateHom z hz a c hc)
      (centralCoordinateHom_bijective z hz a c hc q hqz ha hzinj hzrange)
  obtain ⟨S, Λ, hΛ, ⟨eΛ⟩⟩ := bilinearIntegral_solvable_realization (triangularBilinear c)
  exact ⟨S, Λ, hΛ, ⟨E.symm.trans eΛ⟩⟩

end PolycyclicRecognition

end

end OAI
