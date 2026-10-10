import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentCyclicRealization

namespace OAI

/-! # Actual nilpotent kernels with cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G] [Group.FG G]

theorem nilpotentByCyclic_finiteIndex_uniform_lattice (N : Subgroup G) [N.Normal]
    [Group.FG N] [Group.IsNilpotent N] [IsCyclic (G ⧸ N)] :
    ∃ Γ : Subgroup G, Γ.FiniteIndex ∧
      ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
        IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  cases finite_or_infinite (G ⧸ N) with
  | inl h =>
    let := h
    let : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    exact virtuallyNilpotent_uniform_lattice ⟨N, inferInstance, inferInstance⟩
  | inr h =>
    let := h
    let E : Multiplicative ℤ ≃* G ⧸ N := intCyclicMulEquiv
    let q : G →* Multiplicative ℤ := E.symm.toMonoidHom.comp (QuotientGroup.mk' N)
    have hker : q.ker = N := by
      ext g
      change E.symm (QuotientGroup.mk' N g) = 1 ↔ g ∈ N
      rw [← E.symm.map_one, E.symm.injective.eq_iff]
      exact QuotientGroup.eq_one_iff g
    let eN := MulEquiv.subgroupCongr hker
    let : Group.FG q.ker := Group.fg_of_surjective
      (f := eN.symm.toMonoidHom) eN.symm.surjective
    let : Group.IsNilpotent q.ker := (Group.isNilpotent_congr eN).mpr inferInstance
    obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective N (E (Multiplicative.ofAdd 1))
    have hqt : q t = Multiplicative.ofAdd 1 := by
      change E.symm (QuotientGroup.mk' N t) = _
      rw [ht, E.symm_apply_apply]
    let e := cyclicKernelEquiv q t hqt
    obtain ⟨Γ, hΓ, S, Λ, hΛ, ⟨f⟩⟩ :=
      nilpotent_cyclic_finiteIndex_uniform_lattice (MulAut.conjNormal (H := q.ker) t)
    have hi : (Γ.map e.toMonoidHom).FiniteIndex := by
      let := hΓ
      exact Subgroup.FiniteIndex.map_of_surjective Γ e.surjective
    let eΓ := Γ.equivMapOfInjective e.toMonoidHom e.injective
    exact ⟨Γ.map e.toMonoidHom, hi, S, Λ, hΛ, ⟨eΓ.symm.trans f⟩⟩

end PolycyclicRecognition

end

end OAI
