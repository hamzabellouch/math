import OAI.Probability.ThorpShuffle.Specht

namespace OAI

universe uα

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Specht
open scoped Classical

variable {α : Type uα} [Fintype α]

lemma tabloid_sum (r : α → ℕ) (f : Tabloid r) : ∑ x, f.val x = ∑ x, r x := by
  obtain ⟨g, hg⟩ := f.property
  rw [hg]
  exact Equiv.sum_comp g r

lemma collision_zero (r c : α → ℕ) (f : Tabloid r)
    (x y : α) (hxy : x ≠ y) (hc : c x = c y) (hf : f.val x = f.val y) :
    PermutationSpace.alternator (fiberGroup c).subtype
      (complexSign.comp (fiberGroup c).subtype) (EuclideanSpace.single f 1) = 0 := by
  apply PermutationSpace.alternator_single_zero _ _ f (⟨Equiv.swap x y, swap_preserves hc⟩ : fiberGroup c)
  · rw [stabilizes_tabloid_iff]
    exact swap_preserves hf
  · exact complexSign_swap x y hxy

lemma alternator_nonzero_nocollision (r c : α → ℕ)
    (v : EuclideanSpace ℂ (Tabloid r))
    (hv : PermutationSpace.alternator (fiberGroup c).subtype
      (complexSign.comp (fiberGroup c).subtype) v ≠ 0) :
    ∃ f : Tabloid r, ∀ x y, c x = c y → f.val x = f.val y → x = y := by
  by_contra hn
  push Not at hn
  apply hv
  have hexp := (EuclideanSpace.basisFun (Tabloid r) ℂ).sum_repr v
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at hexp
  rw [← hexp, map_sum]
  apply Finset.sum_eq_zero
  intro f _
  obtain ⟨x, y, hcol, hrow, hne⟩ := hn f
  rw [map_smul, collision_zero r c f x y hne hcol hrow, smul_zero]

lemma rowRankSum_tableau (D : YoungDiagram) (t : α ≃ Thorp.Young.Cells D) :
    ∑ x : α, tableauRow D t x = ∑ z : Thorp.Young.Cells D, z.val.1 :=
  Equiv.sum_comp t (fun z => z.val.1)

lemma rankSum_le_of_nocollision (D E : YoungDiagram)
    (t : α ≃ Thorp.Young.Cells D) (u : α ≃ Thorp.Young.Cells E)
    (f : Tabloid (tableauRow E u))
    (hf : ∀ x y, tableauCol D t x = tableauCol D t y → f.val x = f.val y → x = y) :
    ∑ z : Thorp.Young.Cells D, z.val.1 ≤ ∑ z : Thorp.Young.Cells E, z.val.1 := by
  have hi : ∀ x y : Thorp.Young.Cells D, x.val.2 = y.val.2 →
      f.val (t.symm x) = f.val (t.symm y) → x = y := by
    intro x y hc hr
    apply t.symm.injective
    apply hf _ _ _ hr
    simpa only [tableauCol, Equiv.apply_symm_apply] using hc
  have hh := Thorp.Young.rowRankSum_le D (fun z => f.val (t.symm z)) hi
  rw [Equiv.sum_comp t.symm, tabloid_sum, rowRankSum_tableau] at hh
  exact hh

lemma shape_eq_of_nocollision_equal_sum (D E : YoungDiagram)
    (t : α ≃ Thorp.Young.Cells D) (u : α ≃ Thorp.Young.Cells E)
    (f : Tabloid (tableauRow E u))
    (hf : ∀ x y, tableauCol D t x = tableauCol D t y → f.val x = f.val y → x = y)
    (hs : ∑ z : Thorp.Young.Cells D, z.val.1 = ∑ z : Thorp.Young.Cells E, z.val.1) : D = E := by
  have hi : ∀ x y : Thorp.Young.Cells D, x.val.2 = y.val.2 →
      f.val (t.symm x) = f.val (t.symm y) → x = y := by
    intro x y hc hr
    apply t.symm.injective
    apply hf _ _ _ hr
    simpa only [tableauCol, Equiv.apply_symm_apply] using hc
  have hsum : ∑ z : Thorp.Young.Cells D, f.val (t.symm z) = ∑ z : Thorp.Young.Cells D, z.val.1 := by
    rw [Equiv.sum_comp t.symm, tabloid_sum, rowRankSum_tableau, hs]
  obtain ⟨σ, -, hσ⟩ := Thorp.Young.column_sort D (fun z => f.val (t.symm z)) hi hsum
  obtain ⟨g, hg⟩ := f.property
  apply Thorp.Young.eq_of_rowPreserving D E (((σ.trans t.symm).trans g).trans u)
  intro x
  have hh := hσ x
  rw [hg] at hh
  exact hh

lemma mapped_column_nonzero (D E : YoungDiagram)
    (t : α ≃ Thorp.Young.Cells D) (u : α ≃ Thorp.Young.Cells E)
    (F : Representation.IntertwiningMap (module D t).toRepresentation (module E u).toRepresentation)
    (hF : Function.Injective F) :
    ∃ v : EuclideanSpace ℂ (Tabloid (tableauRow E u)),
      PermutationSpace.alternator (fiberGroup (tableauCol D t)).subtype
        (complexSign.comp (fiberGroup (tableauCol D t)).subtype) v ≠ 0 := by
  let e : (module D t).toSubmodule := ⟨polytabloid D t, self_mem_cyclic _ _⟩
  have he : e ≠ 0 := by
    intro h
    exact polytabloid_ne_zero D t (congrArg Subtype.val h)
  have heig : ∑ h : fiberGroup (tableauCol D t), complexSign h.val •
      (module D t).toRepresentation h.val e = ⟪polytabloid D t, polytabloid D t⟫_ℂ • e := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    change (∑ h : fiberGroup (tableauCol D t), complexSign h.val •
      tabloidRep D t h.val (polytabloid D t)) = _
    exact (PermutationSpace.alternator_apply _ _ _).symm.trans (columnAlternator_rank_one D t _)
  have hh := congrArg (fun z => (F z : EuclideanSpace ℂ (Tabloid (tableauRow E u)))) heig
  simp only [map_sum, map_smul, F.isIntertwining, Submodule.coe_sum, Submodule.coe_smul] at hh
  refine ⟨F e, ?_⟩
  intro hz
  have heq : PermutationSpace.alternator (fiberGroup (tableauCol D t)).subtype
      (complexSign.comp (fiberGroup (tableauCol D t)).subtype) (F e : EuclideanSpace ℂ (Tabloid (tableauRow E u))) =
      ⟪polytabloid D t, polytabloid D t⟫_ℂ • (F e : EuclideanSpace ℂ (Tabloid (tableauRow E u))) := by
    rw [PermutationSpace.alternator_apply]
    exact hh
  rw [hz] at heq
  rcases smul_eq_zero.mp heq.symm with hs | hs
  · exact polytabloid_ne_zero D t (inner_self_eq_zero.mp hs)
  · have hh' : F e = 0 := Subtype.ext hs
    exact he (hF (by simpa using hh'))

lemma rankSum_le_of_injective_intertwiner (D E : YoungDiagram)
    (t : α ≃ Thorp.Young.Cells D) (u : α ≃ Thorp.Young.Cells E)
    (F : Representation.IntertwiningMap (module D t).toRepresentation (module E u).toRepresentation)
    (hF : Function.Injective F) :
    ∑ z : Thorp.Young.Cells D, z.val.1 ≤ ∑ z : Thorp.Young.Cells E, z.val.1 := by
  obtain ⟨v, hv⟩ := mapped_column_nonzero D E t u F hF
  obtain ⟨f, hf⟩ := alternator_nonzero_nocollision _ _ v hv
  exact rankSum_le_of_nocollision D E t u f hf

theorem shape_eq_of_equiv (D E : YoungDiagram)
    (t : α ≃ Thorp.Young.Cells D) (u : α ≃ Thorp.Young.Cells E)
    (F : Representation.Equiv (module D t).toRepresentation (module E u).toRepresentation) : D = E := by
  have hle := rankSum_le_of_injective_intertwiner D E t u F.toIntertwiningMap F.toLinearEquiv.injective
  have hge := rankSum_le_of_injective_intertwiner E D u t F.symm.toIntertwiningMap F.symm.toLinearEquiv.injective
  obtain ⟨v, hv⟩ := mapped_column_nonzero D E t u F.toIntertwiningMap F.toLinearEquiv.injective
  obtain ⟨f, hf⟩ := alternator_nonzero_nocollision _ _ v hv
  exact shape_eq_of_nocollision_equal_sum D E t u f hf (le_antisymm hle hge)

end Thorp.Specht

end

end OAI
