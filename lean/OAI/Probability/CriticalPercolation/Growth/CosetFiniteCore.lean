import Mathlib
import OAI.Probability.CriticalPercolation.Growth.CosetTransfer
import OAI.Probability.CriticalPercolation.Criticality.BoundedNormalJoins

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma conjugate_map_one (N : Subgroup A) : N.map (MulAut.conj (1:A)).toMonoidHom=N :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.normalizer (N:Set A)).one_mem
lemma conjugate_eq_of_normalizer (N : Subgroup A) (g r : A) (h : r⁻¹*g∈(Subgroup.normalizer (N:Set A))) :
    N.map (MulAut.conj g).toMonoidHom=N.map (MulAut.conj r).toMonoidHom := by
  have he : N.map (MulAut.conj (r⁻¹*g)).toMonoidHom=N := Subgroup.mem_normalizer_iff_map_conj_eq.mp h
  have hh := congrArg (fun P : Subgroup A => P.map (MulAut.conj r).toMonoidHom) he
  rw [conjugate_map_map,mul_inv_cancel_left] at hh
  exact hh

lemma conjugate_stabilizer_relIndex (K : Subgroup A) (S : Set A)
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hK : Bounded S (K:Set A)) (hf : ∀ n, (ball K S n).Finite) (g : A) :
    (K.map (MulAut.conj g).toMonoidHom).relIndex K≠0 := by
  have hk := (bounded_subgroup_iff K (K.map (MulAut.conj g⁻¹).toMonoidHom) S h1 hi hgen hK hf).mp (hK.conj h1 hi hgen g⁻¹)
  have he := Subgroup.relIndex_map_map_of_injective K (K.map (MulAut.conj g⁻¹).toMonoidHom) (f:=(MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [conjugate_map_map,mul_inv_cancel,conjugate_map_one] at he
  rwa [he]

lemma conjugate_commensurable_index (K N : Subgroup A) (S : Set A)
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hK : Bounded S (K:Set A)) (hf : ∀ n, (ball K S n).Finite)
    (hN : N.relIndex K≠0) (g : A) :
    (N.map (MulAut.conj g).toMonoidHom).relIndex K≠0 := by
  apply Subgroup.relIndex_ne_zero_trans (K:=K.map (MulAut.conj g).toMonoidHom)
  · rwa [Subgroup.relIndex_map_map_of_injective N K (MulAut.conj g).injective]
  · exact conjugate_stabilizer_relIndex K S h1 hi hgen hK hf g

lemma finite_conjugate_family_of_finiteIndex_normalizer (H N : Subgroup A)
    [H.FiniteIndex] (hHN : H≤(Subgroup.normalizer (N:Set A))) :
    (Set.range (fun g : A => N.map (MulAut.conj g).toMonoidHom)).Finite := by
  let := H.fintypeQuotientOfFiniteIndex
  obtain ⟨R,hR,hR1⟩ := H.exists_isComplement_left 1
  have hRf : R.Finite := by
    let : Fintype R := Fintype.ofEquiv _ hR.leftQuotientEquiv
    exact Set.toFinite R
  apply (hRf.image (fun g => N.map (MulAut.conj g).toMonoidHom)).subset
  rintro _ ⟨g,rfl⟩
  refine ⟨hR.toLeftFun g,(hR.toLeftFun g).property,?_⟩
  exact (conjugate_eq_of_normalizer N g (hR.toLeftFun g) (hHN (hR.inv_toLeftFun_mul_mem g))).symm

lemma HasDegree.finiteIndex_normal_core {K : Subgroup A} {S : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hK : Bounded S (K:Set A)) (hg : HasDegree K S d)
    (H N : Subgroup A) [H.FiniteIndex] (hHN : H≤(Subgroup.normalizer (N:Set A)))
    (hNb : Bounded S (N:Set A)) (hNi : N.relIndex K≠0) :
    ∃ M : Subgroup A, M.Normal ∧ Bounded S (M:Set A) ∧ M.relIndex K≠0 := by
  refine ⟨N.normalCore,inferInstance,hNb.mono N.normalCore_le,?_⟩
  let F := Set.range (fun g : A => N.map (MulAut.conj g).toMonoidHom)
  let : Finite F := (finite_conjugate_family_of_finiteIndex_normalizer H N hHN).to_subtype
  have he : N.normalCore=⨅ P : F, P.val := by
    rw [Subgroup.normalCore_eq_iInf_map_conj]
    apply le_antisymm
    · apply le_iInf
      rintro ⟨P,⟨g,rfl⟩⟩
      exact iInf_le _ g
    · apply le_iInf
      intro g
      exact iInf_le (fun P : F => P.val) (⟨N.map (MulAut.conj g).toMonoidHom,⟨g,rfl⟩⟩ : F)
  rw [he]
  apply Subgroup.relIndex_iInf_ne_zero
  rintro ⟨P,⟨g,rfl⟩⟩
  exact conjugate_commensurable_index K N S h1 hi hgen hK hg.1 hNi g

end CriticalPercolation.RelativeGrowth
end
end

end OAI
