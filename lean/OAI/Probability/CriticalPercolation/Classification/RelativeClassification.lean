import Mathlib
import OAI.Probability.CriticalPercolation.Growth.CosetIndicability
import OAI.Probability.CriticalPercolation.Growth.CosetIntegerKernel
import OAI.Probability.CriticalPercolation.Growth.CosetKernelDescent
import OAI.Probability.CriticalPercolation.Growth.CosetNormalPromotion
import OAI.Probability.CriticalPercolation.Growth.CosetSubgroupGenerators
import OAI.Probability.CriticalPercolation.Growth.CosetFiniteCore

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma bounded_top_of_finiteIndex (K : Subgroup A) (S : Set A)
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hK : Bounded S (K:Set A)) [K.FiniteIndex] : Bounded S (⊤:Subgroup A) := by
  let := K.fintypeQuotientOfFiniteIndex
  apply bounded_of_finite_coset_image S K h1 hi hgen hK
  exact Set.toFinite _

lemma relIndex_map_subgroupOf_of_le (K L : Subgroup A) (hKL : K≤L)
    (N : Subgroup L) (hN : N.relIndex (K.subgroupOf L)≠0) :
    (N.map L.subtype).relIndex K≠0 := by
  have he : (K.subgroupOf L).map L.subtype=K := by
    rw [Subgroup.subgroupOf,Subgroup.map_comap_eq,Subgroup.range_subtype,inf_eq_right.mpr hKL]
  rw [←he,Subgroup.relIndex_map_map_of_injective N (K.subgroupOf L) L.subtype_injective]
  exact hN

universe u

theorem bounded_normal_commensurable (d : ℕ) :
    ∀ (A : Type u) [Group A] (K : Subgroup A) (S : Set A),
      (1:A)∈S → S⁻¹=S → Subgroup.closure S=⊤ → Bounded S (K:Set A) → HasDegree K S d →
      ∃ N : Subgroup A, N.Normal ∧ Bounded S (N:Set A) ∧ N.relIndex K≠0 := by
  induction d with
  | zero =>
    intro A _ K S h1 hi hgen hK hg
    let := hg.zero_finiteIndex h1 hi hgen
    exact ⟨⊤,inferInstance,bounded_top_of_finiteIndex K S h1 hi hgen hK,by simp⟩
  | succ d ih =>
    intro A _ K S h1 hi hgen hK hg
    rcases finite_or_infinite (A ⧸ K) with hfin | hinf
    · let : K.FiniteIndex := ⟨by let := hfin; exact Nat.card_pos.ne'⟩
      exact ⟨⊤,inferInstance,bounded_top_of_finiteIndex K S h1 hi hgen hK,by simp⟩
    let := hinf
    obtain ⟨H,hHi,f,hf,hKf⟩ := virtually_indicable h1 hi hgen hK hg
    let := hHi
    let J := K.subgroupOf H
    obtain ⟨T,hT1,hTi,hTgen,hTb,hKT⟩ :=
      finiteIndex_generators_containing_stabilizer K S h1 hi hgen hK H
    have hgT : HasDegree J T (d+1) := hg.subgroup_bounded h1 H T hTb
    obtain ⟨U,hU1,hUi,hUgen,hUb,hKU⟩ :=
      hgT.integer_kernel_bounded_generators hT1 hTi hTgen hKT f hf hKf
    have hgU : HasDegree (J.subgroupOf f.ker) U d :=
      hgT.integer_kernel_descent hT1 hTi hTgen f hf hKf U hUb
    obtain ⟨N,hNn,hNb,hNi⟩ := ih f.ker (J.subgroupOf f.ker) U hU1 hUi hUgen
      ⟨1,by simpa only [pow_one] using hKU⟩ hgU
    let := hNn
    let P := N.map f.ker.subtype
    have hPL : P≤f.ker := by rintro _ ⟨n,hn,rfl⟩; exact n.property
    have hPN : f.ker≤Subgroup.normalizer (P:Set H) := normalizer_of_normal_subgroup f.ker N
    have hPb : Bounded T (P:Set H) := Bounded.image_trans f.ker.subtype hUb hNb
    have hPi : P.relIndex J≠0 := relIndex_map_subgroupOf_of_le J f.ker hKf N hNi
    obtain ⟨M,hMn,hMb,hMi⟩ := hgT.promote_integer_normal hT1 hTi hTgen f hf hKf P hPL hPN hPb hPi
    let := hMn
    let Q := M.map H.subtype
    have hQn : H≤Subgroup.normalizer (Q:Set A) := normalizer_of_normal_subgroup H M
    have hQb : Bounded S (Q:Set A) := Bounded.image_trans H.subtype hTb hMb
    have hQi : Q.relIndex K≠0 := relIndex_map_subgroupOf_nonzero K H M hMi
    exact hg.finiteIndex_normal_core h1 hi hgen hK H Q hQn hQb hQi

end CriticalPercolation.RelativeGrowth
end
end

end OAI
