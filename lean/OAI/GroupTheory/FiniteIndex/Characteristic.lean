import OAI.GroupTheory.FiniteIndex.FiniteKernel

namespace OAI

/-! Characteristic finite-index refinement by kernels of finite quotients. -/

namespace FiniteIndexRealization

lemma finite_hom_of_fg (H Q : Type*) [Group H] [Group.FG H] [Group Q] [Finite Q] :
    Finite (H →* Q) := by
  classical
  obtain ⟨S, hS, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG H)
  let : Finite S := hfin.to_subtype
  apply Finite.of_injective (fun f : H →* Q => fun s : S => f s)
  intro f g h
  apply MonoidHom.eq_of_eqOn_dense hS
  intro s hs
  exact congrFun h ⟨s, hs⟩

def universalKernel (H Q : Type*) [Group H] [Group Q] : Subgroup H :=
  ⨅ f : H →* Q, f.ker

lemma universalKernel_characteristic (H Q : Type*) [Group H] [Group Q] :
    (universalKernel H Q).Characteristic := by
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro e x hx
  change e x ∈ universalKernel H Q
  apply Subgroup.mem_iInf.mpr
  intro f
  exact Subgroup.mem_iInf.mp hx (f.comp e.toMonoidHom)

lemma universalKernel_finiteIndex (H Q : Type*) [Group H] [Group.FG H]
    [Group Q] [Finite Q] : (universalKernel H Q).FiniteIndex := by
  let : Finite (H →* Q) := finite_hom_of_fg H Q
  exact Subgroup.finiteIndex_iInf fun f => inferInstance

theorem characteristic_finiteIndex_refinement (H : Type*) [Group H] [Group.FG H]
    (U : Subgroup H) [U.FiniteIndex] :
    ∃ K : Subgroup H, K.Characteristic ∧ K.FiniteIndex ∧ K ≤ U := by
  let Q := H ⧸ U.normalCore
  let K := universalKernel H Q
  refine ⟨K, universalKernel_characteristic H Q, universalKernel_finiteIndex H Q, ?_⟩
  intro x hx
  have h := Subgroup.mem_iInf.mp hx (QuotientGroup.mk' U.normalCore)
  have hc : x ∈ U.normalCore :=
    (QuotientGroup.eq_one_iff (N := U.normalCore) x).mp h
  exact U.normalCore_le hc

end FiniteIndexRealization

end OAI
