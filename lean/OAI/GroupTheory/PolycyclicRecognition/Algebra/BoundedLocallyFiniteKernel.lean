import OAI.GroupTheory.PolycyclicRecognition.Analysis.ElementaryAmenable
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite

namespace OAI

/-! # Removing a locally finite kernel with bounded finite subgroup orders

The bound on finite subgroups remains an explicit premise. Local finiteness
then makes the whole kernel finite, and a finite kernel preserves virtual
solvability by centralizing that kernel.
-/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

def HasBoundedFiniteSubgroupOrders (G : Type) [Group G] : Prop :=
  ∃ b : ℕ, ∀ H : Subgroup G, Finite H → Nat.card H ≤ b

theorem HasBoundedFiniteSubgroupOrders.subgroup
    (hG : HasBoundedFiniteSubgroupOrders G) (H : Subgroup G) :
    HasBoundedFiniteSubgroupOrders H := by
  obtain ⟨b, hb⟩ := hG
  refine ⟨b, fun K hK => ?_⟩
  let := hK
  let e := K.equivMapOfInjective H.subtype Subtype.val_injective
  let : Finite (K.map H.subtype) := Finite.of_equiv K e.toEquiv
  simpa only [Nat.card_congr e.toEquiv] using hb (K.map H.subtype) inferInstance

theorem finite_of_locallyFinite_bounded
    (hlocal : ∀ H : Subgroup G, H.FG → Finite H)
    (hbound : HasBoundedFiniteSubgroupOrders G) : Finite G := by
  classical
  obtain ⟨b, hb⟩ := hbound
  by_contra h
  let : Infinite G := not_finite_iff_infinite.mp h
  let f : Fin (b + 1) → G := fun i => Infinite.natEmbedding G i.val
  have hf : Function.Injective f := (Infinite.natEmbedding G).injective.comp Fin.val_injective
  let H := Subgroup.closure (Set.range f)
  have hH : H.FG := (Subgroup.fg_iff H).mpr ⟨Set.range f, rfl, Set.finite_range f⟩
  let : Finite H := hlocal H hH
  let fH : Fin (b + 1) → H := fun i => ⟨f i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hfH : Function.Injective fH := fun a c hac => hf (congrArg Subtype.val hac)
  have hc := Nat.card_le_card_of_injective fH hfH
  have hh := hb H inferInstance
  simp only [Nat.card_fin] at hc
  omega

theorem finite_locallyFinite_normal_subgroup (N : Subgroup G)
    (hlocal : ∀ H : Subgroup N, H.FG → Finite H)
    (hbound : HasBoundedFiniteSubgroupOrders G) : Finite N :=
  finite_of_locallyFinite_bounded hlocal (hbound.subgroup N)

theorem virtually_solvable_of_finite_kernel
    {Q : Type} [Group Q] [Group.IsSolvable Q] (f : G →* Q) [Finite f.ker] :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  let K := f.ker
  let : Finite (MulAut K) := Finite.of_injective
    (fun a : MulAut K => (a : K → K)) DFunLike.coe_injective
  let ρ : G →* MulAut K := MulAut.conjNormal
  let H := ρ.ker
  let : H.FiniteIndex := inferInstance
  let p : H →* Q := f.comp H.subtype
  have hcomm : ∀ a b : p.ker, a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    have hb : ((b : H) : G) ∈ K := b.property
    have ha : ρ ((a : H) : G) = 1 := (a : H).property
    have he := congrArg (fun u : MulAut K => (u ⟨((b : H) : G), hb⟩ : G)) ha
    change ((a : H) : G) * ((b : H) : G) * ((a : H) : G)⁻¹ = ((b : H) : G) at he
    exact (mul_inv_eq_iff_eq_mul).mp he
  let : IsMulCommutative p.ker := ⟨⟨hcomm⟩⟩
  let e := QuotientGroup.quotientKerEquivRange p
  let : Group.IsSolvable (H ⧸ p.ker) := Group.isSolvable_of_isSolvable_injective
    (f := e.toMonoidHom) e.injective
  let : Group.IsSolvable H := Group.isSolvable_of_subgroup_quotient p.ker
  exact ⟨H, inferInstance, inferInstance⟩

theorem virtually_solvable_of_finite_kernel_virtual_quotient
    {Q : Type} [Group Q] (f : G →* Q) [Finite f.ker]
    (hQ : ∃ S : Subgroup Q, S.FiniteIndex ∧ Group.IsSolvable S) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  obtain ⟨S, hS, hsol⟩ := hQ
  let := hS
  let := hsol
  let P := S.comap f
  let : P.FiniteIndex := inferInstance
  let p : P →* S := (f.comp P.subtype).codRestrict S (fun x => x.property)
  let k : p.ker → f.ker := fun x => ⟨((x : P) : G),
    congrArg (fun s : S => (s : Q)) x.property⟩
  have hk : Function.Injective k := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : f.ker => (x : G)) hxy
  let : Finite p.ker := Finite.of_injective k hk
  obtain ⟨H, hH, hHsol⟩ := virtually_solvable_of_finite_kernel p
  let := hH
  let := hHsol
  let e := H.equivMapOfInjective P.subtype Subtype.val_injective
  let : Group.IsSolvable (H.map P.subtype) :=
    Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  refine ⟨H.map P.subtype, ⟨?_⟩, inferInstance⟩
  rw [Subgroup.index_map_subtype]
  exact mul_ne_zero hH.index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := P))

theorem virtually_solvable_of_locallyFinite_kernel_bounded (N : Subgroup G) [N.Normal]
    (hN : ∀ H : Subgroup N, H.FG → Finite H)
    (hb : HasBoundedFiniteSubgroupOrders G)
    (hQ : ∃ S : Subgroup (G ⧸ N), S.FiniteIndex ∧ Group.IsSolvable S) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  let : Finite N := finite_locallyFinite_normal_subgroup N hN hb
  let : Finite (QuotientGroup.mk' N).ker := by
    simpa only [QuotientGroup.ker_mk'] using (inferInstance : Finite N)
  exact virtually_solvable_of_finite_kernel_virtual_quotient (QuotientGroup.mk' N) hQ

end PolycyclicRecognition

end

end OAI
