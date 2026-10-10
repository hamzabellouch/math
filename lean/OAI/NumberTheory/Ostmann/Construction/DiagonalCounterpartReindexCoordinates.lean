import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexSupport

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction

abbrev RemainingIndex (T : List SourceSlot) := Fin (T.length+1)

def remainingPositionSource (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource) :
    RemainingIndex T→PrimeSource := Fin.cases giant (fun i => sources T[i].origin)

def remainingCoordinate (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (x : RemainingSample sources T giant) : RemainingIndex T→ℕ :=
  Fin.cases x.1.val (fun i => (x.2 i).val)

theorem remainingCoordinate_mem (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (x : RemainingSample sources T giant) (i : RemainingIndex T) :
    remainingCoordinate sources T giant x i∈(remainingPositionSource sources T giant i).candidates := by
  induction i using Fin.cases with
  | zero => exact x.1.property
  | succ i => exact (x.2 i).property

theorem remainingCoordinate_list (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (x : RemainingSample sources T giant) :
    List.ofFn (remainingCoordinate sources T giant x)=remainingValues sources T giant x := by
  simp only [remainingCoordinate,List.ofFn_succ,Fin.cases_zero,Fin.cases_succ,
    remainingValues,assignedSlots,Template.sample,List.map_ofFn,Function.comp_def]

@[simp] theorem remainingCoordinate_prod (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x : RemainingSample sources T giant) :
    (∏i,remainingCoordinate sources T giant x i)=remainingProduct sources T giant x := by
  rw [←List.prod_ofFn,remainingCoordinate_list,remainingValues_prod]

theorem remainingCoordinate_ext (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    {x y : RemainingSample sources T giant}
    (he : ∀i,remainingCoordinate sources T giant x i=remainingCoordinate sources T giant y i) : x=y := by
  apply Prod.ext
  · exact Subtype.ext (he 0)
  · funext i
    exact Subtype.ext (he i.succ)

theorem remainingCoordinate_injective_of_nodup (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x : RemainingSample sources T giant)
    (hx : (remainingValues sources T giant x).Nodup) :
    Function.Injective (remainingCoordinate sources T giant x) := by
  rw [←remainingCoordinate_list] at hx
  exact List.nodup_ofFn.mp hx

def CounterpartCompatible (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (x : RemainingSample sources T giant) (e : Equiv.Perm (RemainingIndex T)) : Prop :=
  ∀i,remainingCoordinate sources T giant x (e i)∈(remainingPositionSource sources T giant i).candidates

def reconstructCounterpart (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (x : RemainingSample sources T giant) (e : Equiv.Perm (RemainingIndex T))
    (he : CounterpartCompatible sources T giant x e) : RemainingSample sources T giant :=
  (⟨remainingCoordinate sources T giant x (e 0),he 0⟩,
    fun i => ⟨remainingCoordinate sources T giant x (e i.succ),he i.succ⟩)

@[simp] theorem reconstructCounterpart_coordinate (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x : RemainingSample sources T giant) (e : Equiv.Perm (RemainingIndex T))
    (he : CounterpartCompatible sources T giant x e) (i : RemainingIndex T) :
    remainingCoordinate sources T giant (reconstructCounterpart sources T giant x e he) i=
      remainingCoordinate sources T giant x (e i) := by
  induction i using Fin.cases <;> rfl

@[simp] theorem reconstructCounterpart_product (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x : RemainingSample sources T giant) (e : Equiv.Perm (RemainingIndex T))
    (he : CounterpartCompatible sources T giant x e) :
    remainingProduct sources T giant (reconstructCounterpart sources T giant x e he)=
      remainingProduct sources T giant x := by
  rw [←remainingCoordinate_prod,←remainingCoordinate_prod]
  simp only [reconstructCounterpart_coordinate]
  exact Fintype.prod_equiv e _ _ (fun i => rfl)

theorem remainingCoordinate_range_eq (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x y : RemainingSample sources T giant)
    (he : remainingProduct sources T giant x=remainingProduct sources T giant y) :
    Set.range (remainingCoordinate sources T giant x)=Set.range (remainingCoordinate sources T giant y) := by
  have hp := remainingValues_perm_of_product_eq sources T giant x y he
  rw [←remainingCoordinate_list,←remainingCoordinate_list] at hp
  ext a
  simpa only [Set.mem_range,←List.mem_ofFn] using (hp.mem_iff (a:=a))

theorem remainingCoordinate_existsUnique_matching (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x y : RemainingSample sources T giant)
    (hx : (remainingValues sources T giant x).Nodup)
    (he : remainingProduct sources T giant x=remainingProduct sources T giant y) :
    ∃! e : Equiv.Perm (RemainingIndex T),
      ∀i,remainingCoordinate sources T giant y i=remainingCoordinate sources T giant x (e i) := by
  have hp := remainingValues_perm_of_product_eq sources T giant x y he
  have hix := remainingCoordinate_injective_of_nodup sources T giant x hx
  have hiy := remainingCoordinate_injective_of_nodup sources T giant y (hp.nodup_iff.mp hx)
  let ex := Equiv.ofInjective (remainingCoordinate sources T giant x) hix
  let ey := Equiv.ofInjective (remainingCoordinate sources T giant y) hiy
  let er := Equiv.subtypeEquivRight (fun a => Set.ext_iff.mp
    (remainingCoordinate_range_eq sources T giant x y he).symm a)
  let e : Equiv.Perm (RemainingIndex T) := ey.trans (er.trans ex.symm)
  have he' : ∀i,remainingCoordinate sources T giant y i=remainingCoordinate sources T giant x (e i) := by
    intro i
    exact (congrArg Subtype.val (ex.apply_symm_apply (er (ey i)))).symm
  refine ⟨e,he',?_⟩
  intro f hf
  apply Equiv.ext
  intro i
  exact hix ((hf i).symm.trans (he' i))

end Ostmann.Construction

end

end OAI
