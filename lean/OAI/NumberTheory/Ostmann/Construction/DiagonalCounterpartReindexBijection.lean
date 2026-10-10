import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexCoordinates

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction

abbrev CounterpartPermutation (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (x : RemainingSample sources T giant) :=
  {e : Equiv.Perm (RemainingIndex T) // CounterpartCompatible sources T giant x e}

abbrev RemainingProductFiber (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (x : RemainingSample sources T giant) :=
  {y : RemainingSample sources T giant // remainingProduct sources T giant y=remainingProduct sources T giant x}

def counterpartReconstruction (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (x : RemainingSample sources T giant) :
    CounterpartPermutation sources T giant x→RemainingProductFiber sources T giant x :=
  fun e => ⟨reconstructCounterpart sources T giant x e.val e.property,
    reconstructCounterpart_product sources T giant x e.val e.property⟩

theorem counterpartReconstruction_bijective (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x : RemainingSample sources T giant)
    (hx : (remainingValues sources T giant x).Nodup) :
    Function.Bijective (counterpartReconstruction sources T giant x) := by
  constructor
  · intro e f he
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply remainingCoordinate_injective_of_nodup sources T giant x hx
    have hh := congrArg (fun y : RemainingProductFiber sources T giant x =>
      remainingCoordinate sources T giant y.val i) he
    simpa only [counterpartReconstruction,reconstructCounterpart_coordinate] using hh
  · intro y
    obtain ⟨e,he,huniq⟩ := remainingCoordinate_existsUnique_matching sources T giant x y.val hx y.property.symm
    have hcompat : CounterpartCompatible sources T giant x e := by
      intro i
      rw [←he i]
      exact remainingCoordinate_mem sources T giant y.val i
    refine ⟨⟨e,hcompat⟩,?_⟩
    apply Subtype.ext
    apply remainingCoordinate_ext sources T giant
    intro i
    exact (reconstructCounterpart_coordinate sources T giant x e hcompat i).trans (he i).symm

def counterpartEquiv (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (x : RemainingSample sources T giant) (hx : (remainingValues sources T giant x).Nodup) :
    CounterpartPermutation sources T giant x ≃ RemainingProductFiber sources T giant x :=
  Equiv.ofBijective (counterpartReconstruction sources T giant x)
    (counterpartReconstruction_bijective sources T giant x hx)

theorem sum_remainingProduct_eq_counterparts (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x : RemainingSample sources T giant)
    (hx : (remainingValues sources T giant x).Nodup) (F : RemainingSample sources T giant→ℂ) :
    (∑y,if remainingProduct sources T giant y=remainingProduct sources T giant x then F y else 0) =
      ∑e : CounterpartPermutation sources T giant x,
        F (reconstructCounterpart sources T giant x e.val e.property) := by
  have hs : (∑y : RemainingProductFiber sources T giant x,F y.val)=
      ∑y,if remainingProduct sources T giant y=remainingProduct sources T giant x then F y else 0 := by
    simpa [Finset.sum_filter] using
      (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
        (p := fun y => remainingProduct sources T giant y=remainingProduct sources T giant x) F)
  rw [←hs]
  exact (Fintype.sum_equiv (counterpartEquiv sources T giant x hx)
    (fun e => F (reconstructCounterpart sources T giant x e.val e.property))
    (fun y => F y.val) (fun e => rfl)).symm

theorem weighted_remainingProduct_eq_counterparts (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x : RemainingSample sources T giant)
    (hx : (remainingValues sources T giant x).Nodup) (F : RemainingSample sources T giant→ℂ) :
    (∑y,if remainingProduct sources T giant y=remainingProduct sources T giant x then
      ((remainingPrior sources T giant).mass y:ℂ)*F y else 0) =
      ∑e : CounterpartPermutation sources T giant x,
        ((remainingPrior sources T giant).mass
          (reconstructCounterpart sources T giant x e.val e.property):ℂ)*
        F (reconstructCounterpart sources T giant x e.val e.property) :=
  sum_remainingProduct_eq_counterparts sources T giant x hx _

end Ostmann.Construction

end

end OAI
