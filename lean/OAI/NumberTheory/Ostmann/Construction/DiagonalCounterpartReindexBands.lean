import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexCoordinates
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparationPriors

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction

def remainingPositionBand (T : List SourceSlot) : RemainingIndex T→Option SlotRole :=
  Fin.cases none (fun i => some T[i].role)

def RemainingBandsSeparated (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource) : Prop :=
  ∀i j,remainingPositionBand T i≠remainingPositionBand T j →
    (remainingPositionSource sources T giant i).DisjointMass (remainingPositionSource sources T giant j)

def PreservesRemainingBands (T : List SourceSlot) (e : Equiv.Perm (RemainingIndex T)) : Prop :=
  ∀i,remainingPositionBand T (e i)=remainingPositionBand T i

def remainingPositionSample (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (x : RemainingSample sources T giant) (i : RemainingIndex T) :
    (remainingPositionSource sources T giant i).Sample :=
  ⟨remainingCoordinate sources T giant x i,remainingCoordinate_mem sources T giant x i⟩

theorem remainingPositionSample_mass_ne_zero (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x : RemainingSample sources T giant)
    (hx : (remainingPrior sources T giant).mass x≠0) (i : RemainingIndex T) :
    (remainingPositionSource sources T giant i).law.mass
      (remainingPositionSample sources T giant x i)≠0 := by
  obtain ⟨hq,hh⟩ := (remainingPrior_mass_ne_zero_iff sources T giant x).mp hx
  induction i using Fin.cases with
  | zero => exact hq
  | succ i => exact assignmentPrior_component_mass_ne_zero sources T x.2 hh i

theorem reconstructCounterpart_preserves_bands (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (hsep : RemainingBandsSeparated sources T giant)
    (x : RemainingSample sources T giant) (hx : (remainingPrior sources T giant).mass x≠0)
    (e : Equiv.Perm (RemainingIndex T)) (he : CounterpartCompatible sources T giant x e)
    (hy : (remainingPrior sources T giant).mass (reconstructCounterpart sources T giant x e he)≠0) :
    PreservesRemainingBands T e := by
  intro i
  by_contra hne
  have hd := hsep (e i) i hne
    (remainingPositionSample sources T giant x (e i))
    (remainingPositionSample sources T giant (reconstructCounterpart sources T giant x e he) i)
    (remainingPositionSample_mass_ne_zero sources T giant x hx (e i))
    (remainingPositionSample_mass_ne_zero sources T giant _ hy i)
  exact hd (reconstructCounterpart_coordinate sources T giant x e he i).symm

theorem PreservesRemainingBands.fixes_giant {T : List SourceSlot}
    {e : Equiv.Perm (RemainingIndex T)} (he : PreservesRemainingBands T e) : e 0=0 := by
  have h := he 0
  generalize hi : e 0=i at h ⊢
  induction i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [remainingPositionBand,Fin.cases_zero,Fin.cases_succ] at h
    cases h

theorem PreservesRemainingBands.role_eq {T : List SourceSlot}
    {e : Equiv.Perm (RemainingIndex T)} (he : PreservesRemainingBands T e)
    (i j : Fin T.length) (hij : e i.succ=j.succ) : T[j].role=T[i].role := by
  have h := he i.succ
  simpa only [hij,remainingPositionBand,Fin.cases_succ,Option.some.injEq] using h

end Ostmann.Construction

end

end OAI
