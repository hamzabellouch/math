import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAveragePrincipal

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion HistoryBulkSourceDisintegration HistoryGiantReferenceMean
open HistoryBulkFibreOriginalReference HistoryBulkFibreGiantApproximation
open HistoryBulkActualRootReferenceFamily
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

theorem leftChoices_mass_of_draws (x : Draws C (l:=l))
    (hx : (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).mass x ≠ 0)
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) :
    choicesMass C.sources _ _ l (leftChoices C x i) ≠ 0 := by
  simpa only [leftChoices,choicesMass_assemble] using hx

theorem rightChoices_mass_of_draws (y : Draws C (l:=l))
    (hy : (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).mass y ≠ 0)
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) :
    choicesMass C.sources _ _ l (rightChoices C y i) ≠ 0 := by
  simpa only [rightChoices,choicesMass_assemble] using hy

theorem spectatorList_source (spectator : PrimeSource)
    (ds : Fin (2*(bulkSize k L/2))→spectator.Sample) :
    ∀q∈spectatorList spectator ds,∃p:spectator.Sample,(p:ℕ)=q := by
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact ⟨ds i,rfl⟩

def primeOriginalValue (spectator : PrimeSource)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
    (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
    (a : SelectedNonbulkSample C l) (x y : Draws C (l:=l))
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) : ℂ :=
  wholeMean C (spectatorList spectator ds) σ a x y (fun _ _ _ _=>1)
    (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) i

def mixedOriginalValue (spectator : PrimeSource)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
    (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
    (a : SelectedNonbulkSample C l) (x y : Draws C (l:=l))
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) : ℂ :=
  wholeMean C (spectatorList spectator ds) σ a x y
    (fun i=>plainMixedWeight C (spectatorList spectator ds) a i.1.val)
    (mixedWeight C.giantCenter C.giant)
    (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i

def primeSelectedPrincipal (spectator : PrimeSource)
    (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
    (hl : l≤k) (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
    (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
    (a : SelectedNonbulkSample C l) (x y : Draws C (l:=l))
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) : ℂ :=
  if ha : 0<(selectedNonbulkPrior C l).mass a then
    if hx : (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).mass x≠0 then
      if hy : (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).mass y≠0 then
        (selectWitness C (spectatorList spectator ds) σ a x y (fun _ _ _ _=>1)
          (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
          hactual hl ha (leftChoices_mass_of_draws C x hx) (rightChoices_mass_of_draws C y hy)
          (spectatorList_source spectator ds) (primeWeight_nonneg C.giant)
          (fun r _=>primeDraw_positive C.giant r) i).elim 0
          (fun r=>primeWitnessPrincipal C (spectatorList spectator ds) σ a x y r ha
            (leftChoices_mass_of_draws C x hx i) (rightChoices_mass_of_draws C y hy i)
            (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds))
      else 0
    else 0
  else 0

def mixedSelectedPrincipal (spectator : PrimeSource)
    (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
    (hl : l≤k) (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
    (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
    (a : SelectedNonbulkSample C l) (x y : Draws C (l:=l))
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) : ℂ :=
  if ha : 0<(selectedNonbulkPrior C l).mass a then
    if hx : (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).mass x≠0 then
      if hy : (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).mass y≠0 then
        (selectWitness C (spectatorList spectator ds) σ a x y
          (fun i=>plainMixedWeight C (spectatorList spectator ds) a i.1.val)
          (mixedWeight C.giantCenter C.giant)
          (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant)
          hactual hl ha (leftChoices_mass_of_draws C x hx) (rightChoices_mass_of_draws C y hy)
          (spectatorList_source spectator ds) (mixedWeight_nonneg C.giantCenter C.giant)
          (fun r _=>mixedDraw_positive C.giantCenter C.giant r) i).elim 0
          (fun r=>mixedWitnessPrincipal C (spectatorList spectator ds) σ a x y r ha
            (leftChoices_mass_of_draws C x hx i) (rightChoices_mass_of_draws C y hy i)
            (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds))
      else 0
    else 0
  else 0

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
