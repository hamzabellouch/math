import OAI.NumberTheory.Ostmann.Construction.BinScale
import OAI.NumberTheory.Ostmann.Construction.HalfListStatistic
import OAI.NumberTheory.Ostmann.Construction.SelectedCellSources

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators

def bulkPrimeBand (L : ℝ) (E : Finset ℕ) : Finset ℕ :=
  logLogPrimeBand ((1/250:ℝ)*L) ((3/500:ℝ)*L) \ E

def bulkPrimeSource (L : ℝ) (E : Finset ℕ) (hZ : 0<harmonicPrimeMass (bulkPrimeBand L E)) : PrimeSource :=
  harmonicPrimeSource (bulkPrimeBand L E)
    (fun _p hp => logLogPrimeBand_prime (Finset.mem_sdiff.mp hp).1) hZ

structure InitialSourceChoice (d : Decomposition) (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (E : Finset ℕ) where
  deleted_card : E.card≤2
  blockBase : ℝ
  giantCenter : ℤ
  favorable : Finset ℕ
  giantPositive : 0<logCellMass giantCenter ∅
  bulkPositive : 0<harmonicPrimeMass (bulkPrimeBand L E)
  bulkBin : ℤ
  spectatorBin : ℤ
  cells : NominalCenterArray d k L
    (nominalJ Bs BD Bz k L blockBase giantCenter spectatorBin) bulkBin
    (fun j => nominalCompensation Bs BD Bz k L blockBase giantCenter spectatorBin j)

namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

def scale (C : InitialSourceChoice d Bs BD Bz k L E) : ℕ :=
  giantWindowScale ((2:ℝ)^(k+1)) C.blockBase L

def giant (C : InitialSourceChoice d Bs BD Bz k L E) : PrimeSource :=
  logCellPrimeSource C.giantCenter ∅ C.giantPositive

def bulk (C : InitialSourceChoice d Bs BD Bz k L E) : PrimeSource :=
  bulkPrimeSource L E C.bulkPositive

def auxiliary (C : InitialSourceChoice d Bs BD Bz k L E) : AuxiliaryIndex k → PrimeSource :=
  C.cells.auxSource E C.deleted_card

def sources (C : InitialSourceChoice d Bs BD Bz k L E) : SourceFamily :=
  C.cells.sources E C.deleted_card (Conclusion.bulkSize k L/2) C.bulk

def test (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource) : ℤ → ℝ :=
  halfListTest d C.favorable C.giant C.bulk spectator C.auxiliary
    (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2) C.bulkBin C.spectatorBin

def statistic (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource) : ℝ :=
  smoothedStatistic C.scale (C.test spectator)

theorem auxiliary_balanced (C : InitialSourceChoice d Bs BD Bz k L E) (i : AuxiliaryIndex k) :
    (1/2:ℝ) ≤ (C.auxiliary i).law.mean (fun p => balancedPrimeIndicator d p) :=
  C.cells.auxSource_balanced E C.deleted_card i

theorem test_summable (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (hX : 0<C.scale) :
    Summable (fun n : ℤ => (SchwartzCutoff.psi ((n:ℝ)/C.scale)).re*(C.test spectator n)^2) :=
  halfListTest_statistic_summable _ _ _ _ _ _ _ _ _ _ (by exact_mod_cast hX)

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
