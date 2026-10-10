import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantGridCellBoundsBudget
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementActual
open Construction Conclusion HistorySignedResidues SourcePriorGridDeletion
open PrimeCellReplacement LogCellPartition ScaleBudget PrimeCellMeshBudget
open HistoryGiantGridCellBounds
open scoped BigOperators
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}

def primeErrorUpper (C : InitialSourceChoice d Bs BD Bz k₀ L E) (h k : History l)
    (outside : List ℕ) (deleted : Finset ℕ) (M : ℕ) [NeZero M]
    (hd : pairModulus h k outside ∣ M) (K δ : ℝ) : ℝ :=
  let G := C.giantCenter
  let D := referenceDerivative C h k [false,true]
  let A := referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l
  let mesh := meshWidth giant L
  deletionCap G deleted*(1+fullMassRatio G deleted)*((outside.prod : ℝ)^(2^(l+1))*A) +
    (2*(2*D*mesh)*principalMass M (fun _ : Bool => G-1) (fun _ => G+1)
      (fun _ => logCellMass G deleted) +
      (2*D*mesh+A)*(Fintype.card (GridBoxIndex (fun _ : Bool => G-1) (fun _ => G+1)
        (fun _ => mesh))*(8*giantPrimeError K δ G deleted))) *
      ∑ u : Bool → (ZMod M)ˣ,
        ‖primeResidueTest (residueTransform d) (frequencyBound Bs BD Bz k₀ L) outside h k M hd u‖

def mixedErrorUpper (C : InitialSourceChoice d Bs BD Bz k₀ L E) (h k : History l)
    (outside : List ℕ) (deleted : Finset ℕ) (M : ℕ) [NeZero M]
    (hd : pairModulus h k outside ∣ M) (K δ : ℝ) : ℝ :=
  let G := C.giantCenter
  let D := referenceDerivative C h k [true]
  let A := referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l
  let mesh := meshWidth giant L
  (Real.exp 1+1)*deletionCap G deleted*((outside.prod : ℝ)^(2^(l+1))*A) +
    (2*(2*D*mesh)*mixedPrincipalMass M (G-1) (G+1) G smoothPartition
      (fun _ : Unit => G-1) (fun _ => G+1) (fun _ => logCellMass G deleted) +
      (2*D*mesh+A)*(Fintype.card (MixedGridIndex (G-1) (G+1) mesh
        (fun _ : Unit => G-1) (fun _ => G+1) (fun _ => mesh))*
          giantMixedError K δ G L deleted)) *
      ∑ r : ZMod M, ∑ u : Unit → (ZMod M)ˣ,
        ‖mixedResidueTest (residueTransform d) (frequencyBound Bs BD Bz k₀ L) outside h k M hd r u‖

end Ostmann.Arithmetic.HistoryGiantXiReplacementActual

end

end OAI
