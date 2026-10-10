import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualBoundsBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementActual
open Construction Conclusion HistorySignedResidues SourcePriorGridDeletion
open PrimeCellReplacement LogCellPartition ScaleBudget PrimeCellMeshBudget
open HistoryGiantGridCellBounds
open scoped BigOperators

theorem primeErrorUpper_algebra {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k₀ L E) (h k : History l)
    (outside : List ℕ) (deleted : Finset ℕ) (M : ℕ) [NeZero M]
    (hd : pairModulus h k outside ∣ M) (K δ F J Q r : ℝ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J) (hQ : 0 ≤ Q)
    (hmass : 0 ≤ principalMass M (fun _ : Bool => C.giantCenter-1) (fun _ => C.giantCenter+1) (fun _ => logCellMass C.giantCenter deleted)) (he : 0 ≤ giantPrimeError K δ C.giantCenter deleted)
    (hmesh : meshWidth giant L ≤ 1)
    (hD : referenceDerivative C h k [false,true] ≤ F) (hA : referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l ≤ F)
    (hN : (Fintype.card (GridBoxIndex (fun _ : Bool => C.giantCenter-1) (fun _ => C.giantCenter+1) (fun _ => meshWidth giant L)) : ℝ) ≤ J) (hS : (∑u : Bool → (ZMod M)ˣ, ‖primeResidueTest (residueTransform d) (frequencyBound Bs BD Bz k₀ L) outside h k M hd u‖) ≤ Q)
    (hdel : deletionCap C.giantCenter deleted*(1+fullMassRatio C.giantCenter deleted)*((outside.prod:ℝ)^(2^(l+1))*(referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l)) ≤ r)
    (hvar : meshWidth giant L*Q*F*(principalMass M (fun _ : Bool => C.giantCenter-1) (fun _ => C.giantCenter+1) (fun _ => logCellMass C.giantCenter deleted)) ≤ r)
    (hgrid : J*Q*F*(giantPrimeError K δ C.giantCenter deleted) ≤ r) :
    primeErrorUpper C h k outside deleted M hd K δ ≤ 29*r := by
  have hz := replacement_error_algebra (deletionCap C.giantCenter deleted*(1+fullMassRatio C.giantCenter deleted)*((outside.prod:ℝ)^(2^(l+1))*(referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l))) (referenceDerivative C h k [false,true]) (referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l) (meshWidth giant L)
    (principalMass M (fun _ : Bool => C.giantCenter-1) (fun _ => C.giantCenter+1) (fun _ => logCellMass C.giantCenter deleted)) (Fintype.card (GridBoxIndex (fun _ : Bool => C.giantCenter-1) (fun _ => C.giantCenter+1) (fun _ => meshWidth giant L)) : ℝ) (∑u : Bool → (ZMod M)ˣ, ‖primeResidueTest (residueTransform d) (frequencyBound Bs BD Bz k₀ L) outside h k M hd u‖) F J Q (giantPrimeError K δ C.giantCenter deleted) 8 r
    (referenceDerivative_nonneg C h k _) (referenceAmplitude_nonneg Bs L k₀ l)
    (Real.exp_nonneg _) hmass (by positivity) (by positivity) hF hJ hQ he
    (by norm_num) hmesh hD hA hN hS hdel hvar hgrid
  simpa only [primeErrorUpper, one_mul, show (5+3*(8:ℝ))=29 by norm_num] using hz

theorem mixedErrorUpper_algebra {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k₀ L E) (h k : History l)
    (outside : List ℕ) (deleted : Finset ℕ) (M : ℕ) [NeZero M]
    (hd : pairModulus h k outside ∣ M) (K δ F J Q r : ℝ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J) (hQ : 0 ≤ Q)
    (hmass : 0 ≤ mixedPrincipalMass M (C.giantCenter-1) (C.giantCenter+1) C.giantCenter smoothPartition (fun _ : Unit => C.giantCenter-1) (fun _ => C.giantCenter+1) (fun _ => logCellMass C.giantCenter deleted)) (he : 0 ≤ giantMixedError K δ C.giantCenter L deleted)
    (hmesh : meshWidth giant L ≤ 1)
    (hD : referenceDerivative C h k [true] ≤ F) (hA : referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l ≤ F)
    (hN : (Fintype.card (MixedGridIndex (C.giantCenter-1) (C.giantCenter+1) (meshWidth giant L) (fun _ : Unit => C.giantCenter-1) (fun _ => C.giantCenter+1) (fun _ => meshWidth giant L)) : ℝ) ≤ J) (hS : (∑z : ZMod M, ∑u : Unit → (ZMod M)ˣ, ‖mixedResidueTest (residueTransform d) (frequencyBound Bs BD Bz k₀ L) outside h k M hd z u‖) ≤ Q)
    (hdel : (Real.exp 1+1)*deletionCap C.giantCenter deleted*((outside.prod:ℝ)^(2^(l+1))*(referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l)) ≤ r)
    (hvar : meshWidth giant L*Q*F*(mixedPrincipalMass M (C.giantCenter-1) (C.giantCenter+1) C.giantCenter smoothPartition (fun _ : Unit => C.giantCenter-1) (fun _ => C.giantCenter+1) (fun _ => logCellMass C.giantCenter deleted)) ≤ r)
    (hgrid : J*Q*F*(giantMixedError K δ C.giantCenter L deleted) ≤ r) :
    mixedErrorUpper C h k outside deleted M hd K δ ≤ 8*r := by
  have hz := replacement_error_algebra ((Real.exp 1+1)*deletionCap C.giantCenter deleted*((outside.prod:ℝ)^(2^(l+1))*(referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l))) (referenceDerivative C h k [true]) (referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l) (meshWidth giant L)
    (mixedPrincipalMass M (C.giantCenter-1) (C.giantCenter+1) C.giantCenter smoothPartition (fun _ : Unit => C.giantCenter-1) (fun _ => C.giantCenter+1) (fun _ => logCellMass C.giantCenter deleted)) (Fintype.card (MixedGridIndex (C.giantCenter-1) (C.giantCenter+1) (meshWidth giant L) (fun _ : Unit => C.giantCenter-1) (fun _ => C.giantCenter+1) (fun _ => meshWidth giant L)) : ℝ) (∑z : ZMod M, ∑u : Unit → (ZMod M)ˣ, ‖mixedResidueTest (residueTransform d) (frequencyBound Bs BD Bz k₀ L) outside h k M hd z u‖) F J Q (giantMixedError K δ C.giantCenter L deleted) 1 r
    (referenceDerivative_nonneg C h k _) (referenceAmplitude_nonneg Bs L k₀ l)
    (Real.exp_nonneg _) hmass (by positivity) (by positivity) hF hJ hQ he
    (by norm_num) hmesh hD hA hN hS hdel hvar hgrid
  simpa only [mixedErrorUpper, one_mul, show (5+3*(1:ℝ))=8 by norm_num] using hz

end Ostmann.Arithmetic.HistoryGiantXiReplacementActual

end

end OAI
