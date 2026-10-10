import OAI.NumberTheory.Ostmann.Construction.InitialEtaCRTBasic
import OAI.NumberTheory.Ostmann.Construction.InitialEtaStateProducts

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.InitialEta
open InitialCoordinatesTemplate

variable {giant bulk spectator : PrimeSource} {b s k : ℕ}
  {aux : AuxiliaryIndex k → PrimeSource}

theorem jointState_physicalProduct (d : Decomposition) (P : Finset ℕ)
    (x : JointSample giant bulk spectator aux b s) (freq n : ℤ) :
    statePhysicalProduct d P (jointState x freq) (jointOutside x) n =
      ∏i,tupleLocalTest d P i (tupleValues x i) (n:ZMod (tupleValues x i)) := by
  let f := fun q : ℕ => residueTest d q (n:ZMod q)
  let H := fun y : HalfListSample giant bulk spectator aux b s =>
    favorableGiantResidueTest d P y.1 (n:ZMod (y.1:ℕ)) *
      ((∏i,f (y.2.1 i)) * ((∏i,f (y.2.2.1 i)) * ∏i,f (y.2.2.2 i)))
  have hp : (∏i,tupleLocalTest d P i (tupleValues x i)
      (n:ZMod (tupleValues x i))) = H x.2 * H x.1 := by
    rw [Fintype.prod_prod_type,Fintype.prod_bool]
    simp only [H,Fintype.prod_sum_type,Fintype.prod_unique]
    rfl
  rw [hp]
  change favorableGiantResidueTest d P (jointState x freq).giantPlus _ *
    favorableGiantResidueTest d P (jointState x freq).giantMinus _ *
    ((jointState x freq).small.map (fun q => f q.value)).prod *
    ((jointOutside x).map f).prod = _
  rw [jointState_plus,jointState_minus,jointState_small_prod,jointOutside_prod]
  simp only [H,Fintype.prod_prod_type,Fintype.prod_sum_type,Fintype.prod_bool,
    tupleValues,tupleSample,tupleSource,halfSource,halfSample,smallPosition,halfAt,
    Bool.false_eq_true,ite_false,ite_true,Finset.prod_mul_distrib]
  ring

theorem tuplePhysical_eq_state (d : Decomposition) (P : Finset ℕ)
    (x : JointSample giant bulk spectator aux b s) (freq tb td : ℤ) (X : ℝ) :
    tuplePhysical d P giant bulk spectator aux b s tb td X x =
      (Arithmetic.sourceStateBins b s tb td (jointOutside x) (jointState x freq):ℂ) *
        (∑' n : ℤ,statePhysicalProduct d P (jointState x freq) (jointOutside x) n *
          SchwartzCutoff.psi ((n:ℝ)/X)) / (Real.sqrt X:ℂ) := by
  rw [tuplePhysical_eq,jointState_bins]
  simp only [jointState_physicalProduct]

end Ostmann.Construction.InitialEta

end

end OAI
