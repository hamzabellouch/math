import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPriorGrid
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellSmoothFreezing

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPriorGrid
open Construction PrimeProgression PrimeCellReplacement LogCellPartition
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem bulkClosedSupport_modulus_lt (L : ℝ) (M : ℕ)
    (hsize : (M : ℝ) < Real.exp (bulkLogLower L)) {p : ℕ}
    (hp : p ∈ bulkClosedSupport L) : M < p := by
  have hm := (mem_bulkClosedSupport L p).mp hp
  have he := Real.exp_le_exp.mpr hm.2.1
  rw [Real.exp_log (by exact_mod_cast hm.1.pos : (0 : ℝ) < p)] at he
  exact_mod_cast hsize.trans_le he

theorem bulkClosedSupport_coprime (L : ℝ) (M : ℕ) [NeZero M]
    (hsize : (M : ℝ) < Real.exp (bulkLogLower L)) {p : ℕ}
    (hp : p ∈ bulkClosedSupport L) : p.Coprime M :=
  Nat.coprime_of_lt_prime (NeZero.ne M) (bulkClosedSupport_modulus_lt L M hsize hp)
    ((mem_bulkClosedSupport L p).mp hp).1

def bulkPrimeUnit (L : ℝ) (M : ℕ) [NeZero M]
    (hsize : (M : ℝ) < Real.exp (bulkLogLower L)) (p : ℕ)
    (hp : p ∈ bulkClosedSupport L) : (ZMod M)ˣ :=
  ZMod.unitOfCoprime p (bulkClosedSupport_coprime L M hsize hp)

@[simp] theorem bulkPrimeUnit_coe (L : ℝ) (M : ℕ) [NeZero M]
    (hsize : (M : ℝ) < Real.exp (bulkLogLower L)) (p : ℕ)
    (hp : p ∈ bulkClosedSupport L) :
    (bulkPrimeUnit L M hsize p hp : ZMod M) = p := ZMod.coe_unitOfCoprime _ _

def bulkTupleUnits (L : ℝ) (M : ℕ) [NeZero M]
    (hsize : (M : ℝ) < Real.exp (bulkLogLower L)) (p : BulkPrimeTuple ι L) :
    ι → (ZMod M)ˣ := fun i => bulkPrimeUnit L M hsize (p i).val (p i).property

theorem jointUnitTest_bulkTuple (L : ℝ) (M : ℕ) [NeZero M]
    (hsize : (M : ℝ) < Real.exp (bulkLogLower L)) (F : (ι → (ZMod M)ˣ) → ℂ)
    (p : BulkPrimeTuple ι L) :
    jointUnitTest F (fun i => ((p i).val : ZMod M)) = F (bulkTupleUnits L M hsize p) := by
  have he : (fun i => (bulkTupleUnits L M hsize p i : ZMod M)) =
      fun i => ((p i).val : ZMod M) := by funext i; exact bulkPrimeUnit_coe _ _ _ _ _
  rw [← he, jointUnitTest_units]

def sourceBulkMean (L : ℝ) (E : Finset ℕ)
    (hZ : 0 < harmonicPrimeMass (bulkPrimeBand L E)) (M : ℕ) [NeZero M]
    (hsize : (M : ℝ) < Real.exp (bulkLogLower L))
    (F : (ι → (ZMod M)ˣ) → ℂ) (f : (ι → ℝ) → ℂ) : ℂ :=
  (bulkProductPrior (ι := ι) L E hZ).cmean (fun p =>
    F (fun i => bulkPrimeUnit L M hsize (p i).val (bulkPrimeBand_subset_closed L E (p i).property))*
      f (fun i => ((p i).val : ℝ)))

theorem sourceBulkMean_eq_jointUnitTest (L : ℝ) (E : Finset ℕ)
    (hZ : 0 < harmonicPrimeMass (bulkPrimeBand L E)) (M : ℕ) [NeZero M]
    (hsize : (M : ℝ) < Real.exp (bulkLogLower L))
    (F : (ι → (ZMod M)ˣ) → ℂ) (f : (ι → ℝ) → ℂ) :
    sourceBulkMean L E hZ M hsize F f =
      (bulkProductPrior (ι := ι) L E hZ).cmean (fun p =>
        jointUnitTest F (fun i => ((p i).val : ZMod M))*f (fun i => ((p i).val : ℝ))) := by
  unfold sourceBulkMean FinitePrior.cmean
  apply Finset.sum_congr rfl
  intro p hp
  have he : jointUnitTest F (fun i => ((p i).val : ZMod M)) =
      F (fun i => bulkPrimeUnit L M hsize (p i).val
        (bulkPrimeBand_subset_closed L E (p i).property)) :=
    jointUnitTest_bulkTuple L M hsize F
      (fun i => ⟨(p i).val, bulkPrimeBand_subset_closed L E (p i).property⟩)
  simp only [he]

theorem bulkGridMean_joint_eq_smoothJointTestSum (L : ℝ) (E : Finset ℕ)
    (M : ℕ) [NeZero M] (F : (ι → (ZMod M)ˣ) → ℂ) (f : (ι → ℝ) → ℂ) :
    bulkGridMean L E (fun p => jointUnitTest F (fun i => (p i : ZMod M))*f (fun i => (p i : ℝ))) =
      smoothJointTestSum (fun _ : ι => bulkPrimeCutoff L) M
        (fun _ => bulkLogLower L) (fun _ => bulkLogUpper L) (fun _ => bulkNormalizer L E) F f := by
  unfold bulkGridMean smoothJointTestSum
  apply Finset.sum_congr rfl
  intro p hp
  simp only [bulkTupleWeight, bulkWeight, tupleWeight, mul_assoc]

end Ostmann.Arithmetic.HistoryBulkPriorGrid

end

end OAI
