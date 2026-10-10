import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionIntegerBoundary
import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionMixedTuples
import OAI.NumberTheory.Ostmann.Arithmetic.MixedCellIntegralFreezingLog
import OAI.NumberTheory.Ostmann.Arithmetic.MixedCellJointReplacementAlgebra
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellAssignedReplacement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open scoped BigOperators
open MeasureTheory PrimeProgression PrimeCellReplacement PrimeCellFreezing MixedCellIntegralFreezing
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ} [NeZero M]

def mixedSmoothTestSum (NI : ℕ) (N : ι → ℕ) (M : ℕ) [NeZero M]
    (loI hiI G : ℝ) (φ : ℝ → ℝ) (lo hi Z : ι → ℝ)
    (F : ZMod M → (ι → (ZMod M)ˣ) → ℂ) (f : (Option ι → ℝ) → ℂ) : ℂ :=
  ∑ n ∈ IntegerCell.cellSupport NI loI hiI, ∑ p : PrimeCellTuple N lo hi,
    ((Real.exp (-G)*φ (Real.log n-G):ℝ):ℂ)*
      (∏ i, (((Z i*(p i).val)⁻¹:ℝ):ℂ))*
      jointUnitTest (F (n:ZMod M)) (fun i => ((p i).val:ZMod M))*
      f (Option.elim' (n:ℝ) (fun i => ((p i).val:ℝ)))

def mixedAssignedTestSum (NI : ℕ) (N : ι → ℕ) (M : ℕ) [NeZero M]
    (loI hiI ηI G : ℝ) (φ : ℝ → ℝ) (lo hi η Z : ι → ℝ)
    (j : MixedGridIndex loI hiI ηI lo hi η) (F : ZMod M → (ι → (ZMod M)ˣ) → ℂ) : ℂ :=
  ∑ n ∈ assignedIntegerSupport NI loI hiI ηI j.1,
    ((Real.exp (-G)*φ (Real.log n-G):ℝ):ℂ)*
      assignedJointComplexTestSum N M lo hi η Z j.2 (F (n:ZMod M))

def mixedSmoothAssignedTestSum (NI : ℕ) (N : ι → ℕ) (M : ℕ) [NeZero M]
    (loI hiI ηI G : ℝ) (φ : ℝ → ℝ) (lo hi η Z : ι → ℝ)
    (j : MixedGridIndex loI hiI ηI lo hi η) (F : ZMod M → (ι → (ZMod M)ˣ) → ℂ)
    (f : (Option ι → ℝ) → ℂ) : ℂ :=
  ∑ n ∈ assignedIntegerSupport NI loI hiI ηI j.1,
    ∑ p : AssignedPrimeTuple N lo hi η j.2,
      ((Real.exp (-G)*φ (Real.log n-G):ℝ):ℂ)*
        (assignedTupleWeight N lo hi η Z j.2 p:ℂ)*
        jointUnitTest (F (n:ZMod M)) (fun i => ((p i).val:ZMod M))*
        f (Option.elim' (n:ℝ) (fun i => ((p i).val:ℝ)))

def mixedAssignedAbsMass (NI : ℕ) (N : ι → ℕ) (M : ℕ) [NeZero M]
    (loI hiI ηI G : ℝ) (φ : ℝ → ℝ) (lo hi η Z : ι → ℝ)
    (j : MixedGridIndex loI hiI ηI lo hi η) (F : ZMod M → (ι → (ZMod M)ˣ) → ℂ) : ℝ :=
  ∑ n ∈ assignedIntegerSupport NI loI hiI ηI j.1,
    (Real.exp (-G)*φ (Real.log n-G))*assignedAbsMass N M lo hi η Z j.2 (F (n:ZMod M))

def mixedPrincipalMass (M : ℕ) (loI hiI G : ℝ) (φ : ℝ → ℝ) (lo hi Z : ι → ℝ) : ℝ :=
  mixedLogMass M loI hiI G φ (fun i => ((Nat.totient M:ℝ)*Z i)⁻¹) lo hi

def mixedPrincipalIntegral (M : ℕ) (loI hiI G : ℝ) (φ : ℝ → ℝ) (lo hi Z : ι → ℝ)
    (f : (Option ι → ℝ) → ℂ) : ℂ :=
  mixedLogIntegral M loI hiI G φ (fun i => ((Nat.totient M:ℝ)*Z i)⁻¹) lo hi
    (fun x => f (optionCoordinates x))

theorem mixedAssignedTestSum_eq_integer (NI : ℕ) (N : ι → ℕ)
    (loI hiI ηI G : ℝ) (φ : ℝ → ℝ) (lo hi η Z : ι → ℝ)
    (j : MixedGridIndex loI hiI ηI lo hi η) (F : ZMod M → (ι → (ZMod M)ˣ) → ℂ) :
    mixedAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j F =
      ∑ r : ZMod M, (assignedIntegerResidueMass NI M r loI hiI ηI G φ j.1:ℂ)*
        assignedJointComplexTestSum N M lo hi η Z j.2 (F r) := by
  unfold mixedAssignedTestSum
  rw [IntegerCell.sum_weighted_residueTest (assignedIntegerSupport NI loI hiI ηI j.1)
    (fun n : ℕ => ((Real.exp (-G)*φ (Real.log n-G):ℝ):ℂ))
    (fun r : ZMod M => assignedJointComplexTestSum N M lo hi η Z j.2 (F r))]
  simp only [assignedIntegerResidueMass,Complex.ofReal_sum]

theorem mixedAssignedAbsMass_cast (NI : ℕ) (N : ι → ℕ)
    (loI hiI ηI G : ℝ) (φ : ℝ → ℝ) (lo hi η Z : ι → ℝ)
    (j : MixedGridIndex loI hiI ηI lo hi η) (F : ZMod M → (ι → (ZMod M)ˣ) → ℂ) :
    (mixedAssignedAbsMass NI N M loI hiI ηI G φ lo hi η Z j F:ℂ) =
      mixedAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j (fun r u => (‖F r u‖:ℂ)) := by
  simp only [mixedAssignedAbsMass,mixedAssignedTestSum,Complex.ofReal_sum,
    Complex.ofReal_mul,assignedAbsMass_cast]

theorem mixedSmoothTestSum_eq_sum_assigned (NI : ℕ) (N : ι → ℕ)
    (loI hiI ηI G : ℝ) (φ : ℝ → ℝ) (lo hi η Z : ι → ℝ)
    (hI : loI ≤ hiI) (horder : ∀ i, lo i ≤ hi i)
    (F : ZMod M → (ι → (ZMod M)ˣ) → ℂ) (f : (Option ι → ℝ) → ℂ) :
    mixedSmoothTestSum NI N M loI hiI G φ lo hi Z F f =
      ∑ j : MixedGridIndex loI hiI ηI lo hi η,
        mixedSmoothAssignedTestSum NI N M loI hiI ηI G φ lo hi η Z j F f := by
  simpa only [mixedSmoothTestSum,mixedSmoothAssignedTestSum,assignedTupleWeight,
    Complex.ofReal_prod,mul_assoc] using
    sum_mixed_prior_eq_sum_assigned NI N loI hiI ηI G φ lo hi η Z hI horder
      (fun n p => jointUnitTest (F (n:ZMod M)) (fun i => (p i:ZMod M))*
        f (Option.elim' (n:ℝ) (fun i => (p i:ℝ))))

theorem mixedPrincipalMass_eq_sum_boxes (M : ℕ) (loI hiI ηI G : ℝ)
    (φ : ℝ → ℝ) (lo hi η Z : ι → ℝ) (hI : loI ≤ hiI)
    (horder : ∀ i, lo i ≤ hi i) (hφ : Continuous φ) (hlo : ∀ i, 0 < lo i) :
    mixedPrincipalMass M loI hiI G φ lo hi Z =
      ∑ j : MixedGridIndex loI hiI ηI lo hi η,
        mixedPrincipalMass M (gridPoint loI hiI ηI j.1.val)
          (gridPoint loI hiI ηI (j.1.val+1)) G φ (boxLower lo hi η j.2) (boxUpper lo hi η j.2) Z :=
  mixedLogMass_eq_sum_boxes M loI hiI ηI G φ _ lo hi η hI horder hφ hlo

theorem mixedPrincipalIntegral_eq_sum_boxes (M : ℕ) (loI hiI ηI G : ℝ)
    (φ : ℝ → ℝ) (lo hi η Z : ι → ℝ) (hI : loI ≤ hiI)
    (horder : ∀ i, lo i ≤ hi i) (hφ : Continuous φ) (hlo : ∀ i, 0 < lo i)
    (f : (Option ι → ℝ) → ℂ)
    (hf : ContinuousOn (fun z => f (fun i => Real.exp (z i)))
      (logRectangle (Option.elim' loI lo) (Option.elim' hiI hi))) :
    mixedPrincipalIntegral M loI hiI G φ lo hi Z f =
      ∑ j : MixedGridIndex loI hiI ηI lo hi η,
        mixedPrincipalIntegral M (gridPoint loI hiI ηI j.1.val)
          (gridPoint loI hiI ηI (j.1.val+1)) G φ (boxLower lo hi η j.2) (boxUpper lo hi η j.2) Z f := by
  apply integral_mixedRectangle_eq_sum_boxes loI hiI ηI lo hi η hI horder
  have hh : ContinuousOn (fun z => f (optionCoordinates (mixedExp z)))
      (mixedLogRectangle loI hiI lo hi) := by
    simp only [optionCoordinates_mixedExp]
    exact hf.comp continuous_optionCoordinates.continuousOn
      (fun z hz => (optionCoordinates_mem_logRectangle loI hiI lo hi).mpr hz)
  exact ((continuousOn_mixedLogDensity M loI hiI G φ _ lo hi hφ hlo).smul hh).integrableOn_compact
    (isCompact_mixedLogRectangle loI hiI lo hi)

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
