import OAI.Algebra.AuslanderReiten.Duality.DualResolution
import OAI.Algebra.AuslanderReiten.Algebras.SimpleDual
import OAI.Algebra.AuslanderReiten.Duality.RightDualHomology

namespace OAI

noncomputable section
namespace ArExplicit.Resolution
open ArExplicit.Letter ArExplicit.BaseAlgebra
variable {k : Type*} [Field k] [CharP k 2] (q : k)
local notation "C" => BaseAlgebra k q

theorem exceptional_differential_comp : (leftEll q q).comp (leftEll q 1) = 0 := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change ell q q * (ell q 1 * (a : C)) = 0
  rw [← mul_assoc, show ell q q * ell q 1 = 0 by simpa using ell_successor_mul q 1, zero_mul]

abbrev ExceptionalHomology := RightDualHomology.Homology
  (leftEll q 1) (leftEll q q) (exceptional_differential_comp q)

def exceptionalCyclesMap (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    LinearMap.ker (leftEll q q) →ₗ[Cᵐᵒᵖ] Simple q where
  toFun a := (a.val : C).coeff v • generator q
  map_add' a b := add_smul _ _ _
  map_smul' c a := by
    change ((a.val : C) * c.unop).coeff v • generator q =
      c.unop.coeff f • ((a.val : C).coeff v • generator q)
    rw [exceptional_right_action q hq hq1 a.val a.property c.unop, mul_comm, mul_smul]

theorem exceptionalCyclesMap_surjective (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    Function.Surjective (exceptionalCyclesMap q hq hq1) := by
  intro s
  let r := simpleCoordinate q s
  refine ⟨⟨r • exceptionalCycle q, ?_⟩, ?_⟩
  · change leftEll q q (r • exceptionalCycle q) = 0
    rw [LinearMap.map_smul_of_tower, exceptionalCycle_closed]
    exact @smul_zero k (rightE q) inferInstance inferInstance r
  · change ((r • (exceptionalCycle q : C)).coeff v) • generator q = s
    simpa [exceptionalCycle, r] using (simple_expand q hq1 s).symm

theorem exceptionalCyclesMap_kernel (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    LinearMap.ker (exceptionalCyclesMap q hq hq1) =
      RightDualHomology.boundaries (leftEll q 1) (leftEll q q) (exceptional_differential_comp q) := by
  ext a
  constructor
  · intro ha
    have hv : (a.val : C).coeff v = 0 := by
      have hh := congrArg (simpleCoordinate q) ha
      change simpleCoordinate q ((a.val : C).coeff v • generator q) = simpleCoordinate q 0 at hh
      simpa using hh
    obtain ⟨b, hb⟩ := (exceptional_boundary_iff q hq hq1 a.val a.property).mpr hv
    exact ⟨b, Subtype.ext hb⟩
  · rintro ⟨b, hb⟩
    have he : leftEll q 1 b = a.val := congrArg Subtype.val hb
    have hv := (exceptional_boundary_iff q hq hq1 a.val a.property).mp ⟨b, he⟩
    change (a.val : C).coeff v • generator q = 0
    rw [hv, zero_smul]

def exceptionalHomologyEquiv (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    ExceptionalHomology q ≃ₗ[Cᵐᵒᵖ] Simple q :=
  (Submodule.quotEquivOfEq _ _ (exceptionalCyclesMap_kernel q hq hq1).symm).trans
    ((exceptionalCyclesMap q hq hq1).quotKerEquivOfSurjective
      (exceptionalCyclesMap_surjective q hq hq1))

def exceptionalDualHomologyEquiv (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    RightDualHomology.DualHomology (k := k) (leftEll q 1) (leftEll q q)
      (exceptional_differential_comp q) ≃ₗ[C] Simple q :=
  (RightDualHomology.dualHomologyEquiv _ _ _).symm.trans
    ((RightDual.congr (exceptionalHomologyEquiv q hq hq1)).symm.trans
      (rightSimpleDualEquiv q hq1))

end ArExplicit.Resolution

end

end OAI
