import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExtensionSemisimpleCentralizer
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleInnerCentralizer

namespace OAI

/-! # The actual kernel inside a semisimple centralizer -/

noncomputable section
namespace PolycyclicRecognition
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]

theorem extension_semisimple_centralizer_kernel (E : GroupExtension L G Q)
    (S : L ≃ₗ⁅ℝ⁆ L) (hS : Module.End.IsSemisimple S.toLinearMap) (x : L) :
    E.inl x ∈ semisimpleActionCentralizer E S ↔
      ∃ z y : L, z ∈ Subgroup.center L ∧ S y = y ∧ x = z * y := by
  rw [← semisimple_inner_centralizer_iff S hS x]
  change E.conjAct (E.inl x) ∈
    Subgroup.centralizer {PolynomialExponentialCoordinates.groupAutomorphism (P := C) S} ↔ _
  rw [extension_conjAct_inl, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply LinearMap.ext
    intro y
    have hh := congrArg (fun f : MulAut L => f y) h
    change x * S y * x⁻¹ = S (x * y * x⁻¹) at hh
    change S (polynomialInnerLieEquiv x y) = polynomialInnerLieEquiv x (S y)
    simpa only [polynomialInnerLieEquiv_apply] using hh.symm
  · intro h
    apply DFunLike.ext
    intro y
    have hh : S (polynomialInnerLieEquiv x y) = polynomialInnerLieEquiv x (S y) :=
      LinearMap.congr_fun h.eq y
    change x * S y * x⁻¹ = S (x * y * x⁻¹)
    simpa only [polynomialInnerLieEquiv_apply] using hh.symm

end PolycyclicRecognition

end

end OAI
