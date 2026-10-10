import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentExtensionLangSplitting
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExtensionCentralizerKernel

namespace OAI

/-! # Semisimple centralizer reduction for the completed lattice extension -/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
open scoped Manifold ContDiff IsMulCommutative
variable {N G Q : Type} [Group N] [Group G] [Group Q]
  (C : NilpotentLatticeCoordinates N) (S : GroupExtension N G Q)
  (σ : S.Section) (hσ : σ 1 = 1)

theorem completedExtension_conjugation_smooth
    (g : FactorExtension (C.extensionFactorSystem S σ hσ)) :
    ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞
      ((FactorExtension.groupExtension (C.extensionFactorSystem S σ hσ)).conjAct g) := by
  rw [FactorExtension.conjugation_eq]
  exact ((contMDiff_conjugation g.left).of_le (by simp)).comp
    (C.extensionFactorSystem_smooth S σ hσ g.right)

/-- No fixed-point-free condition: the actual centralizer surjects onto the
whole original quotient, and its intersection with the kernel is explicit. -/
theorem completedExtension_semisimple_centralizer [IsMulCommutative Q] (q : Q) :
    ∃ T : C.carrier ≃ₗ⁅ℝ⁆ C.carrier, Module.End.IsSemisimple T.toLinearMap ∧
      Function.Surjective
        ((FactorExtension.groupExtension (C.extensionFactorSystem S σ hσ)).rightHom.comp
          (semisimpleActionCentralizer
            (FactorExtension.groupExtension (C.extensionFactorSystem S σ hσ)) T).subtype) ∧
      ∀ x : C.carrier,
        (FactorExtension.groupExtension (C.extensionFactorSystem S σ hσ)).inl x ∈
          semisimpleActionCentralizer
            (FactorExtension.groupExtension (C.extensionFactorSystem S σ hσ)) T ↔
        ∃ z y : C.carrier, z ∈ Subgroup.center C.carrier ∧ T y = y ∧ x = z * y := by
  let E := FactorExtension.groupExtension (C.extensionFactorSystem S σ hσ)
  let t : FactorExtension (C.extensionFactorSystem S σ hσ) := ⟨1, q⟩
  let hs := C.completedExtension_conjugation_smooth S σ hσ
  let A := polynomialModelLieEquiv (E.conjAct t) (hs t)
  obtain ⟨T, U, hT, hU, hTU, hA⟩ := real_lie_jordan_decomposition A
  refine ⟨T, hT, extension_semisimple_centralizer_surjective E hs t T U hT hU hTU hA, ?_⟩
  intro x
  exact extension_semisimple_centralizer_kernel E T hT x

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
