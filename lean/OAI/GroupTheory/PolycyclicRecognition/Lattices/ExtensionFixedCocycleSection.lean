import OAI.GroupTheory.PolycyclicRecognition.Geometry.CentralizerLiftJordanFactor
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleCocycleReduction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GaugeExtensionSection

namespace OAI

/-! # A section with semisimple-fixed factors in the original extension

Starting with an actual quotient lift, the semisimple centralizer still maps
onto the quotient. Its moving central cocycle is removed by the constructed
Lang correction, and the resulting section is returned in the original group.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q] [IsMulCommutative Q]

theorem extension_exists_semisimple_fixed_cocycle_section (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g))
    (t : G) (S U : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : (polynomialModelLieEquiv (E.conjAct t) (hsmooth t)).toLinearMap =
      S.toLinearMap * U.toLinearMap) :
    ∃ σ : E.Section, σ 1 = 1 ∧
      (∀ q, σ q ∈ semisimpleActionCentralizer E S) ∧
      ∀ q r, S (GroupExtensionSection.factor E σ q r) = GroupExtensionSection.factor E σ q r := by
  have hsurj := extension_semisimple_centralizer_surjective E hsmooth t S U hS hU hSU hA
  let D := semisimpleCentralizerExtension E S hsurj
  let σ := normalizedExtensionSection D
  have hσ : σ 1 = 1 := normalizedExtensionSection_one D
  let F := GroupExtensionSection.factorSystem D σ hσ
  let A := fun q => polynomialModelLieEquiv (E.conjAct (σ q : G)) (hsmooth (σ q))
  have hSA : ∀ q, Commute S.toLinearMap (A q).toLinearMap := by
    intro q
    exact (mem_semisimpleActionCentralizer_iff E S (σ q) (hsmooth (σ q))).mp (σ q).property
  have hact : ∀ q x, (F.action q x : L) = A q x := by
    intro q x
    change (D.conjAct (σ q) x : L) = A q x
    rw [semisimpleCentralizerExtension_conjAct]
    exact (polynomialModelLieEquiv_apply _ _ _).symm
  have ht : t ∈ semisimpleActionCentralizer E S := by
    apply (mem_semisimpleActionCentralizer_iff E S t (hsmooth t)).mpr
    rw [hA]
    exact (Commute.refl _).mul_right hSU
  obtain ⟨W, hW, hSW, he⟩ := centralizer_same_fiber_jordan_factor E hsmooth S U t
    (σ (E.rightHom t)) ht (σ _).property
    (σ.rightHom_section (E.rightHom t)) hU hSU hA
  obtain ⟨b, hb, hfixed⟩ := semisimple_cocycle_reduction S hS F A hSA hact
    (E.rightHom t) W hW hSW he
  let σb := GroupExtensionSection.gaugeSection D σ b
  let θ : E.Section :=
    { toFun q := (σb q : G)
      rightInverse_rightHom q := σb.rightHom_section q }
  refine ⟨θ, ?_, fun q => (σb q).property, ?_⟩
  · exact congrArg Subtype.val (GroupExtensionSection.gaugeSection_one D σ hσ b hb)
  · intro q r
    have hfactor : ((GroupExtensionSection.factor D σb q r : innerCentralizerLieSubalgebra S) : L) =
        GroupExtensionSection.factor E θ q r := by
      apply E.inl_injective
      have hh := congrArg Subtype.val (GroupExtensionSection.inl_factor D σb q r)
      change E.inl ((GroupExtensionSection.factor D σb q r : innerCentralizerLieSubalgebra S) : L) =
        (σb q : G) * (σb r : G) * (σb (q * r) : G)⁻¹ at hh
      exact hh.trans (GroupExtensionSection.inl_factor E θ q r).symm
    rw [← hfactor]
    have heq := GroupExtensionSection.factor_gaugeSection D σ hσ b hb q r
    change GroupExtensionSection.factor D σb q r = (F.gauge b hb).factor q r at heq
    rw [heq]
    exact hfixed q r

end PolycyclicRecognition

end

end OAI
