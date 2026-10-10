import OAI.GroupTheory.PolycyclicRecognition.Algebra.GroupExtensionFactorSystem
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorExtensionTopology

namespace OAI

/-! # Changing the section preserves the extension topology -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] factorExtensionTopology
variable {N Q : Type} [Group N] [Group Q] [TopologicalSpace N]
  [TopologicalSpace Q] [IsTopologicalGroup N] [DiscreteTopology Q]
  (R : NonabelianFactorSystem N Q)
  (σ : (FactorExtension.groupExtension R).Section) (hσ : σ 1 = 1)

omit [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [DiscreteTopology Q] in
private theorem section_coordinate_left (g : FactorExtension R) :
    GroupExtensionSection.coordinate (FactorExtension.groupExtension R) σ g =
      g.left * (σ g.right).left⁻¹ := by
  have h : FactorExtension.inl R
      (GroupExtensionSection.coordinate (FactorExtension.groupExtension R) σ g) *
      σ g.right = g := by
    have hi := GroupExtensionSection.inl_coordinate (FactorExtension.groupExtension R) σ g
    change FactorExtension.inl R _ = g * (σ g.right)⁻¹ at hi
    rw [hi, inv_mul_cancel_right]
  have hl := congrArg (fun x : FactorExtension R => x.left) h
  simp only [FactorExtension.mul_left, FactorExtension.inl, MonoidHom.coe_mk,
    OneHom.coe_mk, R.action_one, MulAut.one_apply, R.factor_one_left, mul_one] at hl
  exact (eq_mul_inv_iff_mul_eq).mpr hl

omit [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [DiscreteTopology Q] in
private theorem section_equiv_apply (g : FactorExtension R) :
    GroupExtensionSection.mulEquiv (FactorExtension.groupExtension R) σ hσ g =
      ⟨g.left * (σ g.right).left⁻¹, g.right⟩ := by
  apply (GroupExtensionSection.mulEquiv (FactorExtension.groupExtension R) σ hσ).symm.injective
  rw [MulEquiv.symm_apply_apply]
  change g = FactorExtension.inl R (g.left * (σ g.right).left⁻¹) * σ g.right
  rw [← section_coordinate_left R σ g]
  have hi := GroupExtensionSection.inl_coordinate (FactorExtension.groupExtension R) σ g
  change FactorExtension.inl R _ = g * (σ g.right)⁻¹ at hi
  rw [hi, inv_mul_cancel_right]

theorem sectionFactorEquiv_continuous :
    Continuous (GroupExtensionSection.mulEquiv (FactorExtension.groupExtension R) σ hσ) := by
  have hs : Continuous (fun q : Q => (σ q).left) := continuous_of_discreteTopology
  have h : Continuous (fun g : FactorExtension R =>
      (g.left * (σ g.right).left⁻¹, g.right)) :=
    ((continuous_factor_left R).mul (hs.comp (continuous_factor_right R)).inv).prodMk
      (continuous_factor_right R)
  apply continuous_induced_rng.mpr
  convert h using 1
  funext g
  rw [Function.comp_apply, section_equiv_apply R σ hσ g]
  rfl

theorem sectionFactorEquiv_symm_continuous :
    Continuous (GroupExtensionSection.mulEquiv (FactorExtension.groupExtension R) σ hσ).symm := by
  let T := GroupExtensionSection.factorSystem (FactorExtension.groupExtension R) σ hσ
  have hs : Continuous (fun q : Q => (σ q).left) := continuous_of_discreteTopology
  have h : Continuous (fun a : FactorExtension T =>
      (a.left * (σ a.right).left, a.right)) :=
    ((continuous_factor_left T).mul (hs.comp (continuous_factor_right T))).prodMk
      (continuous_factor_right T)
  apply continuous_induced_rng.mpr
  convert h using 1
  funext a
  change ((FactorExtension.inl R a.left * σ a.right).left,
    (FactorExtension.inl R a.left * σ a.right).right) = _
  have hr : (σ a.right).right = a.right := σ.rightHom_section a.right
  simp [FactorExtension.mul_left, FactorExtension.mul_right, FactorExtension.inl,
    R.action_one, R.factor_one_left, hr]

end PolycyclicRecognition

end

end OAI
