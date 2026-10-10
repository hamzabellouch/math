import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralExtensionTransgressionKernel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GroupCocycleCoboundary

namespace OAI

/-! # Independence of the section in the central transgression -/

noncomputable section
namespace PolycyclicRecognition
variable {N G Q : Type} [CommGroup N] [Group G] [Group Q]
variable (E : GroupExtension N G Q) (hc : E.inl.range ≤ Subgroup.center G)

theorem centralExtension_coordinate_inl_mul (σ : E.Section) (n : N) (g : G) :
    GroupExtensionSection.coordinate E σ (E.inl n * g) =
      n * GroupExtensionSection.coordinate E σ g := by
  apply E.inl_injective
  simp only [GroupExtensionSection.inl_coordinate, map_mul, E.rightHom_inl, one_mul]
  group

include hc in
theorem centralExtension_cocycle_change (σ τ : E.Section) (q r : Q) :
    centralExtensionTwoCocycle E σ q r = centralExtensionTwoCocycle E τ q r +
      (Additive.ofMul (GroupExtensionSection.coordinate E τ (σ q)) +
        Additive.ofMul (GroupExtensionSection.coordinate E τ (σ r)) -
          Additive.ofMul (GroupExtensionSection.coordinate E τ (σ (q * r)))) := by
  have he := centralExtension_coordinate_mul E hc τ (σ q) (σ r)
  rw [GroupExtensionSection.section_mul E σ,
    centralExtension_coordinate_inl_mul, σ.rightHom_section, σ.rightHom_section] at he
  have he' : centralExtensionTwoCocycle E σ q r +
      Additive.ofMul (GroupExtensionSection.coordinate E τ (σ (q * r))) =
      Additive.ofMul (GroupExtensionSection.coordinate E τ (σ q)) +
        Additive.ofMul (GroupExtensionSection.coordinate E τ (σ r)) +
          centralExtensionTwoCocycle E τ q r := congrArg Additive.ofMul he
  apply add_right_cancel (b := Additive.ofMul
    (GroupExtensionSection.coordinate E τ (σ (q * r))))
  rw [he']
  abel

theorem centralExtensionTransgression_section_independent (σ τ : E.Section) :
    centralExtensionTransgression E hc σ = centralExtensionTransgression E hc τ := by
  apply groupTwoCocycleHomology_eq_of_coboundary
    (centralExtensionTwoCocycle E σ) (centralExtensionTwoCocycle E τ)
    (centralExtensionTwoCocycle_identity E hc σ)
    (centralExtensionTwoCocycle_identity E hc τ)
    (fun q => Additive.ofMul (GroupExtensionSection.coordinate E τ (σ q)))
  exact centralExtension_cocycle_change E hc σ τ

end PolycyclicRecognition

end

end OAI
