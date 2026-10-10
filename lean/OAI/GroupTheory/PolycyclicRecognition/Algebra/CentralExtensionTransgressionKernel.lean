import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralExtensionTransgression
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GroupExtensionFactorSystem
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FirstHomologyAbelianizationNaturality

namespace OAI

/-! # The transgression vanishes on homology lifted from the extension

The section coordinate gives an explicit coboundary after pullback to the
extension group. All maps below are maps on the actual bar complex.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {N G Q : Type} [CommGroup N] [Group G] [Group Q]
variable (E : GroupExtension N G Q) (hc : E.inl.range ≤ Subgroup.center G)

include hc in
theorem centralExtension_coordinate_mul (σ : E.Section) (g h : G) :
    GroupExtensionSection.coordinate E σ (g * h) =
      GroupExtensionSection.coordinate E σ g * GroupExtensionSection.coordinate E σ h *
        GroupExtensionSection.factor E σ (E.rightHom g) (E.rightHom h) := by
  apply E.inl_injective
  simp only [map_mul, GroupExtensionSection.inl_coordinate,
    GroupExtensionSection.inl_factor]
  have he : Commute (σ (E.rightHom g)) (h * (σ (E.rightHom h))⁻¹) := by
    rw [← GroupExtensionSection.inl_coordinate]
    exact Subgroup.mem_center_iff.mp (hc ⟨_, rfl⟩) _
  calc
    g * h * (σ (E.rightHom g * E.rightHom h))⁻¹ =
        g * (h * (σ (E.rightHom h))⁻¹) * σ (E.rightHom h) *
          (σ (E.rightHom g * E.rightHom h))⁻¹ := by group
    _ = g * ((σ (E.rightHom g))⁻¹ *
        (h * (σ (E.rightHom h))⁻¹) * σ (E.rightHom g)) *
          σ (E.rightHom h) * (σ (E.rightHom g * E.rightHom h))⁻¹ := by
      rw [he.inv_left.eq]
      group
    _ = _ := by group

include hc in
theorem centralExtensionTwoCocycle_pullback (σ : E.Section) (g h : G) :
    centralExtensionTwoCocycle E σ (E.rightHom g) (E.rightHom h) =
      Additive.ofMul (GroupExtensionSection.coordinate E σ (g * h)) -
        Additive.ofMul (GroupExtensionSection.coordinate E σ g) -
          Additive.ofMul (GroupExtensionSection.coordinate E σ h) := by
  have he : Additive.ofMul (GroupExtensionSection.coordinate E σ (g * h)) =
      Additive.ofMul (GroupExtensionSection.coordinate E σ g) +
        Additive.ofMul (GroupExtensionSection.coordinate E σ h) +
          centralExtensionTwoCocycle E σ (E.rightHom g) (E.rightHom h) :=
    congrArg Additive.ofMul (centralExtension_coordinate_mul E hc σ g h)
  rw [he]
  abel

def centralExtensionCoordinateChains (σ : E.Section) :
    (G →₀ ℤ) →ₗ[ℤ] Additive N :=
  Finsupp.linearCombination ℤ (fun g =>
    Additive.ofMul (GroupExtensionSection.coordinate E σ g))

include hc in
theorem centralExtensionTwoCocycle_chains_pullback (σ : E.Section)
    (z : (G × G) →₀ ℤ) :
    groupTwoCocycleChains (centralExtensionTwoCocycle E σ)
      (groupHomology.chainsMap₂ E.rightHom
        (groupIntegralTrivialCoefficientMap E.rightHom) z) =
      -centralExtensionCoordinateChains E σ
        (groupHomology.d₂₁ (integralTrivialCoefficient G) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw, neg_add]
  | single p n =>
    rcases p with ⟨g, h⟩
    rw [groupHomology.d₂₁_single]
    change groupTwoCocycleChains (centralExtensionTwoCocycle E σ)
      (groupHomology.chainsMap₂ E.rightHom
        (groupIntegralTrivialCoefficientMap E.rightHom) (Finsupp.single (g, h) n)) =
      -centralExtensionCoordinateChains E σ
        (Finsupp.single h n - Finsupp.single (g * h) n + Finsupp.single g n)
    have hm : groupHomology.chainsMap₂ E.rightHom
        (groupIntegralTrivialCoefficientMap E.rightHom) (Finsupp.single (g, h) n) =
        Finsupp.single (E.rightHom g, E.rightHom h) n := by
      simp [groupHomology.chainsMap₂, groupIntegralTrivialCoefficientMap]
    rw [hm]
    rw [groupTwoCocycleChains_single, centralExtensionTwoCocycle_pullback E hc]
    simp only [map_add, map_sub, centralExtensionCoordinateChains,
      Finsupp.linearCombination_single, smul_sub]
    abel

theorem centralExtensionTransgression_lift (σ : E.Section)
    (x : groupHomology.H2 (integralTrivialCoefficient G)) :
    centralExtensionTransgression E hc σ
      (groupHomology.map E.rightHom (groupIntegralTrivialCoefficientMap E.rightHom) 2 x) =
      0 := by
  induction x using groupHomology.H2_induction_on with
  | h z =>
    rw [groupHomology.H2π_comp_map_apply, centralExtensionTransgression_cycle]
    rw [groupHomology.coe_mapCycles₂, centralExtensionTwoCocycle_chains_pullback E hc]
    rw [z.property]
    simp

end PolycyclicRecognition

end

end OAI
