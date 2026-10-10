import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralTransgressionSectionIndependence
import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralBarNaturality

namespace OAI

/-! # Naturality of the central transgression

The two squares of a morphism of extensions suffice. No compatibility between
the arbitrarily chosen sections is required.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {N G Q N' G' Q' : Type}
  [CommGroup N] [Group G] [Group Q] [CommGroup N'] [Group G'] [Group Q']
variable (E : GroupExtension N G Q) (E' : GroupExtension N' G' Q')
  (hc' : E'.inl.range ≤ Subgroup.center G')
  (f : N →* N') (g : G →* G') (h : Q →* Q')
  (hl : ∀ n, g (E.inl n) = E'.inl (f n))
  (hr : ∀ a, E'.rightHom (g a) = h (E.rightHom a))

include hc' hl hr in
theorem centralExtension_cocycle_natural (σ : E.Section) (τ : E'.Section) (q r : Q) :
    f.toAdditive.toIntLinearMap (centralExtensionTwoCocycle E σ q r) =
      centralExtensionTwoCocycle E' τ (h q) (h r) +
        (Additive.ofMul (GroupExtensionSection.coordinate E' τ (g (σ q))) +
          Additive.ofMul (GroupExtensionSection.coordinate E' τ (g (σ r))) -
            Additive.ofMul (GroupExtensionSection.coordinate E' τ (g (σ (q * r))))) := by
  have he := centralExtension_coordinate_mul E' hc' τ (g (σ q)) (g (σ r))
  rw [← map_mul, GroupExtensionSection.section_mul E σ, map_mul, hl,
    centralExtension_coordinate_inl_mul, hr, hr,
    σ.rightHom_section, σ.rightHom_section] at he
  have he' : f.toAdditive.toIntLinearMap (centralExtensionTwoCocycle E σ q r) +
      Additive.ofMul (GroupExtensionSection.coordinate E' τ (g (σ (q * r)))) =
      Additive.ofMul (GroupExtensionSection.coordinate E' τ (g (σ q))) +
        Additive.ofMul (GroupExtensionSection.coordinate E' τ (g (σ r))) +
          centralExtensionTwoCocycle E' τ (h q) (h r) := congrArg Additive.ofMul he
  apply add_right_cancel (b := Additive.ofMul
    (GroupExtensionSection.coordinate E' τ (g (σ (q * r)))))
  rw [he']
  abel

include hc' hl hr in
theorem centralExtension_cocycle_natural_chains (σ : E.Section) (τ : E'.Section)
    (z : (Q × Q) →₀ ℤ) :
    f.toAdditive.toIntLinearMap (groupTwoCocycleChains (centralExtensionTwoCocycle E σ) z) =
      groupTwoCocycleChains (centralExtensionTwoCocycle E' τ)
        (groupHomology.chainsMap₂ h (groupIntegralTrivialCoefficientMap h) z) +
          groupOneCochainChains (fun q => Additive.ofMul
            (GroupExtensionSection.coordinate E' τ (g (σ q))))
            (groupHomology.d₂₁ (integralTrivialCoefficient Q) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]; abel
  | single p n =>
    rcases p with ⟨q, r⟩
    rw [groupTwoCocycleChains_single, map_smul,
      centralExtension_cocycle_natural E E' hc' f g h hl hr,
      integralBarMap₂_single, groupTwoCocycleChains_single, groupHomology.d₂₁_single]
    change n • (centralExtensionTwoCocycle E' τ (h q) (h r) +
      (Additive.ofMul (GroupExtensionSection.coordinate E' τ (g (σ q))) +
        Additive.ofMul (GroupExtensionSection.coordinate E' τ (g (σ r))) -
          Additive.ofMul (GroupExtensionSection.coordinate E' τ (g (σ (q * r)))))) =
      n • centralExtensionTwoCocycle E' τ (h q) (h r) +
        groupOneCochainChains (fun q => Additive.ofMul
          (GroupExtensionSection.coordinate E' τ (g (σ q))))
          (Finsupp.single r n - Finsupp.single (q * r) n + Finsupp.single q n)
    simp only [map_add, map_sub, groupOneCochainChains,
      Finsupp.linearCombination_single, smul_add, smul_sub]
    abel

include hl hr in
theorem centralExtensionTransgression_natural
    (hc : E.inl.range ≤ Subgroup.center G) (σ : E.Section) (τ : E'.Section)
    (x : groupHomology.H2 (integralTrivialCoefficient Q)) :
    f.toAdditive.toIntLinearMap (centralExtensionTransgression E hc σ x) =
      centralExtensionTransgression E' hc' τ
        (groupHomology.map h (groupIntegralTrivialCoefficientMap h) 2 x) := by
  induction x using groupHomology.H2_induction_on with
  | h z =>
    rw [groupHomology.H2π_comp_map_apply, centralExtensionTransgression_cycle,
      centralExtensionTransgression_cycle, groupHomology.coe_mapCycles₂,
      centralExtension_cocycle_natural_chains E E' hc' f g h hl hr,
      z.property, map_zero, add_zero]

end PolycyclicRecognition

end

end OAI
