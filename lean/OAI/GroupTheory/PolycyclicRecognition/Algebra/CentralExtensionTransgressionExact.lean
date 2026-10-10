import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralExtensionTransgressionKernel
import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralBarNaturality
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralTransgressionSectionIndependence

namespace OAI

/-! # Exactness of the central transgression at the kernel group

The image in the central kernel is exactly the kernel of its map to the
abelianization of the extension group. The reverse containment is constructed
from an actual integral bar boundary.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {N G Q : Type} [CommGroup N] [Group G] [Group Q]
variable (E : GroupExtension N G Q) (hc : E.inl.range ≤ Subgroup.center G)

def centralExtensionAbelianizationMap : Additive N →ₗ[ℤ] Additive (Abelianization G) :=
  ((Abelianization.of : G →* Abelianization G).comp E.inl).toAdditive.toIntLinearMap

def centralExtensionSectionAbelianChains (σ : E.Section) :
    (Q →₀ ℤ) →ₗ[ℤ] Additive (Abelianization G) :=
  Finsupp.linearCombination ℤ (fun q => Additive.ofMul (Abelianization.of (σ q)))

theorem centralExtensionAbelianization_cocycle (σ : E.Section) (q r : Q) :
    centralExtensionAbelianizationMap E (centralExtensionTwoCocycle E σ q r) =
      Additive.ofMul (Abelianization.of (σ q)) +
        Additive.ofMul (Abelianization.of (σ r)) -
          Additive.ofMul (Abelianization.of (σ (q * r))) := by
  apply Additive.toMul.injective
  change Abelianization.of (E.inl (GroupExtensionSection.factor E σ q r)) =
    Abelianization.of (σ q) * Abelianization.of (σ r) /
      Abelianization.of (σ (q * r))
  simp only [GroupExtensionSection.inl_factor, map_mul, map_inv, div_eq_mul_inv]

theorem centralExtensionAbelianization_chains (σ : E.Section)
    (z : (Q × Q) →₀ ℤ) :
    centralExtensionAbelianizationMap E
      (groupTwoCocycleChains (centralExtensionTwoCocycle E σ) z) =
    centralExtensionSectionAbelianChains E σ
      (groupHomology.d₂₁ (integralTrivialCoefficient Q) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single p n =>
    rcases p with ⟨q, r⟩
    rw [groupTwoCocycleChains_single, map_smul,
      centralExtensionAbelianization_cocycle, groupHomology.d₂₁_single]
    change n • (Additive.ofMul (Abelianization.of (σ q)) +
        Additive.ofMul (Abelianization.of (σ r)) -
          Additive.ofMul (Abelianization.of (σ (q * r)))) =
      centralExtensionSectionAbelianChains E σ
        (Finsupp.single r n - Finsupp.single (q * r) n + Finsupp.single q n)
    simp only [map_add, map_sub, centralExtensionSectionAbelianChains,
      Finsupp.linearCombination_single, smul_sub, smul_add]
    abel

theorem centralExtensionTransgression_abelianization (σ : E.Section)
    (x : groupHomology.H2 (integralTrivialCoefficient Q)) :
    centralExtensionAbelianizationMap E (centralExtensionTransgression E hc σ x) = 0 := by
  induction x using groupHomology.H2_induction_on with
  | h z =>
    rw [centralExtensionTransgression_cycle, centralExtensionAbelianization_chains,
      z.property, map_zero]

theorem centralExtensionTransgression_exact (σ : E.Section) (hσ : σ 1 = 1) :
    LinearMap.range (centralExtensionTransgression E hc σ) =
      LinearMap.ker (centralExtensionAbelianizationMap E) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact centralExtensionTransgression_abelianization E hc σ x
  · intro n hn
    have hzero : groupHomology.H1π (integralTrivialCoefficient G)
        ((groupHomology.cycles₁IsoOfIsTrivial (integralTrivialCoefficient G)).inv
          (Finsupp.single (E.inl n.toMul) (1 : ℤ))) = 0 := by
      apply integralH1AbelianizationEquiv.injective
      rw [integralH1AbelianizationEquiv_single, one_smul, map_zero]
      exact hn
    obtain ⟨b, hb⟩ := (groupHomology.H1π_eq_zero_iff _).mp hzero
    have hb' : groupHomology.d₂₁ (integralTrivialCoefficient G) b =
        Finsupp.single (E.inl n.toMul) 1 := hb
    let z : groupHomology.cycles₂ (integralTrivialCoefficient Q) :=
      ⟨groupHomology.chainsMap₂ E.rightHom
          (groupIntegralTrivialCoefficientMap E.rightHom) b -
            Finsupp.single (1, 1) 1, by
        change groupHomology.d₂₁ (integralTrivialCoefficient Q) (_ - _) = 0
        rw [map_sub, integralBarMap_boundary, hb', integralBarMap₁_single,
          E.rightHom_inl, groupHomology.d₂₁_single_one_fst, sub_self]⟩
    refine ⟨-groupHomology.H2π (integralTrivialCoefficient Q) z, ?_⟩
    rw [map_neg, centralExtensionTransgression_cycle]
    change -(groupTwoCocycleChains (centralExtensionTwoCocycle E σ)
      (groupHomology.chainsMap₂ E.rightHom
        (groupIntegralTrivialCoefficientMap E.rightHom) b -
          Finsupp.single (1, 1) 1)) = n
    rw [map_sub, centralExtensionTwoCocycle_chains_pullback E hc, hb',
      groupTwoCocycleChains_single, one_smul]
    have hcoc : centralExtensionTwoCocycle E σ 1 1 = 0 := by
      exact congrArg Additive.ofMul (GroupExtensionSection.factor_one_left E σ hσ 1)
    have hcoord : GroupExtensionSection.coordinate E σ (E.inl n.toMul) = n.toMul := by
      simpa only [hσ, mul_one] using
        GroupExtensionSection.coordinate_inl_mul E σ n.toMul 1
    simp [centralExtensionCoordinateChains, hcoc, hcoord]

theorem centralExtensionTransgression_range (σ : E.Section) :
    LinearMap.range (centralExtensionTransgression E hc σ) =
      LinearMap.ker (centralExtensionAbelianizationMap E) := by
  rw [centralExtensionTransgression_section_independent E hc σ
    (normalizedExtensionSection E)]
  exact centralExtensionTransgression_exact E hc _ (normalizedExtensionSection_one E)

end PolycyclicRecognition

end

end OAI
