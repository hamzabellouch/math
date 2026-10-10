import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CentralCocycleHomology
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExtensionSectionFactor
import Mathlib.GroupTheory.Commutator.Basic

namespace OAI

/-! # The central extension transgression on actual second homology

Its value on the two-letter alternating cycle is exactly the commutator
of the two section lifts. No bilinearity or splitting of the extension
is assumed.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement IsMulCommutative
variable {N G Q : Type} [CommGroup N] [Group G] [Group Q]
variable (E : GroupExtension N G Q) (hc : E.inl.range ≤ Subgroup.center G)

include hc in
theorem centralExtension_conjAct_eq (g : G) (n : N) : E.conjAct g n = n := by
  apply E.inl_injective
  rw [E.inl_conjAct_comm]
  have hn : Commute g (E.inl n) := Subgroup.mem_center_iff.mp (hc ⟨n, rfl⟩) g
  rw [hn.eq, mul_inv_cancel_right]

def centralExtensionTwoCocycle (σ : E.Section) (q r : Q) : Additive N :=
  Additive.ofMul (GroupExtensionSection.factor E σ q r)

include hc in
theorem centralExtensionTwoCocycle_identity (σ : E.Section) (q r s : Q) :
    centralExtensionTwoCocycle E σ q r + centralExtensionTwoCocycle E σ (q * r) s =
      centralExtensionTwoCocycle E σ r s + centralExtensionTwoCocycle E σ q (r * s) := by
  have h := GroupExtensionSection.factor_cocycle E σ q r s
  rw [centralExtension_conjAct_eq E hc] at h
  exact congrArg Additive.ofMul h

def centralExtensionTransgression (σ : E.Section) :
    groupHomology.H2 (integralTrivialCoefficient Q) →ₗ[ℤ] Additive N :=
  groupTwoCocycleHomology (centralExtensionTwoCocycle E σ)
    (centralExtensionTwoCocycle_identity E hc σ)

theorem centralExtensionTransgression_cycle (σ : E.Section)
    (z : groupHomology.cycles₂ (integralTrivialCoefficient Q)) :
    centralExtensionTransgression E hc σ
      (groupHomology.H2π (integralTrivialCoefficient Q) z) =
      groupTwoCocycleChains (centralExtensionTwoCocycle E σ) z.val :=
  groupTwoCocycleHomology_π _ _ _

theorem centralExtensionTransgression_alternating [IsMulCommutative Q]
    (σ : E.Section) (q r : Q) :
    centralExtensionTransgression E hc σ
      (groupHomology.H2π (integralTrivialCoefficient Q) (antisymmetricBarCycle q r)) =
      centralExtensionTwoCocycle E σ q r - centralExtensionTwoCocycle E σ r q := by
  rw [centralExtensionTransgression_cycle]
  change groupTwoCocycleChains (centralExtensionTwoCocycle E σ)
    (Finsupp.single (q, r) 1 - Finsupp.single (r, q) 1) = _
  rw [map_sub, groupTwoCocycleChains_single, groupTwoCocycleChains_single,
    one_smul, one_smul]

theorem centralExtensionTransgression_commutator [IsMulCommutative Q]
    (σ : E.Section) (q r : Q) :
    E.inl ((centralExtensionTransgression E hc σ
      (groupHomology.H2π (integralTrivialCoefficient Q) (antisymmetricBarCycle q r))).toMul) =
      ⁅σ q, σ r⁆ := by
  rw [centralExtensionTransgression_alternating]
  change E.inl (GroupExtensionSection.factor E σ q r /
    GroupExtensionSection.factor E σ r q) = _
  rw [div_eq_mul_inv, map_mul, map_inv, GroupExtensionSection.inl_factor,
    GroupExtensionSection.inl_factor]
  rw [mul_comm' r q]
  simp [commutatorElement_def, mul_assoc]

end PolycyclicRecognition

end

end OAI
