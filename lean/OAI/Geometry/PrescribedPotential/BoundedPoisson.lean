import Mathlib
import OAI.Geometry.PrescribedPotential.ConstantProjection
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.NormalizedPoisson

namespace OAI

/-! Bounded Poisson. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
namespace LinearNormalization
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

def coefficient (C : ℂ →L[ℝ] H) (hC : Function.Injective C) (P : H →L[ℝ] H)
    (hP : ∀ u, P u ∈ (C : ℂ →ₗ[ℝ] H).range) : H →L[ℝ] ℂ := by
  let S := (C : ℂ →ₗ[ℝ] H).range
  letI : FiniteDimensional ℝ S := LinearMap.finiteDimensional_range _
  let e : ℂ ≃ₗ[ℝ] S := LinearEquiv.ofInjective (C : ℂ →ₗ[ℝ] H) hC
  let l : S →L[ℝ] ℂ := LinearMap.toContinuousLinearMap e.symm.toLinearMap
  exact l ∘L P.codRestrict S hP

lemma coefficient_spec (C : ℂ →L[ℝ] H) (hC : Function.Injective C) (P : H →L[ℝ] H)
    (hP : ∀ u, P u ∈ (C : ℂ →ₗ[ℝ] H).range) (u : H) :
    C (coefficient C hC P hP u) = P u :=
  LinearEquiv.ofInjective_symm_apply (C : ℂ →ₗ[ℝ] H) (h := hC) ⟨P u, hP u⟩

end LinearNormalization
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace Localizers
variable (D : Localizers A ι)

def constantsOrder (s : ℝ) : ℂ →L[ℝ] D.Sobolev s :=
  LinearMap.toContinuousLinearMap ((D.embed s).comp Smooth.constLinear)

omit [ConnectedSpace X] in
@[simp] lemma constantsOrder_apply (s : ℝ) (c : ℂ) :
    D.constantsOrder s c = D.embed s (Smooth.const c) := rfl

lemma constants_injective : Function.Injective D.constants := by
  intro c e h
  have hh := D.embed_injective 0 h
  let x : X := Classical.arbitrary X
  exact congrArg (fun u : Smooth A => u x) hh

variable {D}

 
def ConstantProjection.coefficient (P : D.ConstantProjection) : D.Sobolev 0 →L[ℝ] ℂ :=
  LinearNormalization.coefficient D.constants D.constants_injective P.proj (by
    intro u
    obtain ⟨c, hc⟩ := P.value u
    exact ⟨c, hc.symm⟩)

lemma ConstantProjection.coefficient_spec (P : D.ConstantProjection) (u : D.Sobolev 0) :
    D.constants (P.coefficient u) = P.proj u :=
  LinearNormalization.coefficient_spec _ _ _ _ u

lemma ConstantProjection.coefficient_constants (P : D.ConstantProjection) (c : ℂ) :
    P.coefficient (D.constants c) = c := by
  apply D.constants_injective
  rw [P.coefficient_spec]
  exact P.fixed c

end Localizers
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma fredholm_injective (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) :
    Function.Injective (1 - D.fredholmOperator m hm he P :
      D.localizers.Sobolev 0 →L[ℝ] D.localizers.Sobolev 0) := by
  intro u v huv
  have hz : (1 - D.fredholmOperator m hm he P) (u-v) = 0 := by
    rw [map_sub, huv, sub_self]
  have hh : D.fredholmOperator m hm he P (u-v) = u-v := by
    exact (sub_eq_zero.mp hz).symm
  exact sub_eq_zero.mp (D.fredholm_kernel m hm he P (u-v) hh)

def fredholmEquiv (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) :
    D.localizers.Sobolev 0 ≃L[ℝ] D.localizers.Sobolev 0 :=
  ContinuousLinearEquiv.ofBijective (1 - D.fredholmOperator m hm he P)
    (LinearMap.ker_eq_bot.mpr (D.fredholm_injective m hm he P))
    (LinearMap.range_eq_top.mpr (D.fredholm_surjective m hm he P))

@[simp] lemma fredholmEquiv_apply (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (u : D.localizers.Sobolev 0) :
    D.fredholmEquiv m hm he P u =
      u - ((m^2 : ℝ) • D.resolventZero m hm he u - P.proj u) := rfl

def poissonInput (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) : D.localizers.Sobolev 0 →L[ℝ] D.localizers.Sobolev 0 :=
  - (D.fredholmEquiv m hm he P).symm.toContinuousLinearMap

lemma poissonInput_equation (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (f : D.localizers.Sobolev 0) :
    D.poissonInput m hm he P f = -f - P.proj (D.poissonInput m hm he P f) +
      (m^2 : ℝ) • D.resolventZero m hm he (D.poissonInput m hm he P f) := by
  have h : D.fredholmEquiv m hm he P (D.poissonInput m hm he P f) = -f := by
    change D.fredholmEquiv m hm he P (- (D.fredholmEquiv m hm he P).symm f) = -f
    rw [map_neg, ContinuousLinearEquiv.apply_symm_apply]
  rw [D.fredholmEquiv_apply] at h
  calc
    _ = -f + ((m^2 : ℝ) • D.resolventZero m hm he (D.poissonInput m hm he P f) -
      P.proj (D.poissonInput m hm he P f)) := sub_eq_iff_eq_add.mp h
    _ = _ := by abel

def poissonRaw (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) : D.localizers.Sobolev 0 →L[ℝ] D.localizers.Sobolev 2 :=
  D.completedResolvent m hm he ∘L D.poissonInput m hm he P

def poissonResidue (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) : D.localizers.Sobolev 0 →L[ℝ] ℂ :=
  P.coefficient ∘L D.poissonInput m hm he P

lemma poissonRaw_equation (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (f : D.localizers.Sobolev 0) :
    D.completedL (D.poissonRaw m hm he P f) = f + D.localizers.constants (D.poissonResidue m hm he P f) := by
  have h := D.completedResolvent_equation m hm he (D.poissonInput m hm he P f)
  have hw := D.poissonInput_equation m hm he P f
  change (m^2 : ℝ) • D.resolventZero m hm he (D.poissonInput m hm he P f) -
    D.completedL (D.poissonRaw m hm he P f) = D.poissonInput m hm he P f at h
  change _ = f + D.localizers.constants (P.coefficient (D.poissonInput m hm he P f))
  rw [P.coefficient_spec]
  have hh := h.trans hw
  apply sub_right_inj.mp
  calc
    (m^2 : ℝ) • D.resolventZero m hm he (D.poissonInput m hm he P f) -
        D.completedL (D.poissonRaw m hm he P f) = _ := hh
    _ = (m^2 : ℝ) • D.resolventZero m hm he (D.poissonInput m hm he P f) -
        (f + P.proj (D.poissonInput m hm he P f)) := by abel

end GluingData
end GlobalElliptic

end
end

end OAI
