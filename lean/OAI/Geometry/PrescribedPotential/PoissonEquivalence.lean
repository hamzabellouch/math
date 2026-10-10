import Mathlib
import OAI.Geometry.PrescribedPotential.BoundedPoisson
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.ComplexKernel
import OAI.Geometry.PrescribedPotential.QuantitativeResolvent

namespace OAI

/-! Poisson Equivalence. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
lemma complexL_const (g : KaehlerMetric A) (c : ℂ) : complexL g (Smooth.const c) = 0 := by
  ext x
  obtain ⟨i, hi⟩ := A.covers x
  change complexLValue g (Smooth.const c) x = 0
  rw [complexLValue_local g _ i (by simpa using hi)]
  change localL g i (fun _ => c) (A.euclideanChart i x) = 0
  simp [localL]

namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

omit [ConnectedSpace X] in
lemma completedL_constants (c : ℂ) : D.completedL (D.localizers.constantsOrder 2 c) = 0 := by
  rw [Localizers.constantsOrder_apply]
  change D.localizers.extendCore 2 0 (complexL g) (D.localizers.embed 2 (Smooth.const c)) = 0
  rw [D.localizers.extendCore_embed D.complexL_bound, complexL_const, map_zero]

def poissonBounded (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) : D.localizers.Sobolev 0 →L[ℝ] D.localizers.Sobolev 2 :=
  D.poissonRaw m hm he P - D.localizers.constantsOrder 2 ∘L P.coefficient ∘L
    D.localizers.lower 2 0 ∘L D.poissonRaw m hm he P

lemma poissonBounded_equation (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (f : D.localizers.Sobolev 0) :
    D.completedL (D.poissonBounded m hm he P f) =
      f + D.localizers.constants (D.poissonResidue m hm he P f) := by
  simp only [poissonBounded, _root_.sub_apply, ContinuousLinearMap.comp_apply,
    map_sub, D.completedL_constants, sub_zero, D.poissonRaw_equation]

lemma poissonBounded_normalized (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (f : D.localizers.Sobolev 0) :
    P.coefficient (D.localizers.lower 2 0 (D.poissonBounded m hm he P f)) = 0 := by
  simp only [poissonBounded, _root_.sub_apply, ContinuousLinearMap.comp_apply,
    map_sub, Localizers.constantsOrder_apply,
    D.localizers.lower_embed (by norm_num : (0:ℝ) ≤ 2)]
  change _ - P.coefficient (D.localizers.constants _) = 0
  rw [P.coefficient_constants, sub_self]

lemma completedL_constant_kernel (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (u : D.localizers.Sobolev 2) (c : ℂ) (hu : D.completedL u = D.localizers.constants c) :
    ∃ a : ℂ, u = D.localizers.constantsOrder 2 a ∧ c = 0 := by
  let w := D.shiftedOperator m u
  have hr : D.resolventZero m hm he w = D.localizers.lower 2 0 u := by
    change D.localizers.lower 2 0 (D.completedResolvent m hm he (D.shiftedOperator m u)) = _
    rw [D.completedResolvent_left]
  have hw : w = D.localizers.embed 0 (-Smooth.const c) + (m^2 : ℝ) • D.resolventZero m hm he w := by
    rw [hr, map_neg]
    change (m^2 : ℝ) • D.localizers.lower 2 0 u - D.completedL u = _
    rw [hu]
    change _ - D.localizers.embed 0 (Smooth.const c) = _
    abel
  obtain ⟨v, hv⟩ := D.allRegular_smooth (D.resolvent_feedback_regular m hm he w _ hw)
  have hemb : D.localizers.embed 2 v = u := by
    apply D.localizers.lower_injective (by norm_num : (0:ℝ) ≤ 2)
    rw [D.localizers.lower_embed (by norm_num : (0:ℝ) ≤ 2), hv]
    exact hr
  have hl : complexL g v = Smooth.const c := by
    apply D.localizers.embed_injective 0
    change D.localizers.embed 0 (complexL g v) = D.localizers.constants c
    rw [← hu, ← hemb]
    exact (D.localizers.extendCore_embed D.complexL_bound v).symm
  have hc := complexL_constant_rhs_zero g v hl
  have hl0 : complexL g v = 0 := by rw [hl, hc]; rfl
  obtain ⟨a, ha⟩ := complexL_kernel g v hl0
  exact ⟨a, by rw [← hemb, ha]; rfl, hc⟩

 
def augmentedL (P : D.localizers.ConstantProjection) :
    (D.localizers.Sobolev 2 × ℂ) →L[ℝ] (D.localizers.Sobolev 0 × ℂ) :=
  ((D.completedL ∘L ContinuousLinearMap.fst ℝ _ _) -
    (D.localizers.constants ∘L ContinuousLinearMap.snd ℝ _ _)).prod
    (P.coefficient ∘L D.localizers.lower 2 0 ∘L ContinuousLinearMap.fst ℝ _ _)

lemma augmentedL_apply (P : D.localizers.ConstantProjection) (u : D.localizers.Sobolev 2) (c : ℂ) :
    D.augmentedL P (u,c) = (D.completedL u - D.localizers.constants c,
      P.coefficient (D.localizers.lower 2 0 u)) := rfl

lemma augmentedL_bijective (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) : Function.Bijective (D.augmentedL P) := by
  constructor
  · apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨u,c⟩ h
    have hl : D.completedL u = D.localizers.constants c := sub_eq_zero.mp (congrArg Prod.fst h)
    obtain ⟨a, ha, hc⟩ := D.completedL_constant_kernel m hm he u c hl
    have hn : P.coefficient (D.localizers.lower 2 0 u) = 0 := congrArg Prod.snd h
    rw [ha, Localizers.constantsOrder_apply, D.localizers.lower_embed (by norm_num : (0:ℝ) ≤ 2)] at hn
    change P.coefficient (D.localizers.constants a) = 0 at hn
    rw [P.coefficient_constants] at hn
    rw [ha, hn, map_zero, hc]
    rfl
  · rintro ⟨f,a⟩
    refine ⟨(D.poissonBounded m hm he P f + D.localizers.constantsOrder 2 a,
      D.poissonResidue m hm he P f), ?_⟩
    rw [D.augmentedL_apply]
    apply Prod.ext
    · rw [map_add, D.completedL_constants, add_zero, D.poissonBounded_equation, add_sub_cancel_right]
    · change P.coefficient (D.localizers.lower 2 0
        (D.poissonBounded m hm he P f + D.localizers.constantsOrder 2 a)) = a
      rw [map_add, map_add, D.poissonBounded_normalized, zero_add,
        Localizers.constantsOrder_apply, D.localizers.lower_embed (by norm_num : (0:ℝ) ≤ 2)]
      exact P.coefficient_constants a

 

def poissonEquiv (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) :
    (D.localizers.Sobolev 2 × ℂ) ≃L[ℝ] (D.localizers.Sobolev 0 × ℂ) :=
  ContinuousLinearEquiv.ofBijective (D.augmentedL P)
    (LinearMap.ker_eq_bot.mpr (D.augmentedL_bijective m hm he P).1)
    (LinearMap.range_eq_top.mpr (D.augmentedL_bijective m hm he P).2)

end GluingData
end GlobalElliptic

end
end

end OAI
