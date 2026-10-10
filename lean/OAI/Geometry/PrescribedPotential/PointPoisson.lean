import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalStrongEmbedding
import OAI.Geometry.PrescribedPotential.HigherMetricOperator
import OAI.Geometry.PrescribedPotential.HigherPoisson
import OAI.Geometry.PrescribedPotential.KaehlerClosedDerivatives
import OAI.Geometry.PrescribedPotential.PoissonEquivalence

namespace OAI

/-! Point Poisson. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

def pointEvaluation (s : ℝ) (x₀ : X) : D.localizers.Sobolev s →L[ℝ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℝ x₀) ∘L D.localizers.strong s

omit [ConnectedSpace X] in
lemma pointEvaluation_embed {s : ℝ} (hs : (Module.finrank ℝ (EC d) : ℝ) < 2*s)
    (x₀ : X) (f : Smooth A) : D.pointEvaluation s x₀ (D.localizers.embed s f) = f x₀ := by
  change D.localizers.strong s (D.localizers.embed s f) x₀ = _
  rw [D.localizers.strong_embed s hs]
  rfl

omit [ConnectedSpace X] in
lemma completedLOrder_constants (k : ℕ) (c : ℂ) :
    D.completedLOrder k (D.localizers.constantsOrder ((k : ℝ)+2) c) = 0 := by
  rw [Localizers.constantsOrder_apply, D.completedLOrder_embed, complexL_const, map_zero]

omit [ConnectedSpace X] in
lemma constantsOrder_lower {s t : ℝ} (hst : t ≤ s) (a : ℂ) :
    D.localizers.lower s t (D.localizers.constantsOrder s a) =
      D.localizers.constantsOrder t a := by
  change D.localizers.lower s t (D.localizers.embed s (Smooth.const a)) =
    D.localizers.embed t (Smooth.const a)
  exact D.localizers.lower_embed hst (Smooth.const a)

omit [ConnectedSpace X] in
lemma completedLOrder_to_constant (k : ℕ) (u : D.localizers.Sobolev ((k : ℝ)+2)) (c : ℂ)
    (hu : D.completedLOrder k u = D.localizers.constantsOrder (k : ℝ) c) :
    D.completedL (D.localizers.lower ((k : ℝ)+2) 2 u) = D.localizers.constants c := by
  have hh := congrArg (D.localizers.lower (k : ℝ) 0) hu
  rw [D.completedLOrder_lower, D.constantsOrder_lower (Nat.cast_nonneg k)] at hh
  exact hh

lemma completedLOrder_constant_kernel (m : ℝ) (hm : 1 ≤ m)
    (he : ‖D.completedError m hm‖ < 1) (k : ℕ)
    (u : D.localizers.Sobolev ((k : ℝ)+2)) (c : ℂ)
    (hu : D.completedLOrder k u = D.localizers.constantsOrder (k : ℝ) c) :
    ∃ a : ℂ, u = D.localizers.constantsOrder ((k : ℝ)+2) a ∧ c = 0 := by
  have hl : (2 : ℝ) ≤ (k : ℝ)+2 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  obtain ⟨a, ha, hc⟩ := D.completedL_constant_kernel m hm he
    (D.localizers.lower ((k : ℝ)+2) 2 u) c (D.completedLOrder_to_constant k u c hu)
  refine ⟨a, ?_, hc⟩
  apply D.localizers.lower_injective hl
  exact ha.trans (D.constantsOrder_lower hl a).symm

def rawPoissonOrder (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (k : ℕ) := (D.poissonRaw_order m hm he P k).choose

lemma rawPoissonOrder_equation (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (k : ℕ) (f : D.localizers.Sobolev (k : ℝ)) :
    D.completedLOrder k (D.rawPoissonOrder m hm he P k f) =
      f + D.localizers.constantsOrder (k : ℝ)
        (D.poissonResidue m hm he P (D.localizers.lower (k : ℝ) 0 f)) := by
  apply D.localizers.lower_injective (Nat.cast_nonneg k)
  rw [D.completedLOrder_lower, rawPoissonOrder, (D.poissonRaw_order m hm he P k).choose_spec,
    D.poissonRaw_equation, map_add, Localizers.constantsOrder_apply,
    D.localizers.lower_embed (Nat.cast_nonneg k)]
  rfl

def pointPoissonOrder (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (k : ℕ) (x₀ : X) :
    D.localizers.Sobolev (k : ℝ) →L[ℝ] D.localizers.Sobolev ((k : ℝ)+2) :=
  D.rawPoissonOrder m hm he P k - D.localizers.constantsOrder ((k : ℝ)+2) ∘L
    D.pointEvaluation ((k : ℝ)+2) x₀ ∘L D.rawPoissonOrder m hm he P k

lemma pointPoissonOrder_equation (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (k : ℕ) (x₀ : X)
    (f : D.localizers.Sobolev (k : ℝ)) :
    D.completedLOrder k (D.pointPoissonOrder m hm he P k x₀ f) =
      f + D.localizers.constantsOrder (k : ℝ)
        (D.poissonResidue m hm he P (D.localizers.lower (k : ℝ) 0 f)) := by
  simp only [pointPoissonOrder, _root_.sub_apply, ContinuousLinearMap.comp_apply,
    map_sub, D.completedLOrder_constants, sub_zero, D.rawPoissonOrder_equation]

lemma pointPoissonOrder_normalized (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (k : ℕ)
    (hk : (Module.finrank ℝ (EC d) : ℝ) < 2*((k : ℝ)+2)) (x₀ : X)
    (f : D.localizers.Sobolev (k : ℝ)) :
    D.pointEvaluation ((k : ℝ)+2) x₀ (D.pointPoissonOrder m hm he P k x₀ f) = 0 := by
  simp only [pointPoissonOrder, _root_.sub_apply, ContinuousLinearMap.comp_apply,
    map_sub, Localizers.constantsOrder_apply, D.pointEvaluation_embed hk]
  exact sub_self _

lemma pointPoissonOrder_unique (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (k : ℕ) (hk : (Module.finrank ℝ (EC d) : ℝ) < 2*((k : ℝ)+2)) (x₀ : X)
    (u v : D.localizers.Sobolev ((k : ℝ)+2)) (c e : ℂ)
    (huv : D.completedLOrder k u - D.localizers.constantsOrder (k : ℝ) c =
      D.completedLOrder k v - D.localizers.constantsOrder (k : ℝ) e)
    (hpt : D.pointEvaluation ((k : ℝ)+2) x₀ u = D.pointEvaluation ((k : ℝ)+2) x₀ v) :
    u = v ∧ c = e := by
  have hL : D.completedLOrder k (u-v) = D.localizers.constantsOrder (k : ℝ) (c-e) := by
    rw [map_sub, map_sub]
    calc
      _ = (D.completedLOrder k u - D.localizers.constantsOrder (k : ℝ) c) -
          (D.completedLOrder k v - D.localizers.constantsOrder (k : ℝ) e) +
          (D.localizers.constantsOrder (k : ℝ) c - D.localizers.constantsOrder (k : ℝ) e) := by abel
      _ = _ := by rw [huv, sub_self, zero_add]
  obtain ⟨a, ha, hc⟩ := D.completedLOrder_constant_kernel m hm he k (u-v) (c-e) hL
  have heval := congrArg (D.pointEvaluation ((k : ℝ)+2) x₀) ha
  rw [map_sub, hpt, sub_self, Localizers.constantsOrder_apply, D.pointEvaluation_embed hk] at heval
  have ha0 : a = 0 := heval.symm
  rw [ha0, map_zero] at ha
  exact ⟨sub_eq_zero.mp ha, sub_eq_zero.mp hc⟩
end GluingData
end GlobalElliptic

end
end

end OAI
