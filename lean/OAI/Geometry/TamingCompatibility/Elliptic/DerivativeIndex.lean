import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.Coordinates

namespace OAI

noncomputable section
open MeasureTheory
open scoped SchwartzMap Laplacian ENNReal
open scoped BigOperators
namespace TamingCompatibility.ManifoldLocalization
open MeasureTheory Set Function LineDeriv
open scoped Topology Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (k : ℕ)

abbrev DerivativeIndex := Option (Fin (Module.finrank ℝ Space))
abbrev ChartH1 := PiLp 2 (fun _ : DerivativeIndex => ChartL2 A k)

def jetComponent (j : DerivativeIndex) :
    𝓢(Space,CoordinateFiber k) →L[ℝ] 𝓢(Space,CoordinateFiber k) :=
  match j with
  | none => ContinuousLinearMap.id ℝ _
  | some i => lineDerivOpCLM ℝ 𝓢(Space,CoordinateFiber k) (stdOrthonormalBasis ℝ Space i)

omit [T2Space X] in
def localizeH1 : ManifoldForms.smoothForms X k →ₗ[ℝ] ChartH1 A k :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : DerivativeIndex => ChartL2 A k)).symm.toLinearMap ∘ₗ
  LinearMap.pi (fun j =>
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : A.centers => Lp (CoordinateFiber k) 2 (volume : Measure Space))).symm.toLinearMap ∘ₗ
    LinearMap.pi (fun p =>
      (SchwartzMap.toLpCLM ℝ (CoordinateFiber k) 2 (volume : Measure Space)).toLinearMap ∘ₗ
      (jetComponent k j).toLinearMap ∘ₗ localizedLinear A k p))

omit [T2Space X] in
lemma localizeH1_apply (α : ManifoldForms.smoothForms X k) (j : DerivativeIndex) (p : A.centers) :
    localizeH1 A k α j p = (jetComponent k j (localizedLinear A k p α)).toLp 2 := rfl

omit [T2Space X] in
lemma localizeH1_none (α : ManifoldForms.smoothForms X k) :
    localizeH1 A k α none = localizeL2 A k α := rfl

def globalH1 : Submodule ℝ (ChartH1 A k) :=
  (LinearMap.range (localizeH1 A k)).topologicalClosure

instance globalH1_complete : CompleteSpace (globalH1 A k) :=
  (LinearMap.range (localizeH1 A k)).isClosed_topologicalClosure.completeSpace_coe

def zeroth : ChartH1 A k →L[ℝ] ChartL2 A k := PiLp.proj 2 _ none

omit [T2Space X] in
lemma zeroth_mem_globalL2 (u : globalH1 A k) : zeroth A k u.val ∈ globalL2 A k := by
  apply ((LinearMap.range (localizeH1 A k)).topologicalClosure_minimal
    (t := (globalL2 A k).comap (zeroth A k).toLinearMap) ?_ ?_) u.property
  · rintro _ ⟨α,rfl⟩
    exact Submodule.le_topologicalClosure _ ⟨α,rfl⟩
  · exact (LinearMap.range (localizeL2 A k)).isClosed_topologicalClosure.preimage
      (zeroth A k).continuous

def h1ToL2 : globalH1 A k →L[ℝ] globalL2 A k :=
  ((zeroth A k).comp (globalH1 A k).subtypeL).codRestrict _ (zeroth_mem_globalL2 A k)

def jetDistribution (j : DerivativeIndex) (p : A.centers) :
    ChartH1 A k →L[ℝ] 𝓢'(Space,CoordinateFiber k) :=
  (Lp.toTemperedDistributionCLM (CoordinateFiber k) (volume : Measure Space) 2).restrictScalars ℝ ∘L
    PiLp.proj 2 _ p ∘L PiLp.proj 2 _ j

omit [T2Space X] in
lemma jetDistribution_localize (α : ManifoldForms.smoothForms X k)
    (j : DerivativeIndex) (p : A.centers) :
    jetDistribution A k j p (localizeH1 A k α) =
      SchwartzMap.toTemperedDistributionCLM Space (CoordinateFiber k) volume
        (jetComponent k j (localizedLinear A k p α)) := by
  exact Lp.toTemperedDistribution_toLp_eq _

omit [T2Space X] in
lemma derivative_relation (u : globalH1 A k) (i : Fin (Module.finrank ℝ Space)) (p : A.centers) :
    lineDerivOpCLM ℝ 𝓢'(Space,CoordinateFiber k) (stdOrthonormalBasis ℝ Space i)
      (jetDistribution A k none p u.val) = jetDistribution A k (some i) p u.val := by
  let D := (lineDerivOpCLM ℝ 𝓢'(Space,CoordinateFiber k) (stdOrthonormalBasis ℝ Space i)) ∘L
    jetDistribution A k none p - jetDistribution A k (some i) p
  have hz : LinearMap.range (localizeH1 A k) ≤ LinearMap.ker D.toLinearMap := by
    rintro _ ⟨α,rfl⟩
    change lineDerivOpCLM ℝ 𝓢'(Space,CoordinateFiber k) (stdOrthonormalBasis ℝ Space i)
      (jetDistribution A k none p (localizeH1 A k α)) -
      jetDistribution A k (some i) p (localizeH1 A k α) = 0
    rw [sub_eq_zero, jetDistribution_localize, jetDistribution_localize]
    exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq _ _
  have h := (LinearMap.range (localizeH1 A k)).topologicalClosure_minimal hz D.isClosed_ker u.property
  exact sub_eq_zero.mp h

omit [T2Space X] in
lemma h1ToL2_injective : Function.Injective (h1ToL2 A k) := by
  apply (injective_iff_map_eq_zero _).2
  intro u hu
  have h0 : u.val none = 0 := congrArg Subtype.val hu
  apply Subtype.ext
  ext j : 1
  ext p : 1
  cases j with
  | none => exact congrArg (fun v : ChartL2 A k => v p) h0
  | some i =>
    have he := derivative_relation A k u i p
    have hz : jetDistribution A k none p u.val = 0 := by
      change Lp.toTemperedDistributionCLM (CoordinateFiber k) volume 2 (u.val none p) = 0
      rw [h0]
      exact (Lp.toTemperedDistributionCLM (CoordinateFiber k) volume 2).map_zero
    rw [hz, (lineDerivOpCLM ℝ 𝓢'(Space,CoordinateFiber k)
      (stdOrthonormalBasis ℝ Space i)).map_zero] at he
    have hinj : Function.Injective (Lp.toTemperedDistributionCLM (CoordinateFiber k)
        (volume : Measure Space) 2) :=
      LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot
    apply hinj
    exact he.symm.trans (Lp.toTemperedDistributionCLM (CoordinateFiber k) volume 2).map_zero.symm

end TamingCompatibility.ManifoldLocalization

end

end OAI
