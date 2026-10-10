import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.FiniteCharts

namespace OAI

noncomputable section
open MeasureTheory
open scoped SchwartzMap Laplacian ENNReal
open scoped BigOperators
namespace TamingCompatibility.FiberCoordinates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) (k : ℕ)

def coordinates : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k → ι) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k → ι => ℝ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun a : Fin k → ι =>
      ContinuousAlternatingMap.apply ℝ E ℝ (fun i => b (a i)))

omit [Fintype ι] [DecidableEq ι] in
lemma coordinates_apply (α : E [⋀^Fin k]→L[ℝ] ℝ) (a : Fin k → ι) :
    coordinates b k α a = α (fun i => b (a i)) := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma coordinates_injective : Function.Injective (coordinates b k) := by
  intro α β h
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply b.ext_alternating
  intro a _
  exact congrArg (fun v : EuclideanSpace ℝ (Fin k → ι) => v a) h

def complexCoordinates : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℂ (Fin k → ι) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k → ι => ℂ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun a : Fin k → ι =>
      Complex.ofRealCLM ∘L ContinuousAlternatingMap.apply ℝ E ℝ (fun i => b (a i)))

omit [Fintype ι] [DecidableEq ι] in
lemma complexCoordinates_apply (α : E [⋀^Fin k]→L[ℝ] ℝ) (a : Fin k → ι) :
    complexCoordinates b k α a = (α (fun i => b (a i)) : ℂ) := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma complexCoordinates_injective : Function.Injective (complexCoordinates b k) := by
  intro α β h
  apply coordinates_injective b k
  ext a
  exact Complex.ofReal_injective (congrArg (fun v : EuclideanSpace ℂ (Fin k → ι) => v a) h)

end TamingCompatibility.FiberCoordinates
namespace TamingCompatibility.ManifoldLocalization
open MeasureTheory Set Function
open scoped Topology Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (k : ℕ)

abbrev CoordinateFiber (k : ℕ) := EuclideanSpace ℂ (Fin k → Fin (Module.finrank ℝ Space))

def formCoordinates : (Space [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] CoordinateFiber k :=
  FiberCoordinates.complexCoordinates (stdOrthonormalBasis ℝ Space).toBasis k

omit [T2Space X] in
def localizedLinear (p : A.centers) :
    ManifoldForms.smoothForms X k →ₗ[ℝ] 𝓢(Space,CoordinateFiber k) where
  toFun α := SchwartzMap.postcompCLM (formCoordinates k) (localizedSchwartz A p α.val α.property)
  map_add' α β := by
    apply SchwartzMap.ext
    intro y
    change formCoordinates k (localizedFunction A p (α.val + β.val) y) = _
    rw [localizedFunction_add]
    exact (formCoordinates k).map_add _ _
  map_smul' c α := by
    apply SchwartzMap.ext
    intro y
    change formCoordinates k (localizedFunction A p (c • α.val) y) = _
    rw [localizedFunction_smul]
    exact (formCoordinates k).map_smul _ _

abbrev ChartL2 := PiLp 2 (fun _ : A.centers => Lp (CoordinateFiber k) 2
  (volume : Measure Space))

omit [T2Space X] in
def localizeL2 : ManifoldForms.smoothForms X k →ₗ[ℝ] ChartL2 A k :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : A.centers => Lp (CoordinateFiber k) 2 (volume : Measure Space))).symm.toLinearMap ∘ₗ
  LinearMap.pi (fun p => (SchwartzMap.toLpCLM ℝ (CoordinateFiber k) 2 (volume : Measure Space)).toLinearMap ∘ₗ
    localizedLinear A k p)

omit [T2Space X] in
lemma localizeL2_apply (α : ManifoldForms.smoothForms X k) (p : A.centers) :
    localizeL2 A k α p = (localizedLinear A k p α).toLp 2 := rfl

omit [T2Space X] in
lemma localizeL2_injective : Function.Injective (localizeL2 A k) := by
  apply (injective_iff_map_eq_zero _).2
  intro α hα
  apply Subtype.ext
  apply eq_zero_of_localizedFunction_eq_zero A
  intro p
  have hp := congrArg (fun u : ChartL2 A k => u p) hα
  have hs : localizedLinear A k p α = 0 := SchwartzMap.injective_toLp 2 volume (by
    change (localizedLinear A k p α).toLp 2 = 0 at hp
    have hzero : (0 : 𝓢(Space,CoordinateFiber k)).toLp 2 = 0 :=
      (SchwartzMap.toLpCLM ℝ (CoordinateFiber k) 2 (volume : Measure Space)).map_zero
    exact hp.trans hzero.symm)
  funext y
  apply FiberCoordinates.complexCoordinates_injective (stdOrthonormalBasis ℝ Space).toBasis k
  have he := congrArg (fun f : 𝓢(Space,CoordinateFiber k) => f y) hs
  change formCoordinates k (localizedFunction A p α.val y) = 0 at he
  change formCoordinates k (localizedFunction A p α.val y) = formCoordinates k 0
  rwa [map_zero]

def globalL2 : Submodule ℝ (ChartL2 A k) :=
  (LinearMap.range (localizeL2 A k)).topologicalClosure

instance globalL2_complete : CompleteSpace (globalL2 A k) :=
  (LinearMap.range (localizeL2 A k)).isClosed_topologicalClosure.completeSpace_coe

omit [T2Space X] in
def smoothToL2 : ManifoldForms.smoothForms X k →ₗ[ℝ] globalL2 A k :=
  (localizeL2 A k).codRestrict _ (fun α => Submodule.le_topologicalClosure _ ⟨α,rfl⟩)

omit [T2Space X] in
lemma smoothToL2_injective : Function.Injective (smoothToL2 A k) := by
  intro α β h
  exact localizeL2_injective A k (congrArg Subtype.val h)

end TamingCompatibility.ManifoldLocalization

end

end OAI
