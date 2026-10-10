import Mathlib
import OAI.Analysis.SymmetricDomains.GoodNashBoundary

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical

noncomputable def normalParameterInjection (r k : ℕ) :
    (Fin k → ℝ) →L[ℝ] (Fin ((r+r)+k) → ℝ) :=
  LinearMap.toContinuousLinearMap
  { toFun := fun x j => Sum.elim (fun _ => 0) x (finSumFinEquiv.symm j)
    map_add' := by
      intro x y
      funext j
      cases h : finSumFinEquiv.symm j <;> simp [h]
    map_smul' := by
      intro a x
      funext j
      cases h : finSumFinEquiv.symm j <;> simp [h] }

lemma normalParameterInjection_norm_le (r k : ℕ) (x : Fin k → ℝ) :
    ‖normalParameterInjection r k x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  change ‖Sum.elim (fun _ => (0:ℝ)) x (finSumFinEquiv.symm j)‖ ≤ ‖x‖
  cases h : finSumFinEquiv.symm j with
  | inl a => simpa only [Sum.elim_inl,norm_zero] using norm_nonneg x
  | inr a => exact norm_le_pi_norm x a

lemma normalParameterInjection_opNorm (r k : ℕ) : ‖normalParameterInjection r k‖ ≤ 1 :=
  (normalParameterInjection r k).opNorm_le_bound zero_le_one (by
    intro x
    simpa only [one_mul] using normalParameterInjection_norm_le r k x)

lemma complexGraphRealEquiv_normal {r k : ℕ} (w : Affine k) :
    complexGraphRealEquiv r k (0,w) =
      (normalParameterInjection r k (fun j => (w j).re),fun j => (w j).im) := by
  apply Prod.ext
  · funext j
    change Sum.elim (complexRealEquiv r 0) (fun j => (w j).re) (finSumFinEquiv.symm j) = _
    simp only [map_zero]
    rfl
  · rfl

lemma ProjectionNashChart.coordinateDomain_isOpen {N m s k : ℕ}
    {V U : Set (Affine N)} {p : Affine N} (c : ProjectionNashChart V p m)
    (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
    (e : Affine m ≃L[ℝ] ((Fin s → ℝ) × (Fin k → ℝ))) :
    IsOpen (c.coordinateDomain U e) := by
  obtain ⟨O,hO,he⟩ := isOpen_induced_iff.mp hU
  let S := {z : Affine m | ‖complexRealEquiv m z‖ < c.radius}
  have hS : IsOpen S := isOpen_lt (complexRealEquiv m).continuous.norm continuous_const
  have hopen : IsOpen (S ∩ c.inverse ⁻¹' O) :=
    c.inverse_analytic.continuousOn.isOpen_inter_preimage hS hO
  have hE : c.coordinateDomain U e = e.symm ⁻¹' (S ∩ c.inverse ⁻¹' O) := by
    ext z
    change (_ ∧ _) ↔ (_ ∧ _)
    constructor
    · rintro ⟨hz,hu⟩
      refine ⟨hz,?_⟩
      have hv := c.inverse_mem _ hz
      exact (Set.ext_iff.mp he ⟨_,hv⟩).mpr hu
    · rintro ⟨hz,hu⟩
      refine ⟨hz,?_⟩
      have hv := c.inverse_mem _ hz
      exact (Set.ext_iff.mp he ⟨_,hv⟩).mp hu
  rw [hE]
  exact hopen.preimage e.symm.continuous

namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

noncomputable def normalInjection (c : NashBoundaryChart (m := m) U V B q) :
    Affine c.normal.normalDim →L[ℂ] Affine m :=
  c.normal.coordinates.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ (Affine c.normal.tangentDim) (Affine c.normal.normalDim))

noncomputable def sliceLift (c : NashBoundaryChart (m := m) U V B q)
    (s : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ)
    (w : Affine c.normal.normalDim) : Affine m :=
  c.normal.realCoordinates.symm (s,c.normal.graph s)+c.normalInjection w

noncomputable def sliceParameter (c : NashBoundaryChart (m := m) U V B q)
    (s : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ)
    (x : Fin c.normal.normalDim → ℝ) : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ :=
  s+normalParameterInjection c.normal.tangentDim c.normal.normalDim x

noncomputable def sliceGraph (c : NashBoundaryChart (m := m) U V B q)
    (s : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ)
    (x : Fin c.normal.normalDim → ℝ) : Fin c.normal.normalDim → ℝ :=
  c.normal.graph (c.sliceParameter s x)-c.normal.graph s

noncomputable def sliceDomain (c : NashBoundaryChart (m := m) U V B q)
    (s : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) : Set (Affine c.normal.normalDim) :=
  {w | c.normal.realCoordinates (c.sliceLift s w) ∈ c.chart.coordinateDomain U c.normal.realCoordinates}

lemma sliceLift_analytic (c : NashBoundaryChart (m := m) U V B q) (s) :
    AnalyticOnNhd ℂ (c.sliceLift s) univ := by
  intro w _
  exact analyticAt_const.add (c.normalInjection.analyticAt w)

lemma sliceParameter_zero (c : NashBoundaryChart (m := m) U V B q) (s) :
    c.sliceParameter s 0 = s := by simp only [sliceParameter,map_zero,add_zero]

lemma sliceGraph_zero (c : NashBoundaryChart (m := m) U V B q) (s) :
    c.sliceGraph s 0 = 0 := by simp only [sliceGraph,sliceParameter_zero,sub_self]

lemma slice_real_coordinates (c : NashBoundaryChart (m := m) U V B q) (s)
    (w : Affine c.normal.normalDim) :
    c.normal.realCoordinates (c.sliceLift s w) =
      (c.sliceParameter s (fun j => (w j).re),c.normal.graph s+(fun j => (w j).im)) := by
  rw [sliceLift,map_add,c.normal.realCoordinates.apply_symm_apply]
  have h : c.normal.realCoordinates (c.normalInjection w) =
      (normalParameterInjection c.normal.tangentDim c.normal.normalDim (fun j => (w j).re),fun j => (w j).im) := by
    change complexGraphRealEquiv _ _ (c.normal.coordinates (c.normal.coordinates.symm (0,w))) = _
    rw [c.normal.coordinates.apply_symm_apply]
    exact complexGraphRealEquiv_normal w
  rw [h]
  rfl

lemma sliceDomain_isOpen (c : NashBoundaryChart (m := m) U V B q)
    (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U)) (s) : IsOpen (c.sliceDomain s) := by
  exact (c.chart.coordinateDomain_isOpen hU c.normal.realCoordinates).preimage
    (c.normal.realCoordinates.continuous.comp ((continuous_const.add c.normalInjection.continuous)))

lemma sliceGraph_analytic (c : NashBoundaryChart (m := m) U V B q) {s}
    (hs : s ∈ ball 0 c.graphRadius) : AnalyticAt ℝ (c.sliceGraph s) 0 := by
  have ha : AnalyticAt ℝ (c.sliceParameter s) 0 :=
    analyticAt_const.add ((normalParameterInjection _ _).analyticAt 0)
  have hg : AnalyticAt ℝ c.normal.graph (c.sliceParameter s 0) := by
    rw [c.sliceParameter_zero]
    exact c.normal.graph_analytic s (ball_subset_ball c.graphRadius_le hs)
  exact (hg.comp ha).sub analyticAt_const

lemma sliceGraph_derivative_bound (c : NashBoundaryChart (m := m) U V B q) {s}
    (hs : s ∈ ball 0 c.graphRadius) :
    ‖fderiv ℝ (c.sliceGraph s) 0‖ ≤ ‖fderiv ℝ c.normal.graph s‖ := by
  have hp : HasFDerivAt (c.sliceParameter s)
      (normalParameterInjection c.normal.tangentDim c.normal.normalDim) 0 :=
    ((normalParameterInjection _ _).hasFDerivAt).const_add s
  have hg := (c.normal.graph_analytic s (ball_subset_ball c.graphRadius_le hs)).differentiableAt.hasFDerivAt
  rw [← c.sliceParameter_zero s] at hg
  have hd := (hg.comp 0 hp).sub_const (c.normal.graph s)
  change HasFDerivAt (c.sliceGraph s) _ _ at hd
  rw [hd.fderiv]
  simp only [sliceParameter_zero]
  calc
    _ ≤ ‖fderiv ℝ c.normal.graph s‖ *
        ‖normalParameterInjection c.normal.tangentDim c.normal.normalDim‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ c.normal.graph s‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (normalParameterInjection_opNorm c.normal.tangentDim c.normal.normalDim)
        (norm_nonneg _)
    _ = ‖fderiv ℝ c.normal.graph s‖ := mul_one _
end NashBoundaryChart
end Release061

end

end OAI
