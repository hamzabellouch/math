import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveFrameBounds

namespace OAI

/-! First-derivative bounds for coefficient functionals in each overlapping
primitive chart, fixed before choosing any independent phases or radii. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance coefficientReadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance coefficientReadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance coefficientReadDualNormed : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadDualSpace : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadDerivativeNormed : NormedAddCommGroup
    (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadDerivativeSpace : NormedSpace ℝ
    (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadPairNormed : NormedAddCommGroup
    ((TensorFiber →L[ℝ] ℝ) × (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ)) := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance coefficientReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance coefficientReadDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance coefficientReadSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance coefficientReadSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

def coefficientFrameRead (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (i : B.centers) (a : B.centers × Fin 3) (y : JetPolynomial.Base) : TensorFiber →L[ℝ] ℝ :=
  B.coefficientFrame P i a ((chart (i : M)).symm y)

omit [CompactSpace M] in
lemma coefficientFrame_smoothAt
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (i : B.centers) (a : B.centers × Fin 3) {p : M}
    (hi : p ∈ (chart (i : M)).source) (ha : p ∈ (chart (a.1 : M)).source)
    (hQ : ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p)) :
    ContMDiffAt planeModel 𝓘(ℝ,TensorFiber →L[ℝ] ℝ) ∞ (B.coefficientFrame P i a) p := by
  have hq := hQ.contMDiffAt.comp p
    ((chart_smooth (a.1 : M) p ha).contMDiffAt ((chart (a.1 : M)).open_source.mem_nhds ha))
  have hT := (contMDiffOn_coordChangeL (IB := planeModel) (n := ∞)
    (B.tensorTriv i) (B.tensorTriv a.1)).contMDiffAt
    ((B.tensorTriv i).open_baseSet.inter (B.tensorTriv a.1).open_baseSet |>.mem_nhds
      ⟨B.tensorTriv_domain i hi,B.tensorTriv_domain a.1 ha⟩)
  have hconst : ContMDiffAt planeModel 𝓘(ℝ,TensorFiber →L[ℝ] PhaseMean.Tensor) ∞
      (fun _ : M => fiberToThree) p := contMDiffAt_const
  apply (hq.clm_comp (hconst.clm_comp hT)).congr_of_eventuallyEq
  filter_upwards [((chart (i : M)).open_source.inter (chart (a.1 : M)).open_source).mem_nhds
    ⟨hi,ha⟩] with q hq
  exact B.coefficientFrame_coordChange P i a hq.1 hq.2

omit [CompactSpace M] in
lemma coefficientFrameRead_smoothAt
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (i : B.centers) (a : B.centers × Fin 3) {p : M}
    (hi : p ∈ (chart (i : M)).source) (ha : p ∈ (chart (a.1 : M)).source)
    (hQ : ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p)) :
    ContDiffAt ℝ ∞ (B.coefficientFrameRead P i a) (chart (i : M) p) := by
  have hx := (chart (i : M)).map_source hi
  have hsym := ((chart_symm_smooth (i : M)) _ hx).contMDiffAt
    ((chart (i : M)).open_target.mem_nhds hx)
  have hout : ContMDiffAt planeModel 𝓘(ℝ,TensorFiber →L[ℝ] ℝ) ∞
      (B.coefficientFrame P i a) ((chart (i : M)).symm (chart (i : M) p)) := by
    rw [(chart (i : M)).left_inv hi]
    exact B.coefficientFrame_smoothAt P i a hi ha hQ
  have h := hout.comp (chart (i : M) p) hsym
  exact h.contDiffAt

 theorem coefficientFrameRead_C1_bound
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (hQ : ∀ (a : B.centers × Fin 3) p, p ∈ tsupport (B.weight a.1) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p)) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i a p,
      p ∈ tsupport (B.weight i) → p ∈ tsupport (B.weight a.1) →
      ‖B.coefficientFrameRead P i a (chart (i : M) p)‖ ≤ D ∧
      ‖fderiv ℝ (B.coefficientFrameRead P i a) (chart (i : M) p)‖ ≤ D := by
  have hb (i : B.centers) (a : B.centers × Fin 3) : ∃ D : ℝ, 1 ≤ D ∧
      ∀ p ∈ tsupport (B.weight i) ∩ tsupport (B.weight a.1),
        ‖B.coefficientFrameRead P i a (chart (i : M) p)‖ ≤ D ∧
        ‖fderiv ℝ (B.coefficientFrameRead P i a) (chart (i : M) p)‖ ≤ D := by
    let K := (chart (i : M)) '' (tsupport (B.weight i) ∩ tsupport (B.weight a.1))
    have hK : IsCompact K := ((isClosed_tsupport (B.weight i)).inter
      (isClosed_tsupport (B.weight a.1))).isCompact.image_of_continuousOn
        ((chart (i : M)).continuousOn.mono (fun _ hp => B.weight_support i hp.1))
    have hc : ContinuousOn (fun y => (B.coefficientFrameRead P i a y,
        fderiv ℝ (B.coefficientFrameRead P i a) y)) K := by
      rintro y ⟨p,hp,rfl⟩
      have hs := B.coefficientFrameRead_smoothAt P i a (B.weight_support i hp.1)
        (B.weight_support a.1 hp.2) (hQ a p hp.2)
      exact (hs.continuousAt.prodMk (hs.continuousAt_fderiv (by simp))).continuousWithinAt
    obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn hc
    refine ⟨max 1 D,le_max_left _ _,?_⟩
    intro p hp
    have hh := (hD _ ⟨p,hp,rfl⟩).trans (le_max_right 1 D)
    exact ⟨(norm_fst_le _).trans hh,(norm_snd_le _).trans hh⟩
  choose D hD hb using fun k : B.centers × (B.centers × Fin 3) => hb k.1 k.2
  refine ⟨1+∑ k, D k,?_,?_⟩
  · have := Finset.sum_nonneg (s := Finset.univ) (fun k _ => zero_le_one.trans (hD k))
    linarith
  · intro i a p hi ha
    have hle : D (i,a) ≤ 1+∑ k, D k := by
      have := Finset.single_le_sum (fun k _ => zero_le_one.trans (hD k)) (Finset.mem_univ (i,a))
      linarith
    exact ⟨((hb (i,a) p ⟨hi,ha⟩).1).trans hle,((hb (i,a) p ⟨hi,ha⟩).2).trans hle⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
