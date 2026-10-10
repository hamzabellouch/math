import OAI.Geometry.SurfaceImmersion.Geometry.TensorFrameAlgebra
import OAI.Geometry.SurfaceImmersion.Correction.TensorOperatorSmooth
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteScalarBounds

namespace OAI

/-! Compact bounds for actual coefficient and differential fields in the
fixed tensor frames, including overlapping phase charts. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance frameBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance frameBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance frameBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance frameBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance frameBoundSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance frameBoundSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

omit [CompactSpace M] [T2Space M] in
lemma coefficientFrame_coordChange
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (i : B.centers) (a : B.centers × Fin 3) {p : M}
    (hi : p ∈ (chart (i : M)).source) (ha : p ∈ (chart (a.1 : M)).source) :
    B.coefficientFrame P i a p =
      ((P a.1 (chart (a.1 : M) p)).Q a.2).comp (fiberToThree.comp
        ((B.tensorTriv i).coordChangeL ℝ (B.tensorTriv a.1) p : TensorFiber →L[ℝ] TensorFiber)) := by
  apply ContinuousLinearMap.ext
  intro H
  change (P a.1 (chart (a.1 : M) p)).Q a.2
      (fiberToThree ((B.tensorTriv a.1).continuousLinearMapAt ℝ p
        ((B.tensorTriv i).symmL ℝ p H))) = _
  rw [(B.tensorTriv a.1).continuousLinearMapAt_apply_of_mem ℝ (B.tensorTriv_domain a.1 ha),
    (B.tensorTriv i).symmL_apply (R := ℝ) (B.tensorTriv_domain i hi),
    ← (B.tensorTriv i).coordChangeL_apply (R := ℝ) (B.tensorTriv a.1)
      ⟨B.tensorTriv_domain i hi,B.tensorTriv_domain a.1 ha⟩]
  rfl

omit [T2Space M] in
 theorem coefficientFrame_bound
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (hQ : ∀ (a : B.centers × Fin 3) p, p ∈ tsupport (B.weight a.1) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p)) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i a p,
      p ∈ tsupport (B.weight i) → p ∈ tsupport (B.weight a.1) →
      ‖B.coefficientFrame P i a p‖ ≤ D := by
  have hbound (i : B.centers) (a : B.centers × Fin 3) :
      ∃ D : ℝ, 1 ≤ D ∧ ∀ p ∈ tsupport (B.weight i) ∩ tsupport (B.weight a.1),
        ‖B.coefficientFrame P i a p‖ ≤ D := by
    let K := tsupport (B.weight i) ∩ tsupport (B.weight a.1)
    have hc : ContinuousOn (B.coefficientFrame P i a) K := by
      intro p hp
      have hi := B.weight_support i hp.1
      have ha := B.weight_support a.1 hp.2
      have hq := (hQ a p hp.2).contMDiffAt.comp p
        ((chart_smooth (a.1 : M) p ha).contMDiffAt ((chart (a.1 : M)).open_source.mem_nhds ha))
      have hT := (contMDiffOn_coordChangeL (IB := planeModel) (n := ∞) (B.tensorTriv i) (B.tensorTriv a.1)).contMDiffAt
        ((B.tensorTriv i).open_baseSet.inter (B.tensorTriv a.1).open_baseSet |>.mem_nhds
          ⟨B.tensorTriv_domain i hi,B.tensorTriv_domain a.1 ha⟩)
      have hconst : ContMDiffAt planeModel 𝓘(ℝ,TensorFiber →L[ℝ] PhaseMean.Tensor) ∞
          (fun _ : M => fiberToThree) p := contMDiffAt_const
      have hs : ContinuousWithinAt (fun q =>
          ((P a.1 (chart (a.1 : M) q)).Q a.2).comp (fiberToThree.comp
            ((B.tensorTriv i).coordChangeL ℝ (B.tensorTriv a.1) q : TensorFiber →L[ℝ] TensorFiber))) K p :=
        (hq.clm_comp (hconst.clm_comp hT)).continuousAt.continuousWithinAt
      apply hs.congr
      · intro q hq
        exact (B.coefficientFrame_coordChange P i a (B.weight_support i hq.1)
          (B.weight_support a.1 hq.2))
      · exact (B.coefficientFrame_coordChange P i a hi ha)
    obtain ⟨D,hD⟩ := ((isClosed_tsupport (B.weight i)).inter
      (isClosed_tsupport (B.weight a.1))).isCompact.exists_bound_of_continuousOn hc
    exact ⟨max 1 D,le_max_left _ _,fun p hp => (hD p hp).trans (le_max_right _ _)⟩
  choose D hD hb using fun k : B.centers × (B.centers × Fin 3) => hbound k.1 k.2
  refine ⟨1+∑ k, D k,?_,?_⟩
  · have := Finset.sum_nonneg (s := Finset.univ) (fun k _ => (zero_le_one.trans (hD k)))
    linarith
  · intro i a p hi ha
    exact (hb (i,a) p ⟨hi,ha⟩).trans (by
      have := Finset.single_le_sum (fun k _ => zero_le_one.trans (hD k)) (Finset.mem_univ (i,a))
      linarith)

omit [CompactSpace M] [T2Space M] in
lemma covectorFrame_norm_sq (i : B.centers) {p : M} (hp : p ∈ (chart (i : M)).source)
    (v : Plane →L[ℝ] ℝ) :
    ‖B.covectorFrame i p v‖^2 = ‖(B.tensorTriv i).continuousLinearMapAt ℝ p (v.smulRight v)‖ := by
  rw [B.tensor_frame_square i hp,ContinuousLinearMap.norm_smulRight_apply,pow_two]

omit [T2Space M] in
 theorem covectorFrame_bound_at (phi : M → ℝ) (hphi : ContMDiff planeModel 𝓘(ℝ) ∞ phi)
    (i : B.centers) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ p ∈ tsupport (B.weight i),
      ‖B.covectorFrame i p (mfderiv planeModel 𝓘(ℝ) phi p)‖ ≤ D := by
  have hsec := B.phaseDifferentialSquare_smooth phi hphi
  have hc := (B.bundleComponent_smooth_on B.tensorTriv B.tensorTriv_domain i hsec).continuousOn.mono
    (B.weight_support i)
  obtain ⟨C,hC⟩ := (isClosed_tsupport (B.weight i)).isCompact.exists_bound_of_continuousOn hc
  refine ⟨|C|+1,by linarith [abs_nonneg C],?_⟩
  intro p hp
  have hh := hC p hp
  let v : Plane →L[ℝ] ℝ := mfderiv planeModel 𝓘(ℝ) phi p
  have he := B.covectorFrame_norm_sq i (B.weight_support i hp) v
  change ‖(B.tensorTriv i).continuousLinearMapAt ℝ p (v.smulRight v)‖ ≤ C at hh
  rw [← he] at hh
  change ‖B.covectorFrame i p v‖ ≤ |C|+1
  nlinarith [norm_nonneg (B.covectorFrame i p v),le_abs_self C,abs_nonneg C]

omit [T2Space M] in
 theorem covectorFrame_bound (phi : M → ℝ) (hphi : ContMDiff planeModel 𝓘(ℝ) ∞ phi) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i p, p ∈ tsupport (B.weight i) →
      ‖B.covectorFrame i p (mfderiv planeModel 𝓘(ℝ) phi p)‖ ≤ D := by
  choose D hD hb using B.covectorFrame_bound_at phi hphi
  refine ⟨1+∑ i, D i,?_,?_⟩
  · have := Finset.sum_nonneg (s := Finset.univ) (fun i _ => zero_le_one.trans (hD i)); linarith
  · intro i p hp
    exact (hb i p hp).trans (by
      have := Finset.single_le_sum (fun i _ => zero_le_one.trans (hD i)) (Finset.mem_univ i)
      linarith)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
