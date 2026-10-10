import Mathlib
import OAI.Analysis.AffineBernstein.ActualProductBounds
import OAI.Analysis.AffineBernstein.SigmaCapHelpers
import OAI.Analysis.AffineBernstein.WholeGraphAreaTransport
import OAI.Analysis.AffineBernstein.ActualAreaMass
import OAI.Analysis.AffineBernstein.ProductAmbientCoordinates
import OAI.Analysis.AffineBernstein.PositiveMassAlgebra

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section FaceSigmaTransport
open Metric
/-- The original graph affine area over any compact-fiber rectangle is controlled
by the actual weighted sigma mass. The multiplicity constant is fixed before
all epigraphs and affine coordinates. -/
theorem affineEpigraph_face_sigma_transport {n k m d : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m) :
    ∃ CA > 0, ∀ {Ω : Set (Space n)}, IsOpen Ω → Convex ℝ Ω →
    ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω → (∀ x ∈ Ω, (hessian u x).PosDef) →
    ∀ (a : Space n × ℝ) (L : (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
      {D : Set (Space k)}, IsOpen D →
    (∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
    (∀ s ∈ D, (0:Space m) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
    ∀ {Q : Set (Space k)}, MeasurableSet Q → Q ⊆ D → ∀ {M : ℝ}, 0 ≤ M →
    (∀ s ∈ Q, ∀ y : Space m, (s,y) ∈ affineEpigraphPullback Ω u a L → ‖y‖ ≤ M) →
    ∀ {K : Set (Space n)}, K ⊆ Ω → (∀ x ∈ K, (L.symm ((x,u x)-a)).1 ∈ Q) →
    let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
    let H := fun q : Space k × Space m => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let μ := (volume.restrict Q).prod (volume : Measure (Space m)).toSphere
    let F := ((m:ℝ≥0∞)^2 * volume (closedBall (0:Space m) (M+1))) * volume Q
    ENNReal.ofReal (Real.rpow |(productAmbientBasis bE e).det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
        ((n:ℝ)/((n:ℝ)+2)) * ∫ x in K, affineAreaDensity u x) ≤
      (ENNReal.ofReal CA * ENNReal.ofReal (M^((n:ℝ)/((n:ℝ)+2))) * F^(1-2/((n:ℝ)+2))) *
      (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
        ENNReal.ofReal (tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE (q.1,q.2)*
          tubeLogMassWeight H (q.1,q.2)) ∂μ)^(2/((n:ℝ)+2)) := by
  let : NeZero m := ⟨by omega⟩
  let bS := EuclideanSpace.basisFun (Fin k) ℝ
  let bF := EuclideanSpace.basisFun (Fin d) ℝ
  let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
  obtain ⟨CA,hCA,hwhole⟩ := affineEpigraph_whole_graph_area_bound bS bF bE f e
  refine ⟨CA,hCA,?_⟩
  intro Ω hΩ hcv u hu hp a L D hD hK hzero Q hQ hQD M hM hbound K hKO hKQ
  dsimp only
  let H := fun q : Space k × Space m => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let μ := (volume.restrict Q).prod (volume : Measure (Space m)).toSphere
  let σ : ℝ≥0∞ := ∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
    ENNReal.ofReal (tubeMeasureDensity n H bS.toBasis bE (q.1,q.2)*tubeLogMassWeight H (q.1,q.2)) ∂μ
  let F : ℝ≥0∞ := ((m:ℝ≥0∞)^2 * volume (closedBall (0:Space m) (M+1))) * volume Q
  have hfarea : (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
      ENNReal.ofReal (tubeAngularDensity H (q.1,q.2) bE) ∂μ) ≤ F := by
    have hh := affineEpigraph_product_fiber_area_bound hm hΩ hcv hu hp a L hD hK hzero hQ hQD hbound
    simpa only [bE,tubeAngularDensity_reindex] using hh
  have hw := hwhole hΩ hcv hu hp a L hD hK hzero hQ hQD hKO hKQ
  dsimp only at hw
  have hjhold := affineEpigraph_area_le_sigma hn hΩ hcv hu hp a L hD hK hzero bE hQ hQD hM hbound
  dsimp only at hjhold
  have hncard : n = k+d := by
    have hh := Fintype.card_congr e
    simpa only [Fintype.card_fin,Fintype.card_sum] using hh
  have hdim : (Fintype.card (Fin k):ℝ)+Fintype.card (Fin d)+2 = (n:ℝ)+2 := by
    simp only [Fintype.card_fin,hncard,Nat.cast_add]
  rw [hdim] at hw
  have hnn : 0 ≤ᵐ[volume.restrict K] affineAreaDensity u := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hKO (ae_restrict_mem hΩ.measurableSet)] with x hx
    exact Real.rpow_nonneg (hp x hx).det_pos.le _
  have hy : 0 ≤ 1-2/((n:ℝ)+2) := by
    have hh : 2/((n:ℝ)+2) ≤ 1 := (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    linarith
  have hcoef : 0 ≤ Real.rpow |(productAmbientBasis bE e).det
        ((graphAmbientBasis n).map L.symm.toLinearEquiv)| ((n:ℝ)/((n:ℝ)+2)) :=
      Real.rpow_nonneg (abs_nonneg _) _
  rw [ENNReal.ofReal_mul hcoef]
  refine (mul_le_mul_right (ofReal_integral_le_lintegral_of_nonneg hnn) _).trans (hw.trans ?_)
  calc
    _ ≤ ENNReal.ofReal CA *
      (ENNReal.ofReal (M^((n:ℝ)/((n:ℝ)+2))) * σ^(2/((n:ℝ)+2)) * F^(1-2/((n:ℝ)+2))) := by
      apply mul_le_mul_right
      exact hjhold.trans (mul_le_mul_right (ENNReal.rpow_le_rpow hfarea hy) _)
    _ = _ := by
      change ENNReal.ofReal CA * (ENNReal.ofReal (M^((n:ℝ)/((n:ℝ)+2))) *
        σ^(2/((n:ℝ)+2)) * F^(1-2/((n:ℝ)+2))) =
        (ENNReal.ofReal CA * ENNReal.ofReal (M^((n:ℝ)/((n:ℝ)+2))) * F^(1-2/((n:ℝ)+2))) * σ^(2/((n:ℝ)+2))
      ac_rfl
end FaceSigmaTransport


end
end AffineBernstein
end

end OAI
