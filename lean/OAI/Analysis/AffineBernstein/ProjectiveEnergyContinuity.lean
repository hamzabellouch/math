import Mathlib
import OAI.Analysis.AffineBernstein.FlatTubePositive
import OAI.Analysis.AffineBernstein.FlatProductCoordinates
import OAI.Analysis.AffineBernstein.ProjectiveWeightContinuity

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open intervalIntegral
open scoped Pointwise

section ProjectiveEnergyContinuity
open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma continuousAt_flatInverseArea {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (δ : ℝ)
    (hB : 0 < (tubeBaseMatrix H q bS).det) (hR : 0 < (tubeRadiusMatrix H q bE).det)
    (v : ι → ℝ) :
    ContinuousAt (fun y => tubeAreaDensity (tubeBaseMatrix H y bS) (tubeRadiusMatrix H y bE) δ *
      (‖supportConormal H y‖ * inverseMatrixPair (tubeBaseMatrix H y bS) v v)) q := by
  have hb := (contDiffAt_tubeBaseMatrix hH bS).continuousAt
  have hhh := ((hH.fderiv_right (m:=∞) (by simp)).fderiv_right (m:=∞) (by simp)).continuousAt
  have hr : ContinuousAt (fun y => tubeRadiusMatrix H y bE) q := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact (hhh.clm_apply continuousAt_const).clm_apply continuousAt_const
  have hbd := continuous_id.matrix_det.continuousAt.comp hb
  have hrd := continuous_id.matrix_det.continuousAt.comp hr
  have hν : ContinuousAt (fun y => ‖supportConormal H y‖) q :=
    (@continuous_norm ((S × E) →L[ℝ] ℝ) inferInstance).continuousAt.comp
      (continuousAt_supportConormal hH)
  exact ((hbd.rpow_const (Or.inl hB.ne')).mul (hrd.rpow_const (Or.inl hR.ne'))).mul
    (hν.mul (continuousAt_inverseMatrixPair hb hB.ne' v v))

end ProjectiveEnergyContinuity

open Filter
open scoped Topology
variable {S E F : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma affineEpigraph_flatInverseArea_aemeasurable {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bF : OrthonormalBasis κ ℝ F)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (δ : ℝ) (v : ι → ℝ)
    {Q : Set S} (hQ : MeasurableSet Q) (hQD : Q ⊆ D) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    AEMeasurable (fun q : S × F => ENNReal.ofReal
      (tubeAreaDensity (tubeBaseMatrix H (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ)))) bS)
        (tubeRadiusMatrix H (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ)))) (flatProductFiberBasis bF f)) δ *
        (‖supportConormal H (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ))))‖ *
          inverseMatrixPair (tubeBaseMatrix H (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ)))) bS) v v)))
      ((volume.restrict Q).prod volume) := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let bE := flatProductFiberBasis bF f
  rw [Measure.restrict_prod_eq_prod_univ]
  apply ContinuousOn.aemeasurable _ (hQ.prod MeasurableSet.univ)
  intro q hq
  have hv : inner ℝ (f (WithLp.toLp 2 (q.2,(1:ℝ)))) (bE (Sum.inr ())) = 1 := by
    simp only [bE,flatProductFiberBasis_last,f.inner_map_map]
    simp [WithLp.prod_inner_apply]
  have he : f (WithLp.toLp 2 (q.2,(1:ℝ))) ≠ 0 := by
    intro he
    simp [he] at hv
  have hj := (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero (hQD hq.1) he).1
  have hpq := affineEpigraph_flat_tube_positive hΩ hcv hu hp a L hD hK hzero
    (hQD hq.1) bS bE (hv.trans_ne one_ne_zero)
  have hc := continuousAt_flatInverseArea hj bS bE δ hpq.1.det_pos hpq.2.det_pos v
  have hcmap : Continuous (fun q : S × F => (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ))))) := by
    fun_prop
  exact (ENNReal.continuous_ofReal.continuousAt.comp (hc.comp (f := fun q : S × F => (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ)))) ) hcmap.continuousAt)).continuousWithinAt

end AffineBernstein
end

end OAI
