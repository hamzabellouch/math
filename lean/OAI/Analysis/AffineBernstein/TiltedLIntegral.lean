import Mathlib
import OAI.Analysis.AffineBernstein.ActualSigmaInterpolation
import OAI.Analysis.AffineBernstein.TiltedTrace

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section TiltedLIntegral
open MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- The tilted-cap trace estimate for nonnegative integrals, with no a priori
integrability assumption on the trace being bounded. -/
lemma lintegral_inverse_trace_le_tilted {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {B : α → Matrix ι ι ℝ} {I : α → ℝ}
    (hB : ∀ᵐ x ∂μ, (B x).PosDef) (hI : 0 ≤ᵐ[μ] I)
    (hc : ∀ r, AEMeasurable (fun x => ENNReal.ofReal (I x*inverseMatrixPair (B x)
      (capTiltedCovector r) (capTiltedCovector r))) μ) :
    (∫⁻ x, ENNReal.ofReal (I x*(B x)⁻¹.trace) ∂μ) ≤
      ∑ r, ∫⁻ x, ENNReal.ofReal (I x*inverseMatrixPair (B x)
        (capTiltedCovector r) (capTiltedCovector r)) ∂μ := by
  rw [← lintegral_finsetSum' _ (fun r _ => hc r)]
  apply lintegral_mono_ae
  filter_upwards [hB,hI] with x hx hIx
  rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => mul_nonneg hIx
    (inverseMatrixPair_self_nonneg hx _)),← Finset.mul_sum]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (inverse_trace_le_tilted hx) hIx)
end TiltedLIntegral

section ActualSigmaCaps
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

/- The genuine sigma density is controlled by exactly the three source
geometric integrals: fiber area, large base minors, and cap inverse energy.
No upper bound on sigma or on inverse energy is assumed. -/
theorem affineEpigraph_sigma_cap_interpolation {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : Q ⊆ D)
    (ν : Measure (Metric.sphere (0:E) 1)) [SFinite ν] {r ρ M : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hM : 0 ≤ M) (hbase : ∀ s ∈ Q, ∀ i, r ≤ s i)
    (hinner : ∀ s ∈ Q, Metric.closedBall (0:E) ρ ⊆ {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (houter : ∀ s ∈ Q, ∀ y : E, (s,y) ∈ affineEpigraphPullback Ω u a L → ‖y‖ ≤ M) :
    let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let B := fun q : Space k × Metric.sphere (0:E) 1 =>
      tubeBaseMatrix H (q.1,q.2) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    let A := fun q : Space k × Metric.sphere (0:E) 1 => tubeAngularDensity H (q.1,q.2) bE
    let μ := (volume.restrict Q).prod ν
    (∫⁻ q, ENNReal.ofReal (tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE (q.1,q.2) *
      tubeLogMassWeight H (q.1,q.2)) ∂μ) ≤
      ENNReal.ofReal (ρ^(-(n:ℝ)/2)) *
        (∫⁻ q, ENNReal.ofReal (B q).det ∂μ)^(1/(2:ℝ)) *
        (∫⁻ q, ENNReal.ofReal (A q) ∂μ)^(1/(2:ℝ)) +
      ENNReal.ofReal (M/r^2) * (ENNReal.ofReal (ρ^(-(n:ℝ)/2)) *
        (∑ j, ∫⁻ q, ENNReal.ofReal ((B q).det ^ (1/((n:ℝ)+2)) * (A q) ^ (1-1/((n:ℝ)+2))*inverseMatrixPair (B q) (capTiltedCovector j) (capTiltedCovector j)) ∂μ) ^
          (((n:ℝ)+2)/(2*((n:ℝ)+1))) *
        (∫⁻ q, ENNReal.ofReal ((B q).det*(B q)⁻¹.trace) ∂μ) ^ (1-((n:ℝ)+2)/(2*((n:ℝ)+1)))) := by
  let : NeZero k := ⟨by omega⟩
  let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let B := fun q : Space k × Metric.sphere (0:E) 1 => tubeBaseMatrix H (q.1,q.2) b
  let A := fun q : Space k × Metric.sphere (0:E) 1 => tubeAngularDensity H (q.1,q.2) bE
  let μ := (volume.restrict Q).prod ν
  have hmap : Continuous (fun q : Space k × Metric.sphere (0:E) 1 => (q.1,(q.2:E))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have he (e : Metric.sphere (0:E) 1) : ‖(e:E)‖ = 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using e.property
  have he0 (e : Metric.sphere (0:E) 1) : (e:E) ≠ 0 := Metric.ne_of_mem_sphere e.property one_ne_zero
  have hj (q : Space k × Metric.sphere (0:E) 1) (hq : q.1 ∈ Q) : ContDiffAt ℝ ∞ H (q.1,q.2) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero (hQD hq) (he0 q.2)).1
  have hpq (q : Space k × Metric.sphere (0:E) 1) (hq : q.1 ∈ Q) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero (hQD hq) (he0 q.2) b bE
  have hc {f : Space k × E → ℝ}
      (hf : ∀ q : Space k × Metric.sphere (0:E) 1, q.1 ∈ Q → ContinuousAt f (q.1,q.2)) :
      AEMeasurable (fun q : Space k × Metric.sphere (0:E) 1 => f (q.1,q.2)) μ := by
    change AEMeasurable _ ((volume.restrict Q).prod ν)
    rw [Measure.restrict_prod_eq_prod_univ]
    apply ContinuousOn.aemeasurable _ (hQ.prod MeasurableSet.univ)
    intro q hq
    exact ((hf q hq.1).comp (f := fun z : Space k × Metric.sphere (0:E) 1 => (z.1,(z.2:E)))
      (x := q) hmap.continuousAt).continuousWithinAt
  have hHae := hc (f := H) (fun q hq => (hj q hq).continuousAt)
  have hBae := hc (f := fun z => (tubeBaseMatrix H z b).det) (fun q hq =>
    (((continuousDetRows (ι := Fin k)).contDiff.contDiffAt.comp (q.1,(q.2:E))
      (contDiffAt_tubeBaseMatrix (hj q hq) b))).continuousAt)
  have hAae := hc (f := fun z => tubeAngularDensity H z bE) (fun q hq =>
    (contDiffAt_tubeAngularDensity (hj q hq) bE).continuousAt)
  have htae := hc (f := fun z => (tubeBaseMatrix H z b)⁻¹.trace) (by
    intro q hq
    change ContinuousAt (fun z => ∑ i, (tubeBaseMatrix H z b)⁻¹ i i) (q.1,q.2)
    have ht : ContDiffAt ℝ ∞ (fun z => ∑ i, (tubeBaseMatrix H z b)⁻¹ i i) (q.1,q.2) :=
      ContDiffAt.sum fun i _ => contDiffAt_inverse_matrix_entry_param
        (contDiffAt_tubeBaseMatrix (hj q hq) b) (hpq q hq).1.det_pos.ne' i i
    exact ht.continuousAt)
  have hqa : ∀ᵐ q ∂μ, q.1 ∈ Q := by
    change ∀ᵐ q ∂(volume.restrict Q).prod ν, q.1 ∈ Q
    rw [Measure.restrict_prod_eq_prod_univ]
    filter_upwards [ae_restrict_mem (μ := volume.prod ν) (hQ.prod MeasurableSet.univ)] with q hq
    exact hq.1
  let I : Space k × Metric.sphere (0:E) 1 → ℝ := fun q =>
    (B q).det ^ (1/((n:ℝ)+2)) * (A q) ^ (1-1/((n:ℝ)+2))
  have hIae : AEMeasurable I μ := (hBae.pow_const _).mul (hAae.pow_const _)
  have hinv (i j : Fin k) : AEMeasurable (fun q => (B q)⁻¹ i j) μ :=
    hc (f := fun z => (tubeBaseMatrix H z b)⁻¹ i j) (fun q hq =>
      (contDiffAt_inverse_matrix_entry_param (contDiffAt_tubeBaseMatrix (hj q hq) b)
        (hpq q hq).1.det_pos.ne' i j).continuousAt)
  have hcap (j : Fin k) : AEMeasurable (fun q => ENNReal.ofReal
      (I q*inverseMatrixPair (B q) (capTiltedCovector j) (capTiltedCovector j))) μ := by
    apply AEMeasurable.ennreal_ofReal
    apply hIae.mul
    unfold inverseMatrixPair
    apply Finset.aemeasurable_fun_sum
    intro l _
    apply Finset.aemeasurable_fun_sum
    intro i _
    exact ((hinv i l).mul_const _).mul_const _
  have htrace := lintegral_inverse_trace_le_tilted
    (hqa.mono fun q hq => (hpq q hq).1)
    (hqa.mono fun q hq => mul_nonneg (Real.rpow_nonneg (hpq q hq).1.det_pos.le _)
      (Real.rpow_nonneg (hpq q hq).2.1.le _)) hcap
  have hs := affineEpigraph_sigma_interpolation hn hk hΩ hcv hu hp a L hD hK hzero bE
    hQ hQD ν hr hρ hM hbase hinner houter
  refine hs.trans ?_
  have hα : 0 ≤ ((n:ℝ)+2)/(2*((n:ℝ)+1)) := by positivity
  gcongr
end ActualSigmaCaps

-- END

end AffineBernstein

end

end OAI
