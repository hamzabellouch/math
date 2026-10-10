import Mathlib
import OAI.Analysis.AffineBernstein.ActualBaseMinors
import OAI.Analysis.AffineBernstein.LogMassWeight
import OAI.Analysis.AffineBernstein.WeightedMassUpper

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

/- The genuine sigma density is controlled by exactly the three source
geometric integrals: fiber area, large base minors, and cap inverse energy.
No upper bound on sigma or on inverse energy is assumed. -/
theorem affineEpigraph_sigma_interpolation {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
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
        (∫⁻ q, ENNReal.ofReal ((B q).det ^ (1/((n:ℝ)+2)) * (A q) ^ (1-1/((n:ℝ)+2))*(B q)⁻¹.trace) ∂μ) ^
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
  apply lintegral_sigma_mass_le hn hHae hBae hAae htae
    (hqa.mono fun q hq => (hpq q hq).1.det_pos)
    (hqa.mono fun q hq => (hpq q hq).2.1)
    (hqa.mono fun q hq => (hpq q hq).1.inv.trace_pos) hρ (div_nonneg hM (sq_nonneg r))
  · filter_upwards [hqa] with q hq
    exact homogeneousSupport_ge_of_ball (hK q.1 (hQD hq)) (he q.2) hρ.le (hinner q.1 hq)
  · filter_upwards [hqa] with q hq
    apply tubeLogMassWeight_le_trace H (q.1,q.2) hr (hbase q.1 hq) (hpq q hq).2.2.le
    · exact (le_abs_self _).trans (homogeneousSupport_abs_le_of_radius (hK q.1 (hQD hq))
        ⟨0,interior_subset (hzero q.1 (hQD hq))⟩ (he q.2) (houter q.1 hq))
    · exact (hpq q hq).1

end AffineBernstein
end

end OAI
