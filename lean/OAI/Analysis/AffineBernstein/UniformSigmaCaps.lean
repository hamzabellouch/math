import Mathlib
import OAI.Analysis.AffineBernstein.CompleteSphericalCaps
import OAI.Analysis.AffineBernstein.ActualProductBounds
import OAI.Analysis.AffineBernstein.TiltedLIntegral
import OAI.Analysis.AffineBernstein.SigmaCapHelpers

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- A uniform weighted actual-sigma bound in a normalized positive cell.
The cap energy, large minors and fiber area are all PRODUCED from literal geometry
and the unchanged complete original PDE. In particular no integrability or energy
bound is an assumption. All constants precede the varying graph and normalization. -/
theorem complete_affineMaximal_uniform_sigma_bound {n k m d : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m)
    {D Q : Set (Space k)} (hD : IsOpen D) (hDc : Convex ℝ D)
    (hQ : IsCompact Q) (hQD : Q ⊆ D)
    (o : Space k × Space m) {ε r₀ r₁ α ρ M R T RQ : ℝ}
    (hε : 0 < ε) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hα : 0 < α) (hρ : 0 < ρ)
    (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hogap : ∀ j : Fin k, capTiltedForm j o.1 < T+ε)
    (hDheight : ∀ j : Fin k, ∀ s ∈ D, capTiltedForm j s ≤ T+ε)
    (hQheight : ∀ j : Fin k, ∀ s ∈ Q, capTiltedForm j s ≤ T-ε)
    (hbase : ∀ s ∈ Q, ∀ i, α ≤ s i)
    (hmargin : ∀ s ∈ Q, Metric.closedBall s r₁ ⊆ D)
    (hRQ : ∀ s ∈ Q, ‖s‖ ≤ RQ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {Ω : Set (Space n)}, IsOpen Ω → Ω.Nonempty → Convex ℝ Ω →
      ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
      (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u → EuclideanGraphComplete Ω u →
      ∀ (a : Space n × ℝ) (L : (Space k × Space m) ≃L[ℝ] (Space n × ℝ)),
      (∀ j : Fin k, ∀ p ∈ affineEpigraphPullback Ω u a L,
        capTiltedForm j p.1 ≤ T+ε → ‖p‖ ≤ R) →
      Metric.closedBall o r₀ ⊆ affineEpigraphPullback Ω u a L →
      (∀ s ∈ D, Metric.closedBall (0:Space m) ρ ⊆
        {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
      (∀ s ∈ D, ∀ y : Space m, (s,y) ∈ affineEpigraphPullback Ω u a L → ‖y‖ ≤ M) →
      let H := fun q : Space k × Space m =>
        homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
      let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
      (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
        ENNReal.ofReal (tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE
          (q.1,q.2) * tubeLogMassWeight H (q.1,q.2))
        ∂(volume.restrict Q).prod (volume : Measure (Space m)).toSphere) ≤ C := by
  let : NeZero k := ⟨by omega⟩
  let : NeZero m := ⟨by omega⟩
  let bS := EuclideanSpace.basisFun (Fin k) ℝ
  let bF := EuclideanSpace.basisFun (Fin d) ℝ
  let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
  choose C hC hc using fun j : Fin k =>
    complete_affineMaximal_uniform_spherical_cap_bound bS bF bE f e
      (capTiltedForm j) o hε hr₀ hR T (hogap j)
  let ν : Measure (Metric.sphere (0:Space m) 1) := volume.toSphere
  let μ : Measure (Space k × Metric.sphere (0:Space m) 1) := (volume.restrict Q).prod ν
  let Cm : ℝ≥0∞ := (((k:ℝ≥0∞)+1)*volume (Metric.closedBall (0:Space k) (2*M/r₁+RQ))) * ν Set.univ
  let Ca : ℝ≥0∞ := ((m:ℝ≥0∞)^2 * volume (Metric.closedBall (0:Space m) (M+1))) * volume Q
  let Ce : ℝ≥0∞ := ∑ j, ENNReal.ofReal (C j)
  let γ : ℝ := ((n:ℝ)+2)/(2*((n:ℝ)+1))
  have hγ : 0 ≤ γ := by dsimp [γ]; positivity
  have hγ' : 0 ≤ 1-γ := by
    dsimp [γ]
    have hd : 0 < 2*((n:ℝ)+1) := by positivity
    have hh : ((n:ℝ)+2)/(2*((n:ℝ)+1)) ≤ 1 := (div_le_one hd).mpr (by linarith)
    linarith
  let Cσ : ℝ≥0∞ := ENNReal.ofReal (ρ^(-(n:ℝ)/2)) * Cm^(1/(2:ℝ)) * Ca^(1/(2:ℝ)) +
    ENNReal.ofReal (M/α^2) * (ENNReal.ofReal (ρ^(-(n:ℝ)/2)) * Ce^γ * Cm^(1-γ))
  have hCm : Cm ≠ ⊤ := by
    dsimp [Cm, ν]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp)
      (isCompact_closedBall _ _).measure_ne_top) (measure_ne_top _ _)
  have hCa : Ca ≠ ⊤ := by
    dsimp [Ca]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp)
      (isCompact_closedBall _ _).measure_ne_top) hQ.measure_ne_top
  have hCe : Ce ≠ ⊤ := by dsimp [Ce]; simp
  refine ⟨Cσ, ?_, ?_⟩
  · dsimp [Cσ]
    finiteness
  intro Ω hΩ hne hcv u hu hp hmP hcomplete a L hcaps hball hinter houter
  let H := fun q : Space k × Space m =>
    homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let B := fun q : Space k × Metric.sphere (0:Space m) 1 => tubeBaseMatrix H (q.1,q.2) bS.toBasis
  let A := fun q : Space k × Metric.sphere (0:Space m) 1 => tubeAngularDensity H (q.1,q.2) bE
  have hclosed := sourceEpigraph_closed hΩ hne hcv hu hp hcomplete
  have hK (s : Space k) (hs : s ∈ D) : IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L} :=
    affineEpigraphPullback_fiber_isCompact hclosed a L (capTiltedForm (0 : Fin k))
      (hcaps 0) (hDheight 0 s hs)
  have hzero (s : Space k) (hs : s ∈ D) : (0 : Space m) ∈
      interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L} :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 hρ)
      (hinter s hs))
  have hqa : ∀ᵐ q ∂μ, q.1 ∈ Q := by
    dsimp [μ]
    rw [Measure.restrict_prod_eq_prod_univ]
    filter_upwards [ae_restrict_mem (μ := volume.prod ν) (hQ.measurableSet.prod MeasurableSet.univ)] with q hq
    exact hq.1
  have he (q : Metric.sphere (0:Space m) 1) : ‖(q : Space m)‖ = 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using q.property
  have he0 (q : Metric.sphere (0:Space m) 1) : (q : Space m) ≠ 0 :=
    Metric.ne_of_mem_sphere q.property one_ne_zero
  have hpos (q : Space k × Metric.sphere (0:Space m) 1) (hq : q.1 ∈ Q) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero (hQD hq) (he0 q.2) bS.toBasis bE
  have hmin := affineEpigraph_product_minors_bound hm hΩ hcv hu hp a L hD hDc hK hzero
    hQ.measurableSet hQD hr₁ hM hmargin houter hRQ
  change (∫⁻ q, ENNReal.ofReal ((B q).det*(1+(B q)⁻¹.trace)) ∂μ) ≤ Cm at hmin
  have hdet : (∫⁻ q, ENNReal.ofReal (B q).det ∂μ) ≤ Cm := by
    apply le_trans (lintegral_mono_ae ?_) hmin
    filter_upwards [hqa] with q hq
    apply ENNReal.ofReal_le_ofReal
    have hd := (hpos q hq).1.det_pos.le
    have ht := inverse_trace_nonneg (hpos q hq).1
    nlinarith
  have htrace : (∫⁻ q, ENNReal.ofReal ((B q).det * (B q)⁻¹.trace) ∂μ) ≤ Cm := by
    apply le_trans (lintegral_mono_ae ?_) hmin
    filter_upwards [hqa] with q hq
    apply ENNReal.ofReal_le_ofReal
    have hd := (hpos q hq).1.det_pos.le
    nlinarith
  have harea : (∫⁻ q, ENNReal.ofReal (A q) ∂μ) ≤ Ca := by
    have ha := affineEpigraph_product_fiber_area_bound hm hΩ hcv hu hp a L hD hK hzero
      hQ.measurableSet hQD (fun s hs y hy => houter s (hQD hs) y hy)
    simpa only [A,bE,tubeAngularDensity_reindex] using ha
  have hncard : (Fintype.card (Fin k):ℝ)+Fintype.card (Fin d) = n := by
    have hh := Fintype.card_congr e
    simp only [Fintype.card_fin,Fintype.card_sum] at hh
    simp only [Fintype.card_fin]
    exact_mod_cast hh.symm
  have henergy (j : Fin k) :
      (∫⁻ q, ENNReal.ofReal ((B q).det^(1/((n:ℝ)+2)) * (A q)^(1-1/((n:ℝ)+2)) *
        inverseMatrixPair (B q) (capTiltedCovector j) (capTiltedCovector j)) ∂μ) ≤ ENNReal.ofReal (C j) := by
    have hb := hc j hΩ hne hcv hu hp hmP hcomplete a L hD (hDheight j) hzero (hcaps j) hball
      hQ.measurableSet hQD (hQheight j)
    simp only [hncard,bS,capTiltedForm_basis] at hb
    apply le_trans (lintegral_mono_ae ?_) hb
    filter_upwards [hqa] with q hq
    apply ENNReal.ofReal_le_ofReal
    have hn := one_le_norm_supportConormal H q.1 (he q.2)
    have hi := inverseMatrixPair_self_nonneg (hpos q hq).1 (capTiltedCovector j)
    have hI : 0 ≤ (B q).det^(1/((n:ℝ)+2)) * (A q)^(1-1/((n:ℝ)+2)) :=
      mul_nonneg (Real.rpow_nonneg (hpos q hq).1.det_pos.le _)
        (Real.rpow_nonneg (hpos q hq).2.1.le _)
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hi hn) hI
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => henergy j)
  have hs := affineEpigraph_sigma_cap_interpolation hn hk hΩ hcv hu hp a L hD hK hzero bE
    hQ.measurableSet hQD ν hα hρ hM hbase (fun s hs => hinter s (hQD hs))
      (fun s hs => houter s (hQD hs))
  apply hs.trans
  change _ ≤ Cσ
  dsimp only [Cσ]
  gcongr

/- Coordinate Hessian. On the open domain it depends only on the restriction of `u`.
The order of the two differentiations is immaterial under the smoothness hypothesis. -/
/- The coefficient U^{ij} = det(D²u) (D²u)^{-1}_{ij}. -/
/- The classical determinant weight; in particular, this is not a generalized exponent. -/
/- Length on [0,1] for g_x(v,v) = ‖v‖² + (Du_x v)², the metric induced
by the Euclidean graph embedding x ↦ (x,u(x)). The product norm on Lean's ordinary
product type is NOT used (it would be the maximum norm). -/
/- The intrinsic extended distance: infimum of lengths of C¹ paths in the domain.
Using a single C¹ path gives the same intrinsic distance as piecewise C¹ paths,
by smooth endpoint reparameterization and concatenation. -/
/- Sequential completeness for the induced Euclidean path metric. This states
that every intrinsic Cauchy sequence of points in Ω has an intrinsic limit in Ω.
It imposes no growth condition and no completeness condition on the affine metric. -/
/- The graph, regarded as an affine subset of R^{n+1}. -/

end AffineBernstein
end

end OAI
