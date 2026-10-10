import OAI.Geometry.SurfaceImmersion.Atlas.ConvexQuadraticPhase
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseBasisPerturbation

namespace OAI

/-! The actual positive coefficient forms of the three convex phases.
The chart and cone radii are chosen together before a path metric. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

def convexPhaseCovectors (P : PhaseBasis) (L : ℝ) (p : Base) : Fin 3 → Base :=
  fun i => P.ξ i + L • p

lemma convexPhaseCovectors_smooth (P : PhaseBasis) (L : ℝ) :
    ContDiff ℝ ∞ (convexPhaseCovectors P L) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_const.add (contDiff_id.const_smul L)

lemma convexPhaseCovectors_eq_phaseDerivative (P : PhaseBasis) (L : ℝ) (p : Base) :
    convexPhaseCovectors P L p =
      fun i => phaseDerivative (convexQuadraticPhase (P.ξ i) L) p := by
  funext i
  exact (convexQuadraticPhase_phaseDerivative (P.ξ i) L p).symm

lemma convexPhaseCovectors_dist (P : PhaseBasis) {L : ℝ} (hL : 0 ≤ L) (p : Base) :
    ‖convexPhaseCovectors P L p - P.ξ‖ ≤ L * ‖p‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hL (norm_nonneg p))).mpr
  intro i
  simp only [convexPhaseCovectors, Pi.sub_apply, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hL, le_refl]

def convexPhaseCoefficient (P : PhaseBasis) (L : ℝ) (p : Base) (i : Fin 3) :
    PhaseMean.Tensor →L[ℝ] ℝ :=
  perturbedPhaseCoefficient P (convexPhaseCovectors P L p) i

lemma convexPhaseCoefficient_smoothAt (P : PhaseBasis) (L : ℝ) {p : Base}
    (hp : (perturbedPhaseOperator P (convexPhaseCovectors P L p)).IsInvertible)
    (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun x => convexPhaseCoefficient P L x i) p :=
  (perturbedPhaseCoefficient_smoothAt P hp i).comp p
    (convexPhaseCovectors_smooth P L).contDiffAt

lemma convexPhaseCoefficient_decomposition (P : PhaseBasis) (L : ℝ) {p : Base}
    (hp : (perturbedPhaseOperator P (convexPhaseCovectors P L p)).IsInvertible)
    (H : PhaseMean.Tensor) :
    ∑ i, convexPhaseCoefficient P L p i H •
      covectorSquare (phaseDerivative (convexQuadraticPhase (P.ξ i) L) p) = H := by
  simpa only [convexPhaseCoefficient, convexQuadraticPhase_phaseDerivative,
    convexPhaseCovectors] using perturbedPhase_decomposition P hp H

/-- One sufficiently small disk retains both the actual positive basis
coefficients and the positive metric Hessians for every fixed compact
family of admissible metric first jets. -/
theorem compact_positive_convex_phase_charts (P : PhaseBasis)
    {T : Set PhaseMean.Tensor} (hT : IsCompact T)
    (hTpos : ∀ H ∈ T, ∀ i, 0 < P.Q i H)
    {J : Set MetricFirstJet} (hJ : IsCompact J)
    (hdet : ∀ j ∈ J, metricJetDet j ≠ 0) :
    ∃ L r : ℝ, 0 < L ∧ 0 < r ∧
      (∀ p : Base, ‖p‖ ≤ r →
        (perturbedPhaseOperator P (convexPhaseCovectors P L p)).IsInvertible ∧
        (∀ H ∈ T, ∀ i, 0 < convexPhaseCoefficient P L p i H) ∧
        (∀ i, ContDiffAt ℝ ∞ (fun x => convexPhaseCoefficient P L x i) p)) ∧
      ∀ (h : Base → PhaseMean.Tensor) (p : Base), ‖p‖ ≤ r →
        (h p,fderiv ℝ h p) ∈ J → ∀ i,
          (∀ v : Base, v ≠ 0 →
            0 < coordinateMetricHessian h (convexQuadraticPhase (P.ξ i) L) p v v) ∧
          ∃ e : OpenPartialHomeomorph Base Base, p ∈ e.source ∧
            (∀ x, (e x).1 = convexQuadraticPhase (P.ξ i) L x) ∧
            ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨eps,heps,hpert⟩ := compact_positive_phase_perturbation P hT hTpos
  obtain ⟨L,r,hL,hr,hchart⟩ := finite_uniform_convex_phase_charts hJ hdet P.ξ P.nonzero
  let r' := min r (eps / (2 * L))
  have hr' : 0 < r' := lt_min hr (div_pos heps (mul_pos (by norm_num) hL))
  refine ⟨L,r',hL,hr',?_,?_⟩
  · intro p hp
    have hnorm : ‖convexPhaseCovectors P L p - P.ξ‖ < eps := by
      calc
        _ ≤ L * ‖p‖ := convexPhaseCovectors_dist P hL.le p
        _ ≤ L * (eps / (2 * L)) :=
          mul_le_mul_of_nonneg_left (hp.trans (min_le_right _ _)) hL.le
        _ = eps / 2 := by field_simp [hL.ne']
        _ < eps := by linarith
    obtain ⟨hinv,_,hpos⟩ := hpert _ hnorm
    exact ⟨hinv,hpos,fun i => convexPhaseCoefficient_smoothAt P L hinv i⟩
  · intro h p hp hj i
    exact hchart h p (hp.trans (min_le_left _ _)) hj i

/-- Shrinking once supplies a single chart for each entire closed disk,
instead of choosing a different local chart at each of its points. -/
theorem convex_phase_charts_on_disk (P : PhaseBasis) {L r₀ : ℝ}
    (hL : 0 ≤ L) (hr₀ : 0 < r₀) :
    ∃ r : ℝ, 0 < r ∧ r ≤ r₀ ∧
      ∃ e : Fin 3 → OpenPartialHomeomorph Base Base,
        (∀ i x, (e i x).1 = convexQuadraticPhase (P.ξ i) L x) ∧
        (∀ i, ContDiff ℝ ∞ (e i) ∧ ContDiffOn ℝ ∞ (e i).symm (e i).target) ∧
        ∀ i p, ‖p‖ ≤ r → p ∈ (e i).source := by
  have hcharts (i : Fin 3) :
      ∃ e : OpenPartialHomeomorph Base Base, (0 : Base) ∈ e.source ∧
        (∀ x, (e x).1 = convexQuadraticPhase (P.ξ i) L x) ∧
        ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target := by
    apply convexQuadraticPhase_chart hL
    simpa only [norm_zero, mul_zero] using norm_pos_iff.mpr (P.nonzero i)
  choose e he0 hephase hesmooth heinverse using hcharts
  let U : Set Base := ⋂ i, (e i).source
  have hU : IsOpen U := isOpen_iInter_of_finite (fun i => (e i).open_source)
  have h0 : (0 : Base) ∈ U := mem_iInter.mpr he0
  obtain ⟨eps,heps,hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  refine ⟨min r₀ (eps / 2),lt_min hr₀ (half_pos heps),min_le_left _ _,
    e,hephase,fun i => ⟨hesmooth i,heinverse i⟩,?_⟩
  intro i p hp
  have hpball : p ∈ Metric.ball (0 : Base) eps := by
    rw [Metric.mem_ball,dist_zero_right]
    exact (hp.trans (min_le_right _ _)).trans_lt (by linarith)
  exact mem_iInter.mp (hball hpball) i

/-- The cone and Hessian margins persist under small independent changes
of the linear parts, with the same quadratic coefficient and disk. -/
theorem compact_perturbed_convex_phase_margin (P : PhaseBasis)
    {T : Set PhaseMean.Tensor} (hT : IsCompact T)
    (hTpos : ∀ H ∈ T, ∀ i, 0 < P.Q i H)
    {J : Set MetricFirstJet} (hJ : IsCompact J)
    (hdet : ∀ j ∈ J, metricJetDet j ≠ 0) :
    ∃ L r eps : ℝ, 0 < L ∧ 0 < r ∧ 0 < eps ∧
      ∀ ell : Fin 3 → Base, ‖ell-P.ξ‖ < eps → ∀ p : Base, ‖p‖ ≤ r →
        let xi := fun i => phaseDerivative (convexQuadraticPhase (ell i) L) p
        (perturbedPhaseOperator P xi).IsInvertible ∧ (∀ i, xi i ≠ 0) ∧
        (∀ H ∈ T, ∀ i, 0 < perturbedPhaseCoefficient P xi i H) ∧
        ∀ h : Base → PhaseMean.Tensor, (h p,fderiv ℝ h p) ∈ J → ∀ i v,
          (L/2)*(v.1^2+v.2^2) ≤
            coordinateMetricHessian h (convexQuadraticPhase (ell i) L) p v v := by
  obtain ⟨eta,heta,hpert⟩ := compact_positive_phase_perturbation P hT hTpos
  obtain ⟨L,r,hL,hr,hess⟩ := compact_uniform_convex_quadratic_phases hJ hdet
    (show 0 ≤ ‖P.ξ‖+1 by positivity)
  let r' := min r (eta/(4*L))
  let eps := min (eta/4) 1
  have hr' : 0 < r' := lt_min hr (div_pos heta (mul_pos (by norm_num) hL))
  have heps : 0 < eps := lt_min (by positivity) zero_lt_one
  refine ⟨L,r',eps,hL,hr',heps,fun ell hell p hp => ?_⟩
  dsimp only
  have hnorm : ‖(fun i => phaseDerivative (convexQuadraticPhase (ell i) L) p)-P.ξ‖ < eta := by
    have hbound : ‖(fun i => phaseDerivative (convexQuadraticPhase (ell i) L) p)-P.ξ‖ ≤
        ‖ell-P.ξ‖+L*‖p‖ := by
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro i
      simp only [Pi.sub_apply,convexQuadraticPhase_phaseDerivative]
      calc
        ‖ell i + L • p - P.ξ i‖ = ‖(ell i-P.ξ i)+L • p‖ := by congr 1; abel
        _ ≤ ‖ell i-P.ξ i‖+‖L • p‖ := norm_add_le _ _
        _ ≤ ‖ell-P.ξ‖+L*‖p‖ := by
          simpa only [Pi.sub_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg hL.le] using
            add_le_add (norm_le_pi_norm (ell-P.ξ) i) (le_refl ‖L • p‖)
    have hpbound : L*‖p‖ ≤ eta/4 := by
      calc
        _ ≤ L*(eta/(4*L)) :=
          mul_le_mul_of_nonneg_left (hp.trans (min_le_right _ _)) hL.le
        _ = eta/4 := by field_simp [hL.ne']
    have hellbound : ‖ell-P.ξ‖ < eta/4 := hell.trans_le (min_le_left _ _)
    linarith
  obtain ⟨hinv,hnz,hpos⟩ := hpert _ hnorm
  refine ⟨hinv,hnz,hpos,fun h hj i v => ?_⟩
  apply hess h (ell i) p _ (hp.trans (min_le_left _ _)) hj v
  calc
    ‖ell i‖ ≤ ‖ell i-P.ξ i‖+‖P.ξ i‖ := by simpa using norm_add_le (ell i-P.ξ i) (P.ξ i)
    _ ≤ ‖ell-P.ξ‖+‖P.ξ‖ := add_le_add (norm_le_pi_norm (ell-P.ξ) i) (norm_le_pi_norm P.ξ i)
    _ ≤ ‖P.ξ‖+1 := by
      have : ‖ell-P.ξ‖ < 1 := hell.trans_le (min_le_right _ _)
      linarith

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
