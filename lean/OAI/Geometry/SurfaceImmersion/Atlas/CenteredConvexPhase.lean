import OAI.Geometry.SurfaceImmersion.Atlas.SpatialPhaseBasis

namespace OAI

/-! Convex phases centered at the actual coordinate center of a circular
patch. The connection is evaluated at the original point, so translation
of the phase does not silently translate the metric. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

def centeredConvexPhase (ell : Base) (L : ℝ) (c p : Base) : ℝ :=
  convexQuadraticPhase ell L (p-c)

lemma centeredConvexPhase_smooth (ell : Base) (L : ℝ) (c : Base) :
    ContDiff ℝ ∞ (centeredConvexPhase ell L c) :=
  (convexQuadraticPhase_smooth ell L).comp (contDiff_id.sub contDiff_const)

lemma centeredConvexPhase_hasFDerivAt (ell : Base) (L : ℝ) (c p : Base) :
    HasFDerivAt (centeredConvexPhase ell L c) (phaseLinear (ell+L • (p-c))) p := by
  have ht : HasFDerivAt (fun x : Base => x-c) (ContinuousLinearMap.id ℝ Base) p :=
    (hasFDerivAt_id p).sub_const c
  simpa only [centeredConvexPhase,Function.comp_def,ContinuousLinearMap.comp_id] using!
    (convexQuadraticPhase_hasFDerivAt ell L (p-c)).comp p ht

lemma centeredConvexPhase_coordDeriv (ell : Base) (L : ℝ) (c p v : Base) :
    coordDeriv v (centeredConvexPhase ell L c) p = phaseLinear (ell+L • (p-c)) v :=
  congrArg (fun f : Base →L[ℝ] ℝ => f v)
    (centeredConvexPhase_hasFDerivAt ell L c p).fderiv

lemma centeredConvexPhase_phaseDerivative (ell : Base) (L : ℝ) (c p : Base) :
    phaseDerivative (centeredConvexPhase ell L c) p = ell+L • (p-c) := by
  unfold phaseDerivative
  rw [(centeredConvexPhase_hasFDerivAt ell L c p).fderiv]
  ext <;> simp [phaseLinear_apply,dx,dy]

lemma centeredConvexPhase_second (ell : Base) (L : ℝ) (c p v w : Base) :
    coordDeriv v (coordDeriv w (centeredConvexPhase ell L c)) p =
      L*(v.1*w.1+v.2*w.2) := by
  have he : coordDeriv w (centeredConvexPhase ell L c) =
      fun p => phaseLinear ell w+L*phaseLinear w (p-c) := by
    funext q
    rw [centeredConvexPhase_coordDeriv]
    simp only [phaseLinear_apply,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
      smul_eq_mul]
    ring
  have ht : HasFDerivAt (fun x : Base => x-c) (ContinuousLinearMap.id ℝ Base) p :=
    (hasFDerivAt_id p).sub_const c
  have hd : HasFDerivAt (fun x : Base => phaseLinear w (x-c)) (phaseLinear w) p := by
    simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using!
      ((phaseLinear w).hasFDerivAt (x := p-c)).comp p ht
  have hh := (hasFDerivAt_const (phaseLinear ell w) p).add (hd.const_mul L)
  rw [he]
  change (fderiv ℝ ((fun _ : Base => phaseLinear ell w)+
    fun x => L*phaseLinear w (x-c)) p) v = _
  rw [hh.fderiv]
  simp only [smul_apply,smul_eq_mul,zero_add,phaseLinear_apply]
  ring

lemma centeredConvexPhase_regular {ell c p : Base} {L : ℝ} (hL : 0 ≤ L)
    (hp : L*‖p-c‖ < ‖ell‖) : phaseDerivative (centeredConvexPhase ell L c) p ≠ 0 := by
  rw [centeredConvexPhase_phaseDerivative]
  intro he
  have heq : ell = -(L • (p-c)) := eq_neg_of_add_eq_zero_left he
  rw [heq,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg hL] at hp
  exact lt_irrefl _ hp

lemma centeredConvexPhase_hessian (h : Base → PhaseMean.Tensor) (ell : Base) (L : ℝ)
    (c p v w : Base) :
    coordinateMetricHessian h (centeredConvexPhase ell L c) p v w =
      L*(v.1*w.1+v.2*w.2)-phaseLinear (ell+L • (p-c))
        (connectionContract (metricConnectionAt (h p,fderiv ℝ h p)) v w) := by
  rw [coordinateMetricHessian,centeredConvexPhase_second,centeredConvexPhase_phaseDerivative]

theorem centeredConvexPhase_hessian_lower {h : Base → PhaseMean.Tensor}
    {ell c p : Base} {L B K r : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hK : ‖ell‖ ≤ K) (hp : ‖p-c‖ ≤ r)
    (hGamma : ∀ i, ‖metricConnectionAt (h p,fderiv ℝ h p) i‖ ≤ B) (v : Base) :
    (L-4*B*(K+L*r))*(v.1^2+v.2^2) ≤
      coordinateMetricHessian h (centeredConvexPhase ell L c) p v v := by
  have hg1 : |ell.1+L*(p-c).1| ≤ K+L*r := by
    calc
      _ ≤ |ell.1|+|L*(p-c).1| := abs_add_le _ _
      _ ≤ K+L*r := by
        rw [abs_mul,abs_of_nonneg hL]
        exact add_le_add ((norm_fst_le ell).trans hK)
          (mul_le_mul_of_nonneg_left ((norm_fst_le (p-c)).trans hp) hL)
  have hg2 : |ell.2+L*(p-c).2| ≤ K+L*r := by
    calc
      _ ≤ |ell.2|+|L*(p-c).2| := abs_add_le _ _
      _ ≤ K+L*r := by
        rw [abs_mul,abs_of_nonneg hL]
        exact add_le_add ((norm_snd_le ell).trans hK)
          (mul_le_mul_of_nonneg_left ((norm_snd_le (p-c)).trans hp) hL)
  obtain ⟨hc1,hc2⟩ := connectionContract_diagonal_bound hB hGamma v
  let C := connectionContract (metricConnectionAt (h p,fderiv ℝ h p)) v v
  have hdot : |phaseLinear (ell+L • (p-c)) C| ≤
      4*B*(K+L*r)*(v.1^2+v.2^2) := by
    have hk : 0 ≤ K+L*r := (abs_nonneg _).trans hg1
    calc
      _ ≤ |ell.1+L*(p-c).1| * |C.1|+|ell.2+L*(p-c).2| * |C.2| := by
        simpa only [phaseLinear_apply,Prod.fst_add,Prod.snd_add,Prod.smul_fst,
          Prod.smul_snd,smul_eq_mul,abs_mul] using
          abs_add_le ((ell.1+L*(p-c).1)*C.1) ((ell.2+L*(p-c).2)*C.2)
      _ ≤ (K+L*r)*(2*B*(v.1^2+v.2^2))+
          (K+L*r)*(2*B*(v.1^2+v.2^2)) :=
        add_le_add (mul_le_mul hg1 hc1 (abs_nonneg _) hk)
          (mul_le_mul hg2 hc2 (abs_nonneg _) hk)
      _ = _ := by ring
  rw [centeredConvexPhase_hessian]
  have hh := (le_abs_self (phaseLinear (ell+L • (p-c)) C)).trans hdot
  dsimp only [C] at hh
  nlinarith

/-- The metric-jet compact set fixes the same Hessian constants at every
center; the first metric jet is always taken at the actual point. -/
theorem compact_uniform_centered_convex_phases {J : Set MetricFirstJet}
    (hJ : IsCompact J) (hdet : ∀ j ∈ J, metricJetDet j ≠ 0)
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ L r : ℝ, 0 < L ∧ 0 < r ∧
      ∀ (h : Base → PhaseMean.Tensor) (ell c p : Base), ‖ell‖ ≤ K → ‖p-c‖ ≤ r →
        (h p,fderiv ℝ h p) ∈ J → ∀ v : Base,
        (L/2)*(v.1^2+v.2^2) ≤
          coordinateMetricHessian h (centeredConvexPhase ell L c) p v v := by
  obtain ⟨B,hB,hbound⟩ := compact_metricConnection_bound hJ hdet
  let L := 16*(B+1)*(K+1)
  let r := (16*(B+1))⁻¹
  have hBp : 0 < 16*(B+1) := by positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hr : 0 < r := inv_pos.mpr hBp
  have hLr : L*r = K+1 := by
    dsimp [L,r]
    field_simp [hBp.ne']
  have hsmall : 4*B*(K+L*r) ≤ L/2 := by
    rw [hLr]
    dsimp [L]
    nlinarith
  refine ⟨L,r,hL,hr,fun h ell c p hell hp hj v => ?_⟩
  have hb := centeredConvexPhase_hessian_lower hL.le hB hell hp (hbound _ hj) v
  nlinarith [mul_le_mul_of_nonneg_right hsmall (add_nonneg (sq_nonneg v.1) (sq_nonneg v.2))]

/-- Exact positive phase coefficients and Hessian margins survive
independent linear perturbations on a disk centered anywhere. -/
theorem compact_perturbed_centered_phase_margin (P : PhaseBasis)
    {T : Set PhaseMean.Tensor} (hT : IsCompact T)
    (hTpos : ∀ H ∈ T, ∀ i, 0 < P.Q i H)
    {J : Set MetricFirstJet} (hJ : IsCompact J)
    (hdet : ∀ j ∈ J, metricJetDet j ≠ 0) :
    ∃ L r eps : ℝ, 0 < L ∧ 0 < r ∧ 0 < eps ∧
      ∀ ell : Fin 3 → Base, ‖ell-P.ξ‖ < eps → ∀ c p : Base, ‖p-c‖ ≤ r →
        let xi := fun i => phaseDerivative (centeredConvexPhase (ell i) L c) p
        admissiblePhaseCovectors P xi ∧
        (∀ H ∈ T, ∀ i, 0 < perturbedPhaseCoefficient P xi i H) ∧
        ∀ h : Base → PhaseMean.Tensor, (h p,fderiv ℝ h p) ∈ J → ∀ i v,
          (L/2)*(v.1^2+v.2^2) ≤
            coordinateMetricHessian h (centeredConvexPhase (ell i) L c) p v v := by
  obtain ⟨eta,heta,hpert⟩ := compact_positive_phase_perturbation P hT hTpos
  obtain ⟨L,r,hL,hr,hess⟩ := compact_uniform_centered_convex_phases hJ hdet
    (show 0 ≤ ‖P.ξ‖+1 by positivity)
  let r' := min r (eta/(4*L))
  let eps := min (eta/4) 1
  have hr' : 0 < r' := lt_min hr (div_pos heta (mul_pos (by norm_num) hL))
  have heps : 0 < eps := lt_min (by positivity) zero_lt_one
  refine ⟨L,r',eps,hL,hr',heps,fun ell hell c p hp => ?_⟩
  dsimp only
  have hnorm : ‖(fun i => phaseDerivative (centeredConvexPhase (ell i) L c) p)-P.ξ‖ < eta := by
    have hbound : ‖(fun i => phaseDerivative (centeredConvexPhase (ell i) L c) p)-P.ξ‖ ≤
        ‖ell-P.ξ‖+L*‖p-c‖ := by
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro i
      simp only [Pi.sub_apply,centeredConvexPhase_phaseDerivative]
      calc
        ‖ell i+L • (p-c)-P.ξ i‖ = ‖(ell i-P.ξ i)+L • (p-c)‖ := by congr 1; abel
        _ ≤ ‖ell i-P.ξ i‖+‖L • (p-c)‖ := norm_add_le _ _
        _ ≤ ‖ell-P.ξ‖+L*‖p-c‖ := by
          simpa only [Pi.sub_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg hL.le] using
            add_le_add (norm_le_pi_norm (ell-P.ξ) i) (le_refl ‖L • (p-c)‖)
    have hpbound : L*‖p-c‖ ≤ eta/4 := by
      calc
        _ ≤ L*(eta/(4*L)) :=
          mul_le_mul_of_nonneg_left (hp.trans (min_le_right _ _)) hL.le
        _ = eta/4 := by field_simp [hL.ne']
    have hellbound : ‖ell-P.ξ‖ < eta/4 := hell.trans_le (min_le_left _ _)
    linarith
  obtain ⟨hinv,hnz,hpos⟩ := hpert _ hnorm
  refine ⟨⟨hinv,hnz⟩,hpos,fun h hj i v => ?_⟩
  apply hess h (ell i) c p _ (hp.trans (min_le_left _ _)) hj v
  calc
    ‖ell i‖ ≤ ‖ell i-P.ξ i‖+‖P.ξ i‖ := by simpa using norm_add_le (ell i-P.ξ i) (P.ξ i)
    _ ≤ ‖ell-P.ξ‖+‖P.ξ‖ := add_le_add (norm_le_pi_norm (ell-P.ξ) i) (norm_le_pi_norm P.ξ i)
    _ ≤ ‖P.ξ‖+1 := by
      have : ‖ell-P.ξ‖ < 1 := hell.trans_le (min_le_right _ _)
      linarith

def centeredSpatialBasis (P : PhaseBasis) (ell : Fin 3 → Base) (L : ℝ)
    (c p : Base) : PhaseBasis :=
  resolvedPhaseBasis P (fun i => phaseDerivative (centeredConvexPhase (ell i) L c) p)

lemma centeredSpatialBasis_covectors (P : PhaseBasis) (ell : Fin 3 → Base) (L : ℝ)
    (c p : Base)
    (hp : admissiblePhaseCovectors P
      (fun i => phaseDerivative (centeredConvexPhase (ell i) L c) p)) :
    (centeredSpatialBasis P ell L c p).ξ =
      fun i => phaseDerivative (centeredConvexPhase (ell i) L c) p :=
  resolvedPhaseBasis_covectors P hp

lemma centeredSpatialBasis_coefficient_smoothAt (P : PhaseBasis) (ell : Fin 3 → Base)
    (L : ℝ) (c : Base) {p : Base}
    (hp : admissiblePhaseCovectors P
      (fun i => phaseDerivative (centeredConvexPhase (ell i) L c) p)) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun x => (centeredSpatialBasis P ell L c x).Q i) p := by
  have hs : ContDiffAt ℝ ∞
      (fun x : Base => fun j : Fin 3 => phaseDerivative (centeredConvexPhase (ell j) L c) x) p := by
    apply contDiffAt_pi.mpr
    intro j
    simp only [centeredConvexPhase_phaseDerivative]
    exact contDiffAt_const.add ((contDiffAt_id.sub contDiffAt_const).const_smul L)
  exact resolvedPhaseBasis_coefficient_smoothAt P hs hp i

/-- A single genuine phase chart contains the entire smaller centered disk. -/
theorem centered_convex_phase_charts_on_disk (ell : Fin 3 → Base)
    (hell : ∀ i, ell i ≠ 0) (c : Base) {L r₀ : ℝ} (hL : 0 ≤ L) (hr₀ : 0 < r₀) :
    ∃ r : ℝ, 0 < r ∧ r ≤ r₀ ∧
      ∃ e : Fin 3 → OpenPartialHomeomorph Base Base,
        (∀ i x, (e i x).1 = centeredConvexPhase (ell i) L c x) ∧
        (∀ i, ContDiff ℝ ∞ (e i) ∧ ContDiffOn ℝ ∞ (e i).symm (e i).target) ∧
        ∀ i p, ‖p-c‖ ≤ r → p ∈ (e i).source := by
  have hcharts (i : Fin 3) :
      ∃ e : OpenPartialHomeomorph Base Base, c ∈ e.source ∧
        (∀ x, (e x).1 = centeredConvexPhase (ell i) L c x) ∧
        ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target := by
    apply exists_smooth_phase_chart (centeredConvexPhase_smooth (ell i) L c)
    apply centeredConvexPhase_regular hL
    simpa only [sub_self,norm_zero,mul_zero] using norm_pos_iff.mpr (hell i)
  choose e he0 hephase hesmooth heinverse using hcharts
  let U : Set Base := ⋂ i, (e i).source
  have hU : IsOpen U := isOpen_iInter_of_finite (fun i => (e i).open_source)
  have hc : c ∈ U := mem_iInter.mpr he0
  obtain ⟨eps,heps,hball⟩ := Metric.isOpen_iff.mp hU c hc
  refine ⟨min r₀ (eps/2),lt_min hr₀ (half_pos heps),min_le_left _ _,
    e,hephase,fun i => ⟨hesmooth i,heinverse i⟩,?_⟩
  intro i p hp
  have hpball : p ∈ Metric.ball c eps := by
    rw [Metric.mem_ball,dist_eq_norm]
    exact (hp.trans (min_le_right _ _)).trans_lt (by linarith)
  exact mem_iInter.mp (hball hpball) i

/-- The actual spatial basis has precisely the centered phase gradients,
positive tensor coefficients, and smoothly varying coefficient maps. -/
theorem compact_centered_spatial_basis (P : PhaseBasis)
    {T : Set PhaseMean.Tensor} (hT : IsCompact T)
    (hTpos : ∀ H ∈ T, ∀ i, 0 < P.Q i H)
    {J : Set MetricFirstJet} (hJ : IsCompact J)
    (hdet : ∀ j ∈ J, metricJetDet j ≠ 0) :
    ∃ L r eps : ℝ, 0 < L ∧ 0 < r ∧ 0 < eps ∧
      ∀ ell : Fin 3 → Base, ‖ell-P.ξ‖ < eps → ∀ c p : Base, ‖p-c‖ ≤ r →
        ((centeredSpatialBasis P ell L c p).ξ =
          fun i => phaseDerivative (centeredConvexPhase (ell i) L c) p) ∧
        (∀ H ∈ T, ∀ i, 0 < (centeredSpatialBasis P ell L c p).Q i H) ∧
        (∀ i, ContDiffAt ℝ ∞ (fun x => (centeredSpatialBasis P ell L c x).Q i) p) ∧
        ∀ h : Base → PhaseMean.Tensor, (h p,fderiv ℝ h p) ∈ J → ∀ i v,
          (L/2)*(v.1^2+v.2^2) ≤
            coordinateMetricHessian h (centeredConvexPhase (ell i) L c) p v v := by
  obtain ⟨L,r,eps,hL,hr,heps,hall⟩ :=
    compact_perturbed_centered_phase_margin P hT hTpos hJ hdet
  refine ⟨L,r,eps,hL,hr,heps,fun ell hell c p hp => ?_⟩
  obtain ⟨hxi,hpos,hess⟩ := hall ell hell c p hp
  refine ⟨centeredSpatialBasis_covectors P ell L c p hxi,?_,
    fun i => centeredSpatialBasis_coefficient_smoothAt P ell L c hxi i,hess⟩
  intro H hH i
  change 0 < (resolvedPhaseBasis P _).Q i H
  rw [resolvedPhaseBasis_coefficients P hxi i]
  exact hpos H hH i

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
