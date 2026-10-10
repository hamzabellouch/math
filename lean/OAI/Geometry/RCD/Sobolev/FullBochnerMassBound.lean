import OAI.Geometry.RCD.Sobolev.FullBochnerCutoffIdentity

namespace OAI

/-! # Quantitative bounds retaining the entire positive Bochner measure -/

open Set Filter MeasureTheory Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

omit [IsFiniteMeasureOnCompacts μ] in
theorem GoodLaplacianCutoff.full_mass_le_cutoff
    {p : X} {r C : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (σ : Measure X) [IsFiniteMeasure σ] :
    σ.real (ball p r) ≤ ∫ x, χ.weight x ∂σ := by
  have hb (x : X) : (ball p r).indicator (fun _ : X => (1:ℝ)) x ≤ χ.weight x := by
    by_cases hx : x∈ball p r
    · simp only [indicator_of_mem hx,χ.one x hx,le_refl]
    · simpa only [indicator_of_notMem hx] using (χ.bounds x).1
  have hi := integral_mono ((integrable_const (1:ℝ) : Integrable (fun _ : X => (1:ℝ)) σ).indicator measurableSet_ball)
    (χ.weight.continuous.integrable_of_hasCompactSupport (χ.hasCompactSupport μ Q)) hb
  simpa only [integral_indicator measurableSet_ball,setIntegral_const,smul_eq_mul,mul_one] using hi

theorem GoodLaplacianCutoff.harmonic_full_mass_bound
    {p : X} {r C K : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (hr : 0 < r) (hC : 0 ≤ C) (hK : K ≤ 0)
    (u G : SobolevSpace μ Q)
    (hG : SobolevSpace.toLp μ Q G =ᵐ[μ] localGamma μ Q u u)
    {Ω : Set X} (hΩ : tsupport (χ.weight : X → ℝ) ⊆ Ω)
    (σ : Measure X) [IsFiniteMeasure σ]
    (hσ : IsMeasureLaplacianOn μ Q Ω G (bochnerGramSource μ Q K u u 0 0 σ.toSignedMeasure))
    (c : ℝ) :
    σ.real (ball p r) ≤
      (C/r^2)/2*(∫ x in closedBall p (2*r), |localGamma μ Q u u x-c| ∂μ)+
      (-K)*((∫ x in closedBall p (2*r), |localGamma μ Q u u x-c| ∂μ)+
        c*μ.real (closedBall p (2*r))) := by
  apply (χ.full_mass_le_cutoff μ Q σ).trans
  rw [χ.harmonic_full_mass_identity μ Q u G hG hΩ σ hσ]
  exact χ.energy_error_mass_bound μ Q hr hC hK u c

omit [BorelSpace X] in
theorem GoodLaplacianCutoff.source_square_bound
    {p : X} {r C : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (d : Lp ℝ 2 μ) (B : ℝ≥0)
    (hB : ∀ᵐ x ∂μ.restrict (closedBall p (2*r)), |d x|≤B) :
    (∫ x, χ.weight x*(d x)^2 ∂μ) ≤ (B:ℝ)^2*μ.real (closedBall p (2*r)) := by
  let S := closedBall p (2*r)
  let : IsFiniteMeasure (μ.restrict S) :=
    ⟨by simpa only [S,Measure.restrict_apply_univ] using (isCompact_closedBall p (2*r)).measure_lt_top⟩
  have he : (∫ x in S, χ.weight x*(d x)^2 ∂μ)=∫ x, χ.weight x*(d x)^2 ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [χ.zero x (by simpa only [S,mem_closedBall,dist_comm,not_le] using hx),zero_mul]
  rw [← he]
  apply (le_abs_self _).trans
  have hb := norm_integral_le_of_norm_le (integrable_const ((B:ℝ)^2)) (show
      ∀ᵐ x ∂μ.restrict S, ‖χ.weight x*(d x)^2‖≤(B:ℝ)^2 from by
    filter_upwards [hB] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (χ.bounds x).1 (sq_nonneg _))]
    have hd : (d x)^2≤(B:ℝ)^2 := by nlinarith [sq_abs (d x),abs_nonneg (d x),B.coe_nonneg]
    exact (mul_le_of_le_one_left (sq_nonneg _) (χ.bounds x).2).trans hd)
  simpa only [S,Real.norm_eq_abs,integral_const,smul_eq_mul,measureReal_restrict_apply_univ,mul_comm] using hb

theorem GoodLaplacianCutoff.source_cross_bound
    {p : X} {r C : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (hr : 0 < r) (hC : 0 ≤ C) (u : SobolevSpace μ Q) (d : Lp ℝ 2 μ) (L B : ℝ≥0)
    (hL : ∀ᵐ x ∂μ.restrict (closedBall p (2*r)), SobolevSpace.minimalSlope μ Q u x≤L)
    (hB : ∀ᵐ x ∂μ.restrict (closedBall p (2*r)), |d x|≤B) :
    weightedGamma μ Q d u χ.sobolev ≤ (B:ℝ)*L*(C/r)*μ.real (closedBall p (2*r)) := by
  let S := closedBall p (2*r)
  let : IsFiniteMeasure (μ.restrict S) :=
    ⟨by simpa only [S,Measure.restrict_apply_univ] using (isCompact_closedBall p (2*r)).measure_lt_top⟩
  have he : (∫ x in S, d x*localGamma μ Q u χ.sobolev x ∂μ)=
      weightedGamma μ Q d u χ.sobolev := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [χ.representative,localGamma_comm μ Q u χ.sobolev,
      localGamma_zero_on_level μ Q χ.sobolev u 0] with x hx hc hz hout
    rw [hc,hz (hx.trans (χ.zero x (by simpa only [S,mem_closedBall,dist_comm,not_le] using hout))),mul_zero]
  have hχ := SobolevSpace.minimalSlope_le_lipschitz μ Q χ.sobolev χ.lipschitz χ.representative
  have hχ' : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ Q χ.sobolev x≤C/r := by
    simpa only [Real.coe_toNNReal _ (div_nonneg hC hr.le)] using hχ
  rw [← he]
  apply (le_abs_self _).trans
  have hb := norm_integral_le_of_norm_le (integrable_const ((B:ℝ)*L*(C/r))) (show
      ∀ᵐ x ∂μ.restrict S, ‖d x*localGamma μ Q u χ.sobolev x‖≤(B:ℝ)*L*(C/r) from by
    filter_upwards [hL,hB,ae_restrict_of_ae hχ',ae_restrict_of_ae (localGamma_abs_le μ Q u χ.sobolev),
      ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ Q χ.sobolev))]
      with x hx hd hc hg hn
    rw [Real.norm_eq_abs,abs_mul]
    calc
      _ ≤ (B:ℝ)*(SobolevSpace.minimalSlope μ Q u x*SobolevSpace.minimalSlope μ Q χ.sobolev x) :=
        mul_le_mul hd hg (abs_nonneg _) B.coe_nonneg
      _ ≤ (B:ℝ)*((L:ℝ)*(C/r)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hx hc hn L.coe_nonneg) B.coe_nonneg
      _ = _ := by ring)
  simpa only [S,Real.norm_eq_abs,integral_const,smul_eq_mul,measureReal_restrict_apply_univ,mul_comm] using hb

theorem GoodLaplacianCutoff.regular_full_mass_bound
    {p : X} {r C K : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (hr : 0 < r) (hC : 0 ≤ C) (hK : K ≤ 0)
    (u d G : SobolevSpace μ Q)
    (hd : IsWeakLaplacian μ Q u (SobolevSpace.toLp μ Q d))
    (hG : SobolevSpace.toLp μ Q G =ᵐ[μ] localGamma μ Q u u)
    {Ω : Set X} (hΩ : tsupport (χ.weight : X → ℝ) ⊆ Ω)
    (σ : Measure X) [IsFiniteMeasure σ]
    (hσ : IsMeasureLaplacianOn μ Q Ω G (bochnerGramSource μ Q K u u d d σ.toSignedMeasure))
    (L B : ℝ≥0)
    (hL : ∀ᵐ x ∂μ.restrict (closedBall p (2*r)), SobolevSpace.minimalSlope μ Q u x≤L)
    (hB : ∀ᵐ x ∂μ.restrict (closedBall p (2*r)), |SobolevSpace.toLp μ Q d x|≤B) :
    σ.real (ball p r) ≤
      ((C/r^2)/2*(L:ℝ)^2+(-K)*(L:ℝ)^2+(B:ℝ)^2+(B:ℝ)*L*(C/r))*
        μ.real (closedBall p (2*r)) := by
  let S := closedBall p (2*r)
  let : IsFiniteMeasure (μ.restrict S) :=
    ⟨by simpa only [S,Measure.restrict_apply_univ] using (isCompact_closedBall p (2*r)).measure_lt_top⟩
  have hi : IntegrableOn (fun x => |localGamma μ Q u u x|) S μ :=
    (localGamma_memL1 μ Q u u).integrableOn.abs
  have hI : (∫ x in S, |localGamma μ Q u u x| ∂μ)≤(L:ℝ)^2*μ.real S := by
    have hh := integral_mono_ae hi (integrable_const ((L:ℝ)^2)) (show
        ∀ᵐ x ∂μ.restrict S, |localGamma μ Q u u x|≤(L:ℝ)^2 from by
      filter_upwards [hL,ae_restrict_of_ae (localGamma_self μ Q u),
        ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ Q u))]
        with x hx he hn
      rw [he,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ hn hx 2)
    simpa only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ,mul_comm] using hh
  have he := χ.energy_error_mass_bound μ Q hr hC hK u 0
  simp only [sub_zero,zero_mul,add_zero] at he
  have he' : (1/2:ℝ)*weightedGamma μ Q χ.laplacian u u-K*weightedGamma μ Q χ.weight u u ≤
      ((C/r^2)/2*(L:ℝ)^2+(-K)*(L:ℝ)^2)*μ.real S := by
    apply he.trans
    have hh := add_le_add (mul_le_mul_of_nonneg_left hI (by positivity : 0≤(C/r^2)/2))
      (mul_le_mul_of_nonneg_left hI (neg_nonneg.mpr hK))
    convert hh using 1
    ring
  have hs := χ.source_square_bound μ Q (SobolevSpace.toLp μ Q d) B hB
  have hc := χ.source_cross_bound μ Q hr hC u (SobolevSpace.toLp μ Q d) L B hL hB
  apply (χ.full_mass_le_cutoff μ Q σ).trans
  rw [χ.full_bochner_mass_identity μ Q u d G hd hG hΩ σ hσ]
  calc
    _ ≤ ((C/r^2)/2*(L:ℝ)^2+(-K)*(L:ℝ)^2)*μ.real S+
        (B:ℝ)^2*μ.real S+(B:ℝ)*L*(C/r)*μ.real S := add_le_add (add_le_add he' hs) hc
    _ = _ := by dsimp only [S]; ring

end RegularPointCoordinates

end

end OAI
