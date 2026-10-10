import OAI.Geometry.CylinderCovering.Singular.Basic

namespace OAI

noncomputable section
open Set MeasureTheory Filter Topology Asymptotics
namespace CylinderCovering.FlexibleSingular
open RuledApproximation

lemma labelDomain_volume_vertical (p c d q : ℝ)
    (hcap : ∀ b : ℝ, |b| ≤ 2 → (1/2:ℝ)+c^2*ceilingPolynomial p b+q ≤ 2) :
    volume.real (labelDomain p c d q) = ∫ b in Icc (-2:ℝ) 2,
      max ((1/2:ℝ)+c^2*ceilingPolynomial p b+q-max (d) |b|) 0 := by
  apply plane_volume_vertical_interval (labelDomain_isCompact p c d q).measurableSet
    (labelDomain_isCompact p c d q).measure_lt_top.ne measurableSet_Icc
  intro z
  unfold labelDomain
  simp only [mem_ofPred_eq,mem_Icc,max_le_iff]
  constructor
  · intro hz
    have hb := abs_le.mp (hz.2.2.1.trans hz.2.1)
    exact ⟨hb,⟨⟨hz.1,hz.2.2.1⟩,hz.2.2.2⟩⟩
  · rintro ⟨hb,⟨⟨hd,hb'⟩,hceil⟩⟩
    exact ⟨hd,hceil.trans (hcap (z 0) (abs_le.mpr hb)),hb',hceil⟩

def capQuotient (p c q b : ℝ) : ℝ :=
  (max ((1/2:ℝ)+c^2*ceilingPolynomial p b+q-|b|) 0 -
    max ((1/2:ℝ)-|b|) 0)/c^2

lemma capQuotient_nonneg_bound {p c q b : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) (hc : 0 < c) (hq : 0 ≤ q) :
    0 ≤ capQuotient p c q b ∧
      capQuotient p c q b ≤ ceilingPolynomial p b+q/c^2 := by
  have hd := ceiling_nonneg hp hp2 b
  have hi := positivepart_increment (a := (1/2:ℝ)) (t := |b|)
    (h := c^2*ceilingPolynomial p b+q) (by positivity)
  have he : (c^2*ceilingPolynomial p b+q)/c^2 = ceilingPolynomial p b+q/c^2 := by
    rw [add_div,mul_div_cancel_left₀ _ (pow_ne_zero _ hc.ne')]
  unfold capQuotient
  rw [← add_assoc] at hi
  exact ⟨div_nonneg hi.1 (sq_nonneg c),(div_le_div_of_nonneg_right hi.2 (sq_nonneg c)).trans_eq he⟩

lemma capQuotient_inside {p c q b : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hc : 0 < c) (hq : 0 ≤ q) (hb : |b| ≤ 1/2) :
    capQuotient p c q b = ceilingPolynomial p b+q/c^2 := by
  have hd := ceiling_nonneg hp hp2 b
  have hn : 0 ≤ c^2*ceilingPolynomial p b+q := by positivity
  unfold capQuotient
  rw [max_eq_left (by linarith),max_eq_left (by linarith)]
  have he : ((1/2:ℝ)+c^2*ceilingPolynomial p b+q-|b|-(1/2-|b|)) =
      c^2*ceilingPolynomial p b+q := by ring
  rw [he,add_div,mul_div_cancel_left₀ _ (pow_ne_zero _ hc.ne')]

lemma ceiling_eventually (p : ℝ) {q : ℝ → ℝ}
    (hq : Tendsto q (𝓝[>] 0) (𝓝 0)) :
    ∀ᶠ c : ℝ in 𝓝[>] 0, ∀ b : ℝ, |b| ≤ 2 →
      (1/2:ℝ)+c^2*ceilingPolynomial p b+q c ≤ 2 := by
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (-2:ℝ)) (b := 2)).exists_bound_of_continuousOn
    (ceilingPolynomial_continuous p).continuousOn
  have ht : Tendsto (fun c : ℝ => c^2*C+q c) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using ((h0.pow 2).mul_const C).add hq
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<3/2))] with c hc b hb
  have h := (le_abs_self (ceilingPolynomial p b)).trans (by simpa only [Real.norm_eq_abs] using hC b (abs_le.mp hb))
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg c)
  linarith

lemma capQuotient_tendsto {p : ℝ} {ρ q : ℝ → ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hadm : SingularCutoff.Admissible p ρ q) (b : ℝ) :
    Tendsto (fun c : ℝ => capQuotient p c (q c) b) (𝓝[>] 0)
      (𝓝 ((Icc (-(1/2:ℝ)) (1/2)).indicator (ceilingPolynomial p) b)) := by
  by_cases hb : |b| ≤ 1/2
  · rw [Set.indicator_of_mem (show b ∈ Icc (-(1/2:ℝ)) (1/2) from abs_le.mp hb)]
    have h : Tendsto (fun c : ℝ => ceilingPolynomial p b+q c/c^2) (𝓝[>] 0)
        (𝓝 (ceilingPolynomial p b)) := by
      simpa using hadm.2.2.2.1.tendsto_div_nhds_zero.const_add (ceilingPolynomial p b)
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin, hadm.1] with c hc hpos
    exact (capQuotient_inside hp hp2 hc hpos.2.le hb).symm
  · rw [Set.indicator_of_notMem (by simpa only [mem_Icc,← abs_le] using hb)]
    have ht : Tendsto (fun c : ℝ => (1/2:ℝ)+c^2*ceilingPolynomial p b+q c)
        (𝓝[>] 0) (𝓝 (1/2:ℝ)) := by
      have h0 : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds.add ((h0.pow 2).mul_const (ceilingPolynomial p b))).add
        (SingularCutoff.padding_tendsto_zero hadm)
    apply tendsto_const_nhds.congr'
    filter_upwards [ht.eventually (gt_mem_nhds (lt_of_not_ge hb))] with c hc
    unfold capQuotient
    rw [max_eq_right (by linarith),max_eq_right (by linarith)]
    simp

lemma capQuotient_integral_tendsto {p : ℝ} {ρ q : ℝ → ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hadm : SingularCutoff.Admissible p ρ q) :
    Tendsto (fun c : ℝ => ∫ b in Icc (-2:ℝ) 2, capQuotient p c (q c) b) (𝓝[>] 0)
      (𝓝 (∫ b in Icc (-(1/2:ℝ)) (1/2), ceilingPolynomial p b)) := by
  have hm : ∀ c : ℝ, Continuous (capQuotient p c (q c)) := by
    intro c
    unfold capQuotient
    exact (((continuous_const.add (continuous_const.mul (ceilingPolynomial_continuous p))).add continuous_const).sub continuous_abs).max continuous_const |>.sub
      ((continuous_const.sub continuous_abs).max continuous_const) |>.div_const _
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Icc (-2:ℝ) 2)) (fun b => ceilingPolynomial p b+1)
    (Filter.Eventually.of_forall (fun c => (hm c).aestronglyMeasurable))
    (show ∀ᶠ c : ℝ in 𝓝[>] 0, ∀ᵐ b ∂volume.restrict (Icc (-2:ℝ) 2),
      ‖capQuotient p c (q c) b‖ ≤ ceilingPolynomial p b+1 from by
      have he : ∀ᶠ c : ℝ in 𝓝[>] 0, q c/c^2 < 1 :=
        hadm.2.2.2.1.tendsto_div_nhds_zero.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
      filter_upwards [self_mem_nhdsWithin,he,hadm.1] with c hc hc1 hpos
      exact Filter.Eventually.of_forall (fun b => by
        obtain ⟨h0,h1⟩ := capQuotient_nonneg_bound hp hp2 hc hpos.2.le (b := b)
        rw [Real.norm_eq_abs,abs_of_nonneg h0]
        exact h1.trans (by linarith)))
    (((ceilingPolynomial_continuous p).add continuous_const).continuousOn.integrableOn_Icc)
    (Filter.Eventually.of_forall (capQuotient_tendsto hp hp2 hadm))
  have he : (∫ b in Icc (-2:ℝ) 2, (Icc (-(1/2:ℝ)) (1/2)).indicator (ceilingPolynomial p) b) =
      ∫ b in Icc (-(1/2:ℝ)) (1/2), ceilingPolynomial p b := by
    rw [integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc]
    congr 2
    apply Set.inter_eq_left.mpr
    intro b hb
    constructor <;> linarith [hb.1,hb.2]
  exact he ▸ h
lemma labelDomain_volume_difference {p c d q : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hc : 0 < c) (hd0 : 0 ≤ d) (hq : 0 ≤ q) (hd : d ≤ (1/2:ℝ))
    (hcap : ∀ b : ℝ, |b| ≤ 2 → (1/2:ℝ)+c^2*ceilingPolynomial p b+q ≤ 2) :
    (volume.real (labelDomain p c d q)-(1/4-(d)^2))/c^2 =
      ∫ b in Icc (-2:ℝ) 2, capQuotient p c q b := by
  have hv := coneBand_volume (d := d) (a := (1/2:ℝ)) (by positivity) hd
  norm_num at hv
  rw [← hv,labelDomain_volume_vertical p c d q hcap,coneBand_volume_vertical (by norm_num)]
  have hI₁ : IntegrableOn (fun b : ℝ => max ((1/2:ℝ)+c^2*ceilingPolynomial p b+q-max (d) |b|) 0)
      (Icc (-2:ℝ) 2) := by
    apply ContinuousOn.integrableOn_Icc
    apply Continuous.continuousOn
    exact (((continuous_const.add (continuous_const.mul (ceilingPolynomial_continuous p))).add continuous_const).sub
      (continuous_const.max continuous_abs)).max continuous_const
  have hI₂ : IntegrableOn (fun b : ℝ => max ((1/2:ℝ)-max (d) |b|) 0) (Icc (-2:ℝ) 2) := by
    apply ContinuousOn.integrableOn_Icc
    exact ((continuous_const.sub (continuous_const.max continuous_abs)).max continuous_const).continuousOn
  rw [← integral_sub hI₁ hI₂,← integral_div]
  apply setIntegral_congr_fun measurableSet_Icc
  intro b _
  unfold capQuotient
  apply congrArg (fun x : ℝ => x/c^2)
  have he := positivepart_floor_increment (a := (1/2:ℝ)) (d := d)
    (h := c^2*ceilingPolynomial p b+q) (t := |b|) hd
    (by have := ceiling_nonneg hp hp2 b; positivity)
  simpa only [← add_assoc] using he

lemma labelDomain_volume_tendsto {p : ℝ} {ρ q : ℝ → ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hadm : SingularCutoff.Admissible p ρ q) :
    Tendsto (fun c : ℝ => (volume.real (labelDomain p c (ρ c) (q c))-1/4)/c^2) (𝓝[>] 0)
      (𝓝 (∫ b in Icc (-(1/2:ℝ)) (1/2), ceilingPolynomial p b)) := by
  have h := (capQuotient_integral_tendsto hp hp2 hadm).sub
    (SingularCutoff.tip_area_littleO hadm).tendsto_div_nhds_zero
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,ceiling_eventually p (SingularCutoff.padding_tendsto_zero hadm),
    (SingularCutoff.cutoff_tendsto_zero hadm).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
    hadm.1] with c hc hcap hd hpos
  rw [← labelDomain_volume_difference hp hp2 hc hpos.1.le hpos.2.le hd.le hcap]
  ring

lemma labelDomain_subset_cone (p c d q : ℝ) : labelDomain p c d q ⊆ coneTriangle 2 := by
  intro z hz
  exact ⟨(abs_nonneg _).trans hz.2.2.1,hz.2.1,hz.2.2.1⟩

lemma labelDomain_eventually_mem {p : ℝ} {ρ q : ℝ → ℝ}
    (hp : 0 ≤ p) (hp2 : p ≤ 2) (hadm : SingularCutoff.Admissible p ρ q)
    {z : Plane} (hz : z ∈ coneTriangle 2) (hz1 : 0 < z 1) :
    ∀ᶠ c : ℝ in 𝓝[>] 0, z ∈ labelDomain p c (ρ c) (q c) ↔ z ∈ coneTriangle (1/2) := by
  by_cases hr : z 1 ≤ 1/2
  · filter_upwards [self_mem_nhdsWithin,
      (SingularCutoff.cutoff_tendsto_zero hadm).eventually (gt_mem_nhds hz1),hadm.1]
        with c hc hd hpos
    have hm : z ∈ labelDomain p c (ρ c) (q c) := by
      refine ⟨hd.le,hz.2.1,hz.2.2,hr.trans ?_⟩
      have hn := ceiling_nonneg hp hp2 (z 0)
      have hn' : 0 ≤ c^2*ceilingPolynomial p (z 0)+q c :=
        add_nonneg (mul_nonneg (sq_nonneg c) hn) hpos.2.le
      linarith
    exact ⟨fun _ => ⟨hz.1,hr,hz.2.2⟩,fun _ => hm⟩
  · have ht : Tendsto (fun c : ℝ => (1/2:ℝ)+c^2*ceilingPolynomial p (z 0)+q c)
        (𝓝[>] 0) (𝓝 (1/2:ℝ)) := by
      have h0 : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds.add ((h0.pow 2).mul_const (ceilingPolynomial p (z 0)))).add
        (SingularCutoff.padding_tendsto_zero hadm)
    filter_upwards [ht.eventually (gt_mem_nhds (lt_of_not_ge hr))] with c hc
    exact ⟨fun h => False.elim (not_le_of_gt hc h.2.2.2),fun h => False.elim (hr h.2.1)⟩

lemma flexibleEnergy_integral_tendsto {p : ℝ} {ρ q : ℝ → ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (hadm : SingularCutoff.Admissible p ρ q) :
    Tendsto (fun c : ℝ => ∫ z in labelDomain p c (ρ c) (q c), energyCorrection p c z) (𝓝[>] 0)
      (𝓝 (-(∫ z in coneTriangle (1/2), singularEnergy p z)/2)) := by
  have ht : Tendsto (fun c : ℝ => ∫ z in coneTriangle 2,
      (labelDomain p c (ρ c) (q c)).indicator (energyCorrection p c) z) (𝓝[>] 0)
      (𝓝 (∫ z in coneTriangle 2, (coneTriangle (1/2)).indicator (fun z => -singularEnergy p z/2) z)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun z => singularEnergy p z/2)
    · exact Filter.Eventually.of_forall (fun c =>
        ((energyCorrection_measurable p c).indicator (labelDomain_isCompact p c (ρ c) (q c)).measurableSet).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun c => Filter.Eventually.of_forall (fun z => by
        by_cases hz : z ∈ labelDomain p c (ρ c) (q c)
        · rw [Set.indicator_of_mem hz]
          exact energyCorrection_norm p c z
        · rw [Set.indicator_of_notMem hz,norm_zero]
          exact div_nonneg (singularEnergy_nonneg p z) (by norm_num)))
    · exact (singularEnergy_integrable hp).div_const 2
    · filter_upwards [ae_restrict_mem (coneTriangle_isCompact 2).measurableSet] with z hz
      by_cases hzr : z 1 = 0
      · have he : z = 0 := by
          have hb : z 0 = 0 := abs_nonpos_iff.mp (hz.2.2.trans_eq hzr)
          ext i
          fin_cases i <;> assumption
        subst z
        have he : ∀ c : ℝ, energyCorrection p c 0 = 0 := by simp [energyCorrection,singularEnergy_zero hp]
        simp [Set.indicator,he,singularEnergy_zero hp]
      · have he := labelDomain_eventually_mem (le_trans (by norm_num) hp.le) hp2 hadm hz
          (lt_of_le_of_ne hz.1 (Ne.symm hzr))
        by_cases hza : z ∈ coneTriangle (1/2)
        · rw [Set.indicator_of_mem hza]
          apply (energyCorrection_tendsto p z).congr'
          filter_upwards [he] with c hc
          exact (Set.indicator_of_mem (hc.mpr hza) _).symm
        · rw [Set.indicator_of_notMem hza]
          apply tendsto_const_nhds.congr'
          filter_upwards [he] with c hc
          exact (Set.indicator_of_notMem (fun h => hza (hc.mp h)) _).symm
  have he₁ : ∀ c : ℝ, (∫ z in coneTriangle 2, (labelDomain p c (ρ c) (q c)).indicator (energyCorrection p c) z) =
      ∫ z in labelDomain p c (ρ c) (q c), energyCorrection p c z := by
    intro c
    rw [integral_indicator (labelDomain_isCompact p c (ρ c) (q c)).measurableSet,
      Measure.restrict_restrict (labelDomain_isCompact p c (ρ c) (q c)).measurableSet,
      Set.inter_eq_left.mpr (labelDomain_subset_cone p c (ρ c) (q c))]
  have he₂ : (∫ z in coneTriangle 2, (coneTriangle (1/2)).indicator (fun z => -singularEnergy p z/2) z) =
      -(∫ z in coneTriangle (1/2), singularEnergy p z)/2 := by
    rw [integral_indicator (coneTriangle_isCompact (1/2)).measurableSet,
      Measure.restrict_restrict (coneTriangle_isCompact (1/2)).measurableSet,
      Set.inter_eq_left.mpr (show coneTriangle (1/2) ⊆ coneTriangle 2 from fun z hz =>
        ⟨hz.1,hz.2.1.trans (by norm_num),hz.2.2⟩),integral_div,integral_neg]
  simpa only [he₁,he₂] using ht

lemma flexibleEnergy_integrable {p : ℝ} (hp : 1 < p) (c d q : ℝ) :
    IntegrableOn (energyCorrection p c) (labelDomain p c d q) := by
  apply ((singularEnergy_integrable hp).mono_set (labelDomain_subset_cone p c d q)).div_const 2 |>.mono'
    (energyCorrection_measurable p c).aestronglyMeasurable
  exact Filter.Eventually.of_forall (energyCorrection_norm p c)

lemma weighted_integral_expansion {p : ℝ} (hp : 1 < p) (c d q : ℝ) :
    (∫ z in labelDomain p c d q, physicalWeight (Real.sqrt 2) (c • singularField p z)) =
      volume.real (labelDomain p c d q)+c^2*(∫ z in labelDomain p c d q, energyCorrection p c z) := by
  simp_rw [physicalWeight_energy_expansion]
  rw [integral_add (integrableOn_const (C := (1:ℝ)) (labelDomain_isCompact p c d q).measure_lt_top.ne)
    ((flexibleEnergy_integrable hp c d q).const_mul (c^2)),integral_const_mul]
  simp only [integral_const,smul_eq_mul,mul_one,measureReal_def,Measure.restrict_apply_univ]

lemma weighted_integral_tendsto {p : ℝ} {ρ q : ℝ → ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hadm : SingularCutoff.Admissible p ρ q) :
    Tendsto (fun c : ℝ =>
      ((∫ z in labelDomain p c (ρ c) (q c), physicalWeight (Real.sqrt 2) (c • singularField p z))-1/4)/c^2)
      (𝓝[>] 0) (𝓝 (singularCoefficient p)) := by
  have ht := (labelDomain_volume_tendsto (by linarith : 0 ≤ p) hp2 hadm).add
    (flexibleEnergy_integral_tendsto hp hp2 hadm)
  have hlim : (∫ b in Icc (-(1/2:ℝ)) (1/2), ceilingPolynomial p b) +
      -(∫ z in coneTriangle (1/2), singularEnergy p z)/2 = singularCoefficient p := by
    rw [neg_div,← sub_eq_add_neg]
    exact singular_exact_coefficient hp
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hc0 : c ≠ 0 := ne_of_gt hc
  rw [weighted_integral_expansion hp c (ρ c) (q c)]
  field_simp
  ring

lemma totalCost_quotient_tendsto {p : ℝ} {ρ q : ℝ → ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hadm : SingularCutoff.Admissible p ρ q) :
    Tendsto (fun c : ℝ =>
      (2*cost p c (ρ c) (q c)+8*Real.sqrt 2*(ρ c)^2-Real.sqrt 2/2)/c^2)
      (𝓝[>] 0) (𝓝 (2*Real.sqrt 2*singularCoefficient p)) := by
  have ht := ((weighted_integral_tendsto hp hp2 hadm).const_mul (2*Real.sqrt 2)).add
    ((SingularCutoff.tip_area_littleO hadm).tendsto_div_nhds_zero.const_mul (8*Real.sqrt 2))
  simp only [mul_zero,add_zero] at ht
  apply ht.congr'
  filter_upwards with c
  unfold cost
  ring

lemma asymptotic {p : ℝ} {ρ q : ℝ → ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hadm : SingularCutoff.Admissible p ρ q) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun c => 2*cost p c (ρ c) (q c)+8*Real.sqrt 2*(ρ c)^2-
        (Real.sqrt 2/2+2*Real.sqrt 2*singularCoefficient p*c^2))
      (fun c => c^2) := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · have ht := (totalCost_quotient_tendsto hp hp2 hadm).sub_const (2*Real.sqrt 2*singularCoefficient p)
    simp only [sub_self] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hc0 : c ≠ 0 := ne_of_gt hc
    field_simp
    ring
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact fun h => False.elim ((pow_ne_zero 2 (ne_of_gt hc)) h)

lemma totalCost_small {p : ℝ} {ρ q : ℝ → ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hadm : SingularCutoff.Admissible p ρ q)
    (hk : singularCoefficient p < 0) :
    ∀ᶠ c : ℝ in 𝓝[>] 0,
      2*cost p c (ρ c) (q c)+8*Real.sqrt 2*(ρ c)^2 < Real.sqrt 2/2 := by
  have hk' : 2*Real.sqrt 2*singularCoefficient p < 0 := mul_neg_of_pos_of_neg
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))) hk
  filter_upwards [self_mem_nhdsWithin,
    (totalCost_quotient_tendsto hp hp2 hadm).eventually (gt_mem_nhds hk')] with c hc hcost
  exact sub_neg.mp (by simpa only [zero_mul] using (div_lt_iff₀ (sq_pos_of_pos hc)).mp hcost)

lemma labelDomain_eq_upper_one {p : ℝ} {ρ q : ℝ → ℝ}
    (hadm : SingularCutoff.Admissible p ρ q) :
    ∀ᶠ c : ℝ in 𝓝[>] 0, labelDomain p c (ρ c) (q c) =
      {b : Plane | ρ c ≤ b 1 ∧ b 1 ≤ 1 ∧ |b 0| ≤ b 1 ∧
        b 1 ≤ (1/2:ℝ)+c^2*ceilingPolynomial p (b 0)+q c} := by
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (-2:ℝ)) (b := 2)).exists_bound_of_continuousOn
    (ceilingPolynomial_continuous p).continuousOn
  have h0 : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun c : ℝ => c^2*C+q c) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((h0.pow 2).mul_const C).add (SingularCutoff.padding_tendsto_zero hadm)
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))] with c hc
  ext b
  constructor
  · intro hb
    have hb0 : |b 0| ≤ 2 := hb.2.2.1.trans hb.2.1
    have hpoly : ceilingPolynomial p (b 0) ≤ C :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC (b 0) (abs_le.mp hb0))
    have he := mul_le_mul_of_nonneg_left hpoly (sq_nonneg c)
    exact ⟨hb.1,by linarith [hb.2.2.2],hb.2.2.1,hb.2.2.2⟩
  · intro hb
    exact ⟨hb.1,hb.2.1.trans (by norm_num),hb.2.2.1,hb.2.2.2⟩

end CylinderCovering.FlexibleSingular

end

end OAI
