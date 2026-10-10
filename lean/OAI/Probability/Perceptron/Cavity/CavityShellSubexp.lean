import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityShellLimit

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

lemma cavityShell_subset_closedBall (k : ℕ) :
    cavityShell (k+1) ⊆ Metric.closedBall 0 (Real.sqrt ((k+1:ℕ)+1)) := by
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using
    (Real.le_sqrt (norm_nonneg z) (by positivity)).mpr hz.2

lemma cavityShell_volume_ne_top (k : ℕ) :
    (volume : Measure (Spin (k+1))) (cavityShell (k+1))≠⊤ :=
  ne_of_lt ((measure_mono (cavityShell_subset_closedBall k)).trans_lt
    (isCompact_closedBall _ _).measure_lt_top)

lemma cavity_sqrt_power_gap (k : ℕ) :
    (Real.sqrt (k+1:ℕ))^(k+1)/(2*((k+1:ℕ)+1)) ≤
      (Real.sqrt ((k+1:ℕ)+1))^(k+1)-(Real.sqrt (k+1:ℕ))^(k+1) := by
  let a:=Real.sqrt (k+1:ℕ)
  let b:=Real.sqrt ((k+1:ℕ)+1)
  have ha : 0<a := Real.sqrt_pos.mpr (by positivity)
  have hb : 0<b := Real.sqrt_pos.mpr (by positivity)
  have hab : a≤b := Real.sqrt_le_sqrt (by linarith)
  have ha2 : a^2=(k+1:ℕ) := Real.sq_sqrt (by positivity)
  have hb2 : b^2=((k+1:ℕ)+1) := Real.sq_sqrt (by positivity)
  have hdiff : (b-a)*(b+a)=1 := by nlinarith
  have hlarge : a*(b+a)≤2*b^2 := by nlinarith [sq_nonneg (b-a)]
  have hsmall : a≤2*((k+1:ℕ)+1)*(b-a) := by
    have hh:=mul_le_mul_of_nonneg_right hlarge (sub_nonneg.mpr hab)
    nlinarith
  have hp : a^k≤b^k := pow_le_pow_left₀ ha.le hab k
  have hx : a^k*(b-a)≤b^(k+1)-a^(k+1) := by
    rw [pow_succ,pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right hp hb.le]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2*((k+1:ℕ)+1))).mpr
  calc
    a^(k+1)=a^k*a := pow_succ _ _
    _≤a^k*(2*((k+1:ℕ)+1)*(b-a)) := mul_le_mul_of_nonneg_left hsmall (pow_nonneg ha.le _)
    _=(a^k*(b-a))*(2*((k+1:ℕ)+1)) := by ring
    _≤(b^(k+1)-a^(k+1))*(2*((k+1:ℕ)+1)) := mul_le_mul_of_nonneg_right hx (by positivity)

lemma cavityShell_volume_lower (k : ℕ) :
    (Real.sqrt (k+1:ℕ))^(k+1)/(2*((k+1:ℕ)+1)) *
       (volume : Measure (Spin (k+1))).real (Metric.closedBall 0 1) ≤
      (volume : Measure (Spin (k+1))).real (cavityShell (k+1)) := by
  let A : Set (Spin (k+1)) := Metric.closedBall 0 (Real.sqrt ((k+1:ℕ)+1))
  let B : Set (Spin (k+1)) := Metric.closedBall 0 (Real.sqrt (k+1:ℕ))
  have hBA : B⊆A := Metric.closedBall_subset_closedBall (Real.sqrt_le_sqrt (by linarith))
  have hs : A\B⊆cavityShell (k+1) := by
    intro z hz
    have ha : ‖z‖≤Real.sqrt ((k+1:ℕ)+1) := by simpa only [A,Metric.mem_closedBall,dist_zero_right] using hz.1
    have hb : Real.sqrt (k+1:ℕ)<‖z‖ := by simpa only [B,Metric.mem_closedBall,dist_zero_right,not_le] using hz.2
    constructor
    · nlinarith [Real.sq_sqrt (show (0:ℝ)≤(k+1:ℕ) by positivity),norm_nonneg z,Real.sqrt_nonneg ((k+1:ℕ):ℝ)]
    · nlinarith [Real.sq_sqrt (show (0:ℝ)≤(k+1:ℕ)+1 by positivity),norm_nonneg z,Real.sqrt_nonneg ((k+1:ℕ)+1)]
  have hvol : (volume : Measure (Spin (k+1))).real (A\B)=
      ((Real.sqrt ((k+1:ℕ)+1))^(k+1)-(Real.sqrt (k+1:ℕ))^(k+1)) *
        (volume : Measure (Spin (k+1))).real (Metric.closedBall 0 1) := by
    rw [measureReal_sdiff hBA (Metric.isClosed_closedBall.measurableSet) (isCompact_closedBall _ _).measure_ne_top]
    simp only [A,B,Measure.addHaar_real_closedBall' (volume : Measure (Spin (k+1))) 0 (Real.sqrt_nonneg _),finrank_euclideanSpace,Fintype.card_fin]
    ring
  apply (mul_le_mul_of_nonneg_right (cavity_sqrt_power_gap k) measureReal_nonneg).trans
  rw [←hvol]
  exact measureReal_mono hs (cavityShell_volume_ne_top k)

lemma cavityShell_density_lower (k : ℕ) :
    radialNormalizer k * Real.exp (-((k+1:ℕ)+1)/2) *
      (volume : Measure (Spin (k+1))).real (cavityShell (k+1)) ≤ cavityShellMass k := by
  change _≤(stdGaussian (Spin (k+1))).real _
  rw [←canonicalRadialMass_eq_stdGaussian,canonicalRadialMass_real_apply (by norm_num : (0:ℝ)<1) (cavityShell_measurable _)]
  have h := setIntegral_mono_on (integrableOn_const (cavityShell_volume_ne_top k) (C:=radialNormalizer k*Real.exp (-((k+1:ℕ)+1)/2)))
    (canonicalRadialDensity_integrable k (by norm_num : (0:ℝ)<1)).integrableOn (cavityShell_measurable (k+1))
    (fun z hz=>show radialNormalizer k*Real.exp (-((k+1:ℕ)+1)/2)≤canonicalRadialDensity k 1 z from by
      unfold canonicalRadialDensity
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (radialNormalizer_pos k).le
      have hh:=hz.2
      change ‖z‖^2≤(k+1:ℕ)+1 at hh
      nlinarith)
  simpa only [integral_const,measureReal_restrict_apply MeasurableSet.univ,univ_inter,smul_eq_mul,mul_comm] using h

lemma cavity_band_density_upper (k : ℕ) {ε : ℝ} (hε : 0≤ε) :
    (canonicalRadialMass k 1).real (normSquareBand k ε)≤
      radialNormalizer k * Real.exp (-((k+1:ℕ)*(1-ε))/2) *
        (Real.sqrt ((k+1:ℕ)*(1+ε)))^(k+1) *
          (volume : Measure (Spin (k+1))).real (Metric.closedBall 0 1) := by
  have hs : normSquareBand k ε ⊆ Metric.closedBall (0:Spin (k+1)) (Real.sqrt ((k+1:ℕ)*(1+ε))) := by
    intro z hz
    simpa only [Metric.mem_closedBall,dist_zero_right] using
      (Real.le_sqrt (norm_nonneg z) (by positivity)).mpr hz.2
  have hf : (volume : Measure (Spin (k+1))) (normSquareBand k ε)≠⊤ :=
    ne_of_lt ((measure_mono hs).trans_lt (isCompact_closedBall _ _).measure_lt_top)
  rw [canonicalRadialMass_real_apply (by norm_num : (0:ℝ)<1) (normSquareBand_measurable _ _)]
  have hi := setIntegral_mono_on (canonicalRadialDensity_integrable k (by norm_num : (0:ℝ)<1)).integrableOn
    (integrableOn_const hf (C:=radialNormalizer k * Real.exp (-((k+1:ℕ)*(1-ε))/2))) (normSquareBand_measurable k ε)
    (fun z hz=>show canonicalRadialDensity k 1 z≤radialNormalizer k*Real.exp (-((k+1:ℕ)*(1-ε))/2) from by
      unfold canonicalRadialDensity
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (radialNormalizer_pos k).le
      have hh:=hz.1
      change (k+1:ℕ)*(1-ε)≤‖z‖^2 at hh
      nlinarith)
  simp only [integral_const,measureReal_restrict_apply MeasurableSet.univ,univ_inter,smul_eq_mul] at hi
  apply hi.trans
  have hm := measureReal_mono (μ:=(volume : Measure (Spin (k+1)))) hs (isCompact_closedBall _ _).measure_ne_top
  rw [Measure.addHaar_real_closedBall' (volume : Measure (Spin (k+1))) 0 (Real.sqrt_nonneg _),finrank_euclideanSpace,Fintype.card_fin] at hm
  convert mul_le_mul_of_nonneg_left hm (mul_pos (radialNormalizer_pos k) (Real.exp_pos (-((k+1:ℕ)*(1-ε))/2))).le using 1 <;> ring

lemma cavity_sqrt_pow_exp (k : ℕ) {ε : ℝ} (_hε : 0≤ε) :
    (Real.sqrt (1+ε))^(k+1)≤Real.exp (ε*(k+1:ℕ)/2) := by
  have hh : Real.sqrt (1+ε)≤Real.exp (ε/2) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨(Real.exp_pos _).le,?_⟩
    rw [←Real.exp_nat_mul]
    convert Real.add_one_le_exp ε using 1 <;> ring_nf
  have hp:=pow_le_pow_left₀ (Real.sqrt_nonneg _) hh (k+1)
  rw [←Real.exp_nat_mul] at hp
  convert hp using 1
  congr 1
  ring

lemma cavityShell_band_comparison (k : ℕ) {ε : ℝ} (hε : 0≤ε) :
    (canonicalRadialMass k 1).real (normSquareBand k ε)≤
      cavityShellMass k * (2*((k+1:ℕ)+1))*Real.exp (ε*(k+1:ℕ)+1/2) := by
  let D:=radialNormalizer k * (Real.sqrt (k+1:ℕ))^(k+1) *
    (volume : Measure (Spin (k+1))).real (Metric.closedBall 0 1)
  have hD : 0≤D := by
    exact mul_nonneg (mul_nonneg (radialNormalizer_pos k).le
      (pow_nonneg (Real.sqrt_nonneg _) _)) measureReal_nonneg
  have hl : D*Real.exp (-((k+1:ℕ)+1)/2)/(2*((k+1:ℕ)+1))≤cavityShellMass k := by
    have hv:=mul_le_mul_of_nonneg_left (cavityShell_volume_lower k)
      (mul_pos (radialNormalizer_pos k) (Real.exp_pos (-((k+1:ℕ)+1)/2))).le
    apply le_trans _ (cavityShell_density_lower k)
    convert hv using 1
    dsimp only [D]
    ring
  have hb : (canonicalRadialMass k 1).real (normSquareBand k ε)≤
      D*Real.exp (-((k+1:ℕ)*(1-ε))/2)*Real.exp (ε*(k+1:ℕ)/2) := by
    apply (cavity_band_density_upper k hε).trans
    rw [Real.sqrt_mul (by positivity),mul_pow]
    have hh := mul_le_mul_of_nonneg_left (cavity_sqrt_pow_exp k hε)
      (show 0≤D*Real.exp (-((k+1:ℕ)*(1-ε))/2) by positivity)
    convert hh using 1
    dsimp only [D]
    ring
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_right hl
    (show 0≤(2*((k+1:ℕ)+1))*Real.exp (ε*(k+1:ℕ)+1/2) by positivity)
  convert hh using 1
  · rw [mul_assoc D,←Real.exp_add]
    rw [div_mul_eq_mul_div,eq_div_iff (by positivity : (2*((k+1:ℕ)+1):ℝ)≠0)]
    rw [show D*Real.exp (-((k+1:ℕ)+1)/2)*((2*((k+1:ℕ)+1))*Real.exp (ε*(k+1:ℕ)+1/2))=
        D*(Real.exp (-((k+1:ℕ)+1)/2)*Real.exp (ε*(k+1:ℕ)+1/2))*(2*((k+1:ℕ)+1)) by ring,←Real.exp_add]
    congr 2
    ring_nf
  · ring

lemma cavityShell_log_lower (k : ℕ) {ε : ℝ} (hε : 0≤ε)
    (hb : (1/2:ℝ)≤(canonicalRadialMass k 1).real (normSquareBand k ε)) :
    -ε*(k+1:ℕ)-1/2-Real.log (4*((k+1:ℕ)+1))≤Real.log (cavityShellMass k) := by
  have h := Real.log_le_log (by norm_num : (0:ℝ)<1/2) (hb.trans (cavityShell_band_comparison k hε))
  rw [Real.log_mul (mul_pos (cavityShellMass_pos k) (by positivity)).ne' (Real.exp_pos _).ne',
    Real.log_mul (cavityShellMass_pos k).ne' (by positivity : (2*((k+1:ℕ)+1):ℝ)≠0),Real.log_exp,
    Real.log_div (by norm_num : (1:ℝ)≠0) (by norm_num : (2:ℝ)≠0),Real.log_one] at h
  have he : Real.log (4*((k+1:ℕ)+1))=Real.log 2+Real.log (2*((k+1:ℕ)+1)) := by
    rw [←Real.log_mul (by norm_num : (2:ℝ)≠0) (by positivity : (2*((k+1:ℕ)+1):ℝ)≠0)]
    congr 1
    ring
  rw [he]
  linarith

lemma cavityShell_log_error_tendsto :
    Tendsto (fun k : ℕ=>(1/2+Real.log (4*((k+1:ℕ)+1)))/(k+1:ℕ)) atTop (𝓝 (0:ℝ)) := by
  have hN : Tendsto (fun k : ℕ=>((k+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have ht := (Real.tendsto_pow_log_div_mul_add_atTop (1/4) (-1) 1 (by norm_num)).comp
    ((tendsto_atTop_add_const_right _ 1 hN).const_mul_atTop (by norm_num : (0:ℝ)<4))
  have ht' : Tendsto (fun k : ℕ=>Real.log (4*((k+1:ℕ)+1))/(k+1:ℕ)) atTop (𝓝 (0:ℝ)) := by
    convert ht using 1
    funext k
    dsimp only [Function.comp_def]
    rw [pow_one]
    congr 1
    ring
  have hi := (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(1/2:ℝ)) atTop (𝓝 (1/2))).mul
    (tendsto_inv_atTop_zero.comp hN)
  convert hi.add ht' using 1 <;> simp only [mul_zero,zero_add,div_eq_mul_inv,add_mul,Function.comp_def]

theorem cavityShell_log_sublinear :
    Tendsto (fun k : ℕ=>Real.log (cavityShellMass k)/(k+1:ℕ)) atTop (𝓝 (0:ℝ)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    let ε : ℝ:=min (-a/2) (1/2)
    have he : 0<ε := lt_min (by linarith) (by norm_num)
    have he1 : ε<1 := (min_le_right _ _).trans_lt (by norm_num)
    have hae : a < -ε := by
      have hh : ε≤-a/2 := min_le_left _ _
      dsimp only [ε] at hh ⊢
      linarith
    have ht : Tendsto (fun k : ℕ=>-ε-(1/2+Real.log (4*((k+1:ℕ)+1)))/(k+1:ℕ)) atTop (𝓝 (-ε)) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub cavityShell_log_error_tendsto
    filter_upwards [ht.eventually (lt_mem_nhds hae),canonicalRadial_band_eventually_half he he1] with k hk hb
    apply hk.trans_le
    have hh:=div_le_div_of_nonneg_right (cavityShell_log_lower k he.le hb)
      (by positivity : (0:ℝ)≤(k+1:ℕ))
    convert hh using 1
    field_simp
    ring
  · intro b hb
    filter_upwards [] with k
    have hh := Real.log_nonpos (cavityShellMass_pos k).le (cavityShellMass_le_one k)
    exact (div_nonpos_of_nonpos_of_nonneg hh (by positivity)).trans_lt hb

end SphericalPerceptronFreeEnergy
end

end OAI
