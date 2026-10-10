import OAI.Analysis.RotationWeights.ProductSampling

namespace OAI

noncomputable section

namespace CircleSampling

universe uκ uι

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
section

def scaleEll (m : ℕ) : ℝ := (m:ℝ)^(-(3:ℝ)/5)
def scaleAlpha (m : ℕ) : ℝ := (m:ℝ)^(-(2:ℝ))
def scaleDiscrepancy (m : ℕ) : ℝ := 18*(m:ℝ)^(-(70:ℝ))
def offError (m : ℕ) : ℝ := (2*scaleEll m/(1-scaleEll m))^2 +
  2*(1+scaleEll m)*scaleAlpha m + 4*(1/(scaleEll m*scaleAlpha m))^2*scaleDiscrepancy m

def samplingError (m : ℕ) : ℝ := (1+offError m)^m+(1/2:ℝ)^m -
  2*(1-3*scaleAlpha m)^m+1

lemma rpow_scale_mul (x : ℝ) (hx : 0 < x) (a b : ℝ) : x^a*x^b=x^(a+b) :=
  (Real.rpow_add hx _ _).symm
lemma rpow_scale_sq (x : ℝ) (hx : 0≤x) (a : ℝ) : (x^a)^2=x^(a*2) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx]; norm_num
lemma scale_product {m : ℕ} (hm : 0 < m) : scaleEll m*scaleAlpha m=(m:ℝ)^(-(13:ℝ)/5) := by
  have hx : (0:ℝ) < m := by exact_mod_cast hm
  rw [scaleEll,scaleAlpha,rpow_scale_mul _ hx]; norm_num
lemma mass_offError {m : ℕ} (hm : 0 < m) :
    (m:ℝ)*offError m =
      4*(m:ℝ)^(-(1:ℝ)/5)/(1-scaleEll m)^2 +
      2*(1+scaleEll m)*(m:ℝ)^(-(1:ℝ)) + 72*(m:ℝ)^(-(319:ℝ)/5) := by
  have hx : (0:ℝ) < m := by exact_mod_cast hm
  have h₁ : (m:ℝ)*(scaleEll m)^2=(m:ℝ)^(-(1:ℝ)/5) := by
    rw [scaleEll,rpow_scale_sq _ hx.le]
    conv_lhs => arg 1; rw [← Real.rpow_one (m:ℝ)]
    rw [rpow_scale_mul _ hx]; norm_num
  have h₂ : (m:ℝ)*scaleAlpha m=(m:ℝ)^(-(1:ℝ)) := by
    rw [scaleAlpha]
    conv_lhs => arg 1; rw [← Real.rpow_one (m:ℝ)]
    rw [rpow_scale_mul _ hx]; norm_num
  have h₃ : (m:ℝ)*(1/(scaleEll m*scaleAlpha m))^2*(m:ℝ)^(-(70:ℝ)) =
      (m:ℝ)^(-(319:ℝ)/5) := by
    rw [scale_product hm,one_div,← Real.rpow_neg hx.le,rpow_scale_sq _ hx.le]
    conv_lhs => arg 1; arg 1; rw [← Real.rpow_one (m:ℝ)]
    rw [rpow_scale_mul _ hx,rpow_scale_mul _ hx]; norm_num
  calc
    (m:ℝ)*offError m = 4*((m:ℝ)*(scaleEll m)^2)/(1-scaleEll m)^2 +
        2*(1+scaleEll m)*((m:ℝ)*scaleAlpha m) +
        72*((m:ℝ)*(1/(scaleEll m*scaleAlpha m))^2*(m:ℝ)^(-(70:ℝ))) := by
      unfold offError scaleDiscrepancy
      simp only [div_pow]
      ring
    _ = _ := by rw [h₁,h₂,h₃]

lemma tendsto_nat_rpow_neg {a : ℝ} (ha : 0 < a) :
    Tendsto (fun m : ℕ => (m:ℝ)^(-a)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop
lemma tendsto_scaleEll : Tendsto scaleEll atTop (𝓝 0) := by
  change Tendsto (fun m : ℕ => (m:ℝ)^(-(3:ℝ)/5)) atTop (𝓝 0)
  simpa only [neg_div] using tendsto_nat_rpow_neg (a:=3/5) (by norm_num)
lemma tendsto_scaleAlpha : Tendsto scaleAlpha atTop (𝓝 0) :=
  tendsto_nat_rpow_neg (by norm_num : (0:ℝ)<2)
lemma tendsto_mass_offError : Tendsto (fun m : ℕ => (m:ℝ)*offError m) atTop (𝓝 0) := by
  have ha := tendsto_nat_rpow_neg (by norm_num : (0:ℝ)<1/5)
  have hb := tendsto_nat_rpow_neg (by norm_num : (0:ℝ)<1)
  have hc := tendsto_nat_rpow_neg (by norm_num : (0:ℝ)<319/5)
  have h₁ : Tendsto (fun m : ℕ => 4*(m:ℝ)^(-(1:ℝ)/5)/(1-scaleEll m)^2) atTop (𝓝 0) := by
    convert (ha.const_mul (4:ℝ)).div ((tendsto_const_nhds.sub tendsto_scaleEll).pow 2)
        (by norm_num : (1-(0:ℝ))^2 ≠ 0) using 1
    · ext m; simp only [Pi.div_apply, neg_div]
    · norm_num
  have h₂ : Tendsto (fun m : ℕ => 2*(1+scaleEll m)*(m:ℝ)^(-(1:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using ((tendsto_const_nhds.add tendsto_scaleEll).const_mul 2).mul hb
  have h₃ : Tendsto (fun m : ℕ => 72*(m:ℝ)^(-(319:ℝ)/5)) atTop (𝓝 0) := by
    simpa only [neg_div,mul_zero] using hc.const_mul 72
  have h := (h₁.add h₂).add h₃
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  simpa only [neg_div] using (mass_offError hm).symm
lemma tendsto_mass_alpha : Tendsto (fun m : ℕ => (m:ℝ)*scaleAlpha m) atTop (𝓝 0) := by
  apply (tendsto_nat_rpow_neg (by norm_num : (0:ℝ)<1)).congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  have hx : (0:ℝ) < m := by exact_mod_cast hm
  rw [scaleAlpha]
  conv_rhs => arg 1; rw [← Real.rpow_one (m:ℝ)]
  rw [rpow_scale_mul _ hx]; norm_num
lemma tendsto_samplingError : Tendsto samplingError atTop (𝓝 0) := by
  have ho := Real.tendsto_one_add_pow_exp_of_tendsto tendsto_mass_offError
  have ha : Tendsto (fun m : ℕ => (m:ℝ)*(-3*scaleAlpha m)) atTop (𝓝 0) := by
    simpa only [mul_assoc,mul_comm,mul_left_comm,mul_zero,zero_mul] using tendsto_mass_alpha.const_mul (-3)
  have hl := Real.tendsto_one_add_pow_exp_of_tendsto ha
  have hd := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)
  have hh := ((ho.add hd).sub (hl.const_mul 2)).add_const 1
  change Tendsto (fun m => (1+offError m)^m+(1/2:ℝ)^m - 2*(1-3*scaleAlpha m)^m+1) atTop (𝓝 0)
  convert hh using 1
  · ext m; congr 3; ring
  · norm_num
end
open Filter Set
open scoped Topology
section
lemma eventually_rpow_linear_gap (a b C d : ℝ) (hab : b<a) :
    ∀ᶠ m : ℕ in atTop, C*(m:ℝ)^d*(m:ℝ)^(b*(m:ℝ)) ≤ (m:ℝ)^(a*(m:ℝ)) := by
  have hm : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have he : Tendsto (fun m : ℕ => (a-b)*(m:ℝ)) atTop atTop :=
    hm.const_mul_atTop (sub_pos.mpr hab)
  filter_upwards [hm.eventually_ge_atTop (max 1 C),he.eventually_ge_atTop (d+1)] with m hmin hd
  have hm1 : 1 ≤ (m:ℝ) := (le_max_left _ _).trans hmin
  have hm0 : 0 < (m:ℝ) := lt_of_lt_of_le zero_lt_one hm1
  have hc : C ≤ (m:ℝ) := (le_max_right _ _).trans hmin
  have hpos : 0 ≤ (m:ℝ)^d*(m:ℝ)^(b*(m:ℝ)) := by positivity
  calc
    C*(m:ℝ)^d*(m:ℝ)^(b*(m:ℝ)) ≤ (m:ℝ)*(m:ℝ)^d*(m:ℝ)^(b*(m:ℝ)) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
    _ = (m:ℝ)^(1+d+b*(m:ℝ)) := by rw [Real.rpow_add hm0,Real.rpow_add hm0,Real.rpow_one]
    _ ≤ (m:ℝ)^(a*(m:ℝ)) := Real.rpow_le_rpow_of_exponent_le hm1 (by nlinarith)
open Filter Set
open scoped Topology
lemma inv_scaleEll {m : ℕ} (hm : 0 < m) : (scaleEll m)⁻¹ = (m:ℝ)^((3:ℝ)/5) := by
  have hx : (0:ℝ) < m := by exact_mod_cast hm
  rw [scaleEll, ← Real.rpow_neg hx.le]
  congr 1
  ring
lemma inv_scaleAlpha {m : ℕ} (hm : 0 < m) : (scaleAlpha m)⁻¹ = (m:ℝ)^2 := by
  have hx : (0:ℝ) < m := by exact_mod_cast hm
  rw [scaleAlpha, ← Real.rpow_neg hx.le, neg_neg, Real.rpow_ofNat]
lemma scaleAlpha_pos {m : ℕ} (hm : 0 < m) : 0 < scaleAlpha m := by
  unfold scaleAlpha
  positivity
lemma diagonal_estimate {m : ℕ} (hm : 2 ≤ m) :
    2*((2/scaleEll m)*Real.log (1/(2*scaleAlpha m))) ≤
      8*(m:ℝ)^((3:ℝ)/5)*Real.log m := by
  have hm0 : 0 < m := by omega
  have hx : (0:ℝ) < m := by exact_mod_cast hm0
  have ha := scaleAlpha_pos hm0
  have ht : 0 < 1/(2*scaleAlpha m) := by positivity
  have harg : 1/(2*scaleAlpha m) ≤ (m:ℝ)^2 := by
    rw [one_div,mul_inv_rev, inv_scaleAlpha hm0]
    nlinarith [sq_nonneg (m:ℝ)]
  have hl := Real.log_le_log ht harg
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  rw [div_eq_mul_inv,inv_scaleEll hm0]
  calc
    2*(2*(m:ℝ)^((3:ℝ)/5)*Real.log (1/(2*scaleAlpha m))) ≤
      2*(2*(m:ℝ)^((3:ℝ)/5)*(2*Real.log m)) := by gcongr
    _ = _ := by ring
lemma eventually_diagonal_small : ∀ᶠ m : ℕ in atTop,
    2*((2/scaleEll m)*Real.log (1/(2*scaleAlpha m))) ≤
      (1/2)*(m:ℝ)^((69:ℝ)/100) := by
  have hlim : Tendsto (fun m : ℕ => Real.log (m:ℝ)/(m:ℝ)^((9:ℝ)/100)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 9/100)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/16)),
    eventually_ge_atTop (2:ℕ)] with m hratio hm
  have hm0 : 0 < m := by omega
  have hx : (0:ℝ) < m := by exact_mod_cast hm0
  have hp : 0 < (m:ℝ)^((9:ℝ)/100) := Real.rpow_pos_of_pos hx _
  have hlog := (div_lt_iff₀ hp).mp hratio
  apply (diagonal_estimate hm).trans
  calc
    8*(m:ℝ)^((3:ℝ)/5)*Real.log m ≤
      8*(m:ℝ)^((3:ℝ)/5)*((1/16)*(m:ℝ)^((9:ℝ)/100)) := by gcongr
    _ = (1/2)*((m:ℝ)^((3:ℝ)/5)*(m:ℝ)^((9:ℝ)/100)) := by ring
    _ = _ := by rw [rpow_scale_mul _ hx]; norm_num
end
section
open ContinuousCircleWeight.Sampling
open Filter Set MeasureTheory
open scoped Topology
lemma sampling_discrepancy_numeric {m : ℕ} (hm : 1 ≤ m) {N : ℝ} (hN : 0 < N) :
    8*2*scaleDiscrepancy m/18 + 2/(4*((m^300:ℕ):ℝ)*((m:ℝ)^(-(70:ℝ)))^2) +
      ((m^300:ℕ):ℝ)^2/(Real.pi*(N*(m:ℝ)^1000)*(2/N-1/N)) ≤ scaleDiscrepancy m := by
  have hx1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hx : (0:ℝ) < m := zero_lt_one.trans_le hx1
  have he2 : 2/(4*((m^300:ℕ):ℝ)*((m:ℝ)^(-(70:ℝ)))^2) =
      (1/2)*(m:ℝ)^(-(160:ℝ)) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (m:ℝ) 300, rpow_scale_sq _ hx.le]
    norm_num only [Nat.cast_ofNat]
    have hprod : (m:ℝ)^(300:ℝ)*(m:ℝ)^(-(70:ℝ)*2)=(m:ℝ)^(160:ℝ) := by
      rw [rpow_scale_mul _ hx]; norm_num
    have hexp : -(70:ℝ)*2 = -(140:ℝ) := by norm_num
    rw [hexp] at hprod
    rw [mul_assoc, hprod, div_mul_eq_div_div, div_eq_mul_inv, ← Real.rpow_neg hx.le]
    ring
  have he3 : ((m^300:ℕ):ℝ)^2/(Real.pi*(N*(m:ℝ)^1000)*(2/N-1/N)) =
      (1/Real.pi)*(m:ℝ)^(-(400:ℝ)) := by
    have hden : Real.pi*(N*(m:ℝ)^1000)*(2/N-1/N) = Real.pi*(m:ℝ)^1000 := by
      field_simp
      ring
    rw [hden,Nat.cast_pow,← Real.rpow_natCast (m:ℝ) 300, rpow_scale_sq _ hx.le]
    rw [← Real.rpow_natCast (m:ℝ) 1000]
    norm_num only [Nat.cast_ofNat]
    calc
      (m:ℝ)^(600:ℝ)/(Real.pi*(m:ℝ)^(1000:ℝ)) =
          (1/Real.pi)*((m:ℝ)^(600:ℝ)/(m:ℝ)^(1000:ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_sub hx]; norm_num
  have hle2 : (m:ℝ)^(-(160:ℝ)) ≤ (m:ℝ)^(-(70:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hle3 : (m:ℝ)^(-(400:ℝ)) ≤ (m:ℝ)^(-(70:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hpi : 1/Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three] : (1:ℝ) ≤ Real.pi)
  rw [he2,he3]
  have hp : 0 ≤ (m:ℝ)^(-(400:ℝ)) := Real.rpow_nonneg hx.le _
  have hmul := mul_le_mul_of_nonneg_right hpi hp
  unfold scaleDiscrepancy
  nlinarith [Real.rpow_nonneg hx.le (-(70:ℝ))]

lemma sampling_phase_discrepancy {m : ℕ} (hm : 1 ≤ m) {N c d : ℝ}
    (hN : 0 < N) (hc : 0 < c) (hd : 0 < d)
    (hmc : 1+1/(c*(2/N-1/N)) ≤ 2) (hmd : 1+1/(d*(2/N-1/N)) ≤ 2)
    (hsep : ∀ v w : ℤ, |v| ≤ (m^300:ℕ) → |w| ≤ (m^300:ℕ) →
      (v ≠ 0 ∨ w ≠ 0) → N*(m:ℝ)^1000 ≤ |(v:ℝ)*c+(w:ℝ)*d|)
    (x y : CircleX) (r s : ℝ) :
    |(phasePairLaw (1/N) (2/N) c d).real (Metric.ball x r ×ˢ Metric.ball y s) -
      volume.real (Metric.ball x r)*volume.real (Metric.ball y s)| ≤ scaleDiscrepancy m := by
  have hx : (0:ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hab : 1/N < 2/N := (div_lt_div_iff_of_pos_right hN).mpr (by norm_num)
  have hh := separated_phase_rectangle_bound hab hc hd (by positivity : 0 < N*(m:ℝ)^1000)
    (by norm_num : (0:ℝ) ≤ 2) hmc hmd (H:=m^300) (by positivity)
    (fun v w hv hw hne => hsep v w hv.le hw.le (not_and_or.mp hne))
    (δ:=(m:ℝ)^(-(70:ℝ))) (by positivity) x y r s
  apply hh.trans
  have hn := sampling_discrepancy_numeric hm hN
  unfold scaleDiscrepancy at hn ⊢
  linarith only [hn]
end
section
open Filter Set
open scoped Topology
lemma eventually_sampling_marginal (K : ℕ) : ∀ᶠ m : ℕ in atTop,
    ∀ c : ℝ, (m:ℝ)^((7:ℝ)/10*m)/2 ≤ c →
      0 < c ∧ 1/(c*(2/((m:ℝ)*K)-1/((m:ℝ)*K))) ≤ scaleAlpha m := by
  by_cases hK : K = 0
  · subst K
    filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm c hc
    have hx : (0:ℝ) < m := Nat.cast_pos.mpr (by omega)
    refine ⟨(by positivity : 0 < (m:ℝ)^((7:ℝ)/10*m)/2).trans_le hc,?_⟩
    simpa using (scaleAlpha_pos (by omega : 0 < m)).le
  have hKpos : (0:ℝ) < K := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hK)
  have hg := eventually_rpow_linear_gap (7/10) 0 (2*K) 3 (by norm_num)
  filter_upwards [hg,eventually_ge_atTop (1:ℕ)] with m hg hm c hc
  have hm0 : 0 < m := by omega
  have hx : (0:ℝ) < m := Nat.cast_pos.mpr hm0
  have ha := scaleAlpha_pos hm0
  have hQ : 0 < (m:ℝ)^((7:ℝ)/10*m)/2 := by positivity
  have hcpos := hQ.trans_le hc
  refine ⟨hcpos,?_⟩
  have hg' : 2*(K:ℝ)*(m:ℝ)^3 ≤ (m:ℝ)^((7:ℝ)/10*m) := by
    simpa only [zero_mul,Real.rpow_zero,mul_one,Real.rpow_ofNat] using hg
  have hwidth : 2/((m:ℝ)*K)-1/((m:ℝ)*K) = 1/((m:ℝ)*K) := by ring
  rw [hwidth]
  apply (div_le_iff₀ (by positivity : 0 < c*(1/((m:ℝ)*K)))).mpr
  have hinv := inv_scaleAlpha hm0
  have hmul : scaleAlpha m*(m:ℝ)^2 = 1 := by rw [← hinv]; exact mul_inv_cancel₀ ha.ne'
  have hlarge : (m:ℝ)*K ≤ scaleAlpha m*c := by
    have hh := mul_le_mul_of_nonneg_left hg' ha.le
    have hhh := mul_le_mul_of_nonneg_left hc ha.le
    have hid : scaleAlpha m*(2*(K:ℝ)*(m:ℝ)^3) = 2*((m:ℝ)*K) := by
      calc
        _ = 2*((m:ℝ)*K)*(scaleAlpha m*(m:ℝ)^2) := by ring
        _ = _ := by rw [hmul,mul_one]
    rw [hid] at hh
    nlinarith
  have hh : (1:ℝ) ≤ (scaleAlpha m*c)/((m:ℝ)*K) := (le_div_iff₀ (mul_pos hx hKpos)).mpr (by simpa only [one_mul] using hlarge)
  simpa only [div_eq_mul_inv, mul_assoc, one_mul] using hh
end
section
open ContinuousCircleWeight.Sampling
open Filter Set MeasureTheory
open scoped Topology

def IdealNumerics (K m : ℕ) : Prop :=
  2 ≤ m ∧ scaleEll m < 1 ∧ scaleAlpha m ≤ 1/3 ∧
  2*((2/scaleEll m)*Real.log (1/(2*scaleAlpha m))) ≤ (1/2)*(m:ℝ)^((69:ℝ)/100) ∧
  ∀ c : ℝ, (m:ℝ)^((7:ℝ)/10*m)/2 ≤ c →
    0 < c ∧ 1/(c*(2/((m:ℝ)*K)-1/((m:ℝ)*K))) ≤ scaleAlpha m

lemma eventually_IdealNumerics (K : ℕ) : ∀ᶠ m : ℕ in atTop, IdealNumerics K m := by
  filter_upwards [eventually_ge_atTop (2:ℕ),
    tendsto_scaleEll.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    tendsto_scaleAlpha.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/3)),
    eventually_diagonal_small,eventually_sampling_marginal K] with m hm hℓ hα hd hmean
  exact ⟨hm,hℓ,hα.le,hd,hmean⟩

lemma ideal_stage_error {m K : ℕ} (hK : 0 < K) (hn : IdealNumerics K m)
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (positive : Bool) (c : κ → ℝ)
    (hcard : (m:ℝ)^((69:ℝ)/100*m) ≤ (Fintype.card κ:ℝ))
    (hc : ∀ n, (m:ℝ)^((7:ℝ)/10*m)/2 ≤ c n)
    (hsep : ∀ n k, n ≠ k → ∀ v w : ℤ,
      |v| ≤ (m^300:ℕ) → |w| ≤ (m^300:ℕ) → (v ≠ 0 ∨ w ≠ 0) →
      ((m:ℝ)*K)*(m:ℝ)^1000 ≤ |(v:ℝ)*c n+(w:ℝ)*c k|) :
    (∫ γ : Fin m → ℝ, ∫ s : Fin m → CircleX,
      (idealAverage positive (scaleEll m) (scaleAlpha m) c s γ-1)^2
      ∂Measure.pi (fun _ ↦ volume)
      ∂Measure.pi (fun _ ↦ intervalLaw (1/((m:ℝ)*K)) (2/((m:ℝ)*K)))) ≤ samplingError m := by
  obtain ⟨hm,hℓ1,hα3,hd,hmean⟩ := hn
  have hm0 : 0 < m := by omega
  have hx : (0:ℝ) < m := Nat.cast_pos.mpr hm0
  have hN : 0 < (m:ℝ)*K := mul_pos hx (Nat.cast_pos.mpr hK)
  have hℓ : 0 < scaleEll m := Real.rpow_pos_of_pos hx _
  have hα := scaleAlpha_pos hm0
  have hα2 : scaleAlpha m ≤ 1/2 := by linarith
  have hab : 1/((m:ℝ)*K) < 2/((m:ℝ)*K) := (div_lt_div_iff_of_pos_right hN).mpr (by norm_num)
  have hcm (n : κ) := hmean (c n) (hc n)
  have hD (n : κ) : 1+1/(c n*(2/((m:ℝ)*K)-1/((m:ℝ)*K))) ≤ 2 := by
    linarith [(hcm n).2]
  have hdisc (n k : κ) (hnk : n ≠ k) (x y : CircleX) (r s : ℝ) :=
    sampling_phase_discrepancy (by omega : 1 ≤ m) hN (hcm n).1 (hcm k).1
      (hD n) (hD k) (hsep n k hnk) x y r s
  have he := ideal_error_bound (ι:=Fin m) hab hℓ hℓ1 hα hα2
    (by linarith : 0 ≤ 1-scaleAlpha m) (by norm_num : (0:ℝ) ≤ 2)
    (by unfold scaleDiscrepancy; positivity) positive c (fun n => (hcm n).1)
    (fun n => by linarith [(hcm n).2]) hD hdisc
  simp only [Fintype.card_fin] at he
  have hdiag0 : 0 ≤ 2*((2/scaleEll m)*Real.log (1/(2*scaleAlpha m))) := by
    apply mul_nonneg (by norm_num)
    apply mul_nonneg (by positivity)
    exact Real.log_nonneg ((le_div_iff₀ (by positivity)).mpr (by linarith))
  have hdiag : (Fintype.card κ:ℝ)⁻¹ * (2*((2/scaleEll m)*Real.log (1/(2*scaleAlpha m))))^m ≤ (1/2:ℝ)^m := by
    have hpow : ((m:ℝ)^((69:ℝ)/100))^m = (m:ℝ)^((69:ℝ)/100*m) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]
    have hcpos : (0:ℝ) < Fintype.card κ := Nat.cast_pos.mpr Fintype.card_pos
    rw [mul_comm ((Fintype.card κ:ℝ)⁻¹), ← div_eq_mul_inv]
    apply (div_le_iff₀ hcpos).mpr
    calc
      (2*((2/scaleEll m)*Real.log (1/(2*scaleAlpha m))))^m ≤
        ((1/2)*(m:ℝ)^((69:ℝ)/100))^m := pow_le_pow_left₀ hdiag0 hd m
      _ = (1/2:ℝ)^m*(m:ℝ)^((69:ℝ)/100*m) := by rw [mul_pow,hpow]
      _ ≤ (1/2:ℝ)^m*(Fintype.card κ:ℝ) := by gcongr
  have hbase : 0 ≤ 1-3*scaleAlpha m := by linarith
  have hmeanpow : (1-3*scaleAlpha m)^m ≤ ((1-scaleAlpha m)*(1-2*scaleAlpha m))^m := by
    apply pow_le_pow_left₀ hbase _ m
    nlinarith [sq_nonneg (scaleAlpha m)]
  unfold samplingError
  have hoff : 1+(2*scaleEll m/(1-scaleEll m))^2+2*(1+scaleEll m)*scaleAlpha m+
      4*(1/(scaleEll m*scaleAlpha m))^2*scaleDiscrepancy m = 1+offError m := by
    unfold offError
    ring
  rw [hoff] at he
  linarith
end
section
open ContinuousCircleWeight.Sampling
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
omit [Nonempty κ] in
lemma measurable_idealAverage (positive : Bool) (ℓ α : ℝ) (c : κ → ℝ) :
    Measurable (fun z : (ι → CircleX) × (ι → ℝ) => idealAverage positive ℓ α c z.1 z.2) := by
  unfold idealAverage
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro n _
  apply Finset.measurable_prod
  intro i _
  have hm : Measurable (fun z : (ι → CircleX) × (ι → ℝ) =>
      (z.1 i, ((c n*z.2 i:ℝ):CircleX))) := by fun_prop
  exact (measurable_orientedWeight positive ℓ α).comp hm

lemma idealAverage_bounds (positive : Bool) {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (c : κ → ℝ) (s : ι → CircleX) (γ : ι → ℝ) :
    0 ≤ idealAverage positive ℓ α c s γ ∧
    idealAverage positive ℓ α c s γ ≤ (1/(ℓ*α))^(Fintype.card ι) := by
  have hw i n := orientedWeight_bounds positive hℓ hα (s i) ((c n*γ i:ℝ):CircleX)
  have hcp : (0:ℝ) < Fintype.card κ := Nat.cast_pos.mpr Fintype.card_pos
  unfold idealAverage
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hcp.le) (Finset.sum_nonneg fun n _ => Finset.prod_nonneg fun i _ => (hw i n).1)
  · calc
      _ ≤ (Fintype.card κ:ℝ)⁻¹ * ∑ _n : κ, (1/(ℓ*α))^(Fintype.card ι) := by
        gcongr
        calc
          _ ≤ ∏ _i : ι, (1/(ℓ*α)) := Finset.prod_le_prod₀ (fun i _ => (hw i _).1) (fun i _ => (hw i _).2)
          _ = _ := by simp
      _ = _ := by simp [nsmul_eq_mul,hcp.ne']

def idealEnergy (positive : Bool) (ℓ α : ℝ) (c : κ → ℝ) (γ : ι → ℝ) : ℝ :=
  ∫ s : ι → CircleX, (idealAverage positive ℓ α c s γ-1)^2 ∂Measure.pi (fun _ => volume)

omit [Nonempty κ] in
lemma idealEnergy_nonneg (positive : Bool) (ℓ α : ℝ) (c : κ → ℝ) (γ : ι → ℝ) :
    0 ≤ idealEnergy positive ℓ α c γ := integral_nonneg fun _ => sq_nonneg _

omit [Nonempty κ] in
lemma measurable_idealEnergy (positive : Bool) (ℓ α : ℝ) (c : κ → ℝ) :
    Measurable (idealEnergy (ι:=ι) positive ℓ α c) := by
  unfold idealEnergy
  exact ((((measurable_idealAverage positive ℓ α c).comp measurable_swap).sub measurable_const).pow_const 2).stronglyMeasurable.integral_prod_right.measurable

lemma idealEnergy_le (positive : Bool) {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (c : κ → ℝ) (γ : ι → ℝ) :
    idealEnergy (ι:=ι) positive ℓ α c γ ≤ ((1/(ℓ*α))^(Fintype.card ι)+1)^2 := by
  have hb (s : ι → CircleX) : (idealAverage positive ℓ α c s γ-1)^2 ≤
      ((1/(ℓ*α))^(Fintype.card ι)+1)^2 := by
    have h := idealAverage_bounds positive hℓ hα c s γ
    rw [← sq_abs (idealAverage positive ℓ α c s γ-1)]
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr
    rw [abs_le]
    constructor <;> linarith [pow_nonneg (by positivity : 0 ≤ 1/(ℓ*α)) (Fintype.card ι)]
  have h := integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => sq_nonneg (idealAverage positive ℓ α c s γ-1))
    (integrable_const (μ:=Measure.pi (fun _ : ι => (volume : Measure CircleX))) (((1/(ℓ*α))^(Fintype.card ι)+1)^2)) (Filter.Eventually.of_forall hb)
  simpa [idealEnergy] using h

lemma idealEnergy_integrable (positive : Bool) {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (c : κ → ℝ) (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ] :
    Integrable (idealEnergy (ι:=ι) positive ℓ α c) μ := by
  apply Integrable.of_bound (measurable_idealEnergy positive ℓ α c).aestronglyMeasurable
    (((1/(ℓ*α))^(Fintype.card ι)+1)^2)
  filter_upwards [] with γ
  rw [Real.norm_eq_abs,abs_of_nonneg (idealEnergy_nonneg positive ℓ α c γ)]
  exact idealEnergy_le positive hℓ hα c γ
end
open ContinuousCircleWeight.Sampling
open Set MeasureTheory

def phaseFailure (b : ℝ) (c : ℝ) : Set ℝ :=
  {γ | ¬ (b < 1-repr ((c*γ:ℝ):CircleX) ∧ 1-repr ((c*γ:ℝ):CircleX) < 1-b)}
lemma measurableSet_phaseFailure (b c : ℝ) : MeasurableSet (phaseFailure b c) := by
  apply MeasurableSet.compl
  exact (measurableSet_lt measurable_const (measurable_const.sub
    (measurable_repr.comp ((AddCircle.continuous_mk' 1).measurable.comp (measurable_const.mul measurable_id))))).inter
    (measurableSet_lt (measurable_const.sub
      (measurable_repr.comp ((AddCircle.continuous_mk' 1).measurable.comp (measurable_const.mul measurable_id)))) measurable_const)

lemma phaseFailure_norm (b c γ : ℝ) (hγ : γ ∈ phaseFailure b c) :
    ‖((c*γ:ℝ):CircleX)‖ ≤ b := by
  let x : CircleX := ((c*γ:ℝ):CircleX)
  have h1 : ‖x‖ ≤ repr x := by
    calc
      ‖x‖ = ‖((repr x:ℝ):CircleX)‖ := by rw [coe_repr]
      _ ≤ ‖repr x‖ := QuotientAddGroup.norm_mk_le_norm
      _ = repr x := Real.norm_of_nonneg (repr_mem x).1
  have hx : ((repr x-1:ℝ):CircleX)=x := by
    rw [AddCircle.coe_sub,coe_repr]
    simp
  have h2 : ‖x‖ ≤ 1-repr x := by
    calc
      ‖x‖ = ‖((repr x-1:ℝ):CircleX)‖ := by rw [hx]
      _ ≤ ‖repr x-1‖ := QuotientAddGroup.norm_mk_le_norm
      _ = 1-repr x := by
        rw [Real.norm_eq_abs,abs_of_nonpos (by linarith [(repr_mem x).2])]; ring
  change ¬ (b < 1-repr x ∧ 1-repr x < 1-b) at hγ
  by_contra hb
  have hb' : b < ‖x‖ := lt_of_not_ge hb
  exact hγ ⟨hb'.trans_le h2,by linarith [hb'.trans_le h1]⟩

lemma interval_phase_ball_bound {a b c r : ℝ} (hab : a < b) (hc : 0 < c)
    (hr : 0 ≤ r) :
    (intervalLaw a b).real {γ | ‖((c*γ:ℝ):CircleX)‖ ≤ r} ≤
      (1+1/(c*(b-a)))*(2*r) := by
  have h := phasePairLaw_marginal_fst (d:=0) hab hc (Metric.closedBall (0:CircleX) r)
    measurableSet_closedBall
  rw [Measure.real,phasePairLaw,Measure.map_apply (continuous_phasePair c 0).measurable
    (measurableSet_closedBall.preimage measurable_fst)] at h
  have heq : (phasePair c 0 ⁻¹' (Prod.fst ⁻¹' Metric.closedBall (0:CircleX) r)) =
      {γ | ‖((c*γ:ℝ):CircleX)‖ ≤ r} := by ext γ; simp [phasePair,Metric.mem_closedBall,dist_zero_right]
  rw [heq] at h
  apply h.trans
  gcongr
  rw [Measure.real,AddCircle.volume_closedBall]
  rw [ENNReal.toReal_ofReal (le_min (by norm_num : (0:ℝ) ≤ 1) (mul_nonneg (by norm_num) hr))]
  exact min_le_right _ _

lemma phase_failure_probability {N b c : ℝ} (hN : 0 < N) (hb : 0 ≤ b)
    (hc : N/4 ≤ |c|) :
    intervalLaw (1/N) (2/N) (phaseFailure b c) ≤ ENNReal.ofReal (10*b) := by
  have hab : 1/N < 2/N := (div_lt_div_iff_of_pos_right hN).mpr (by norm_num)
  let := intervalLaw_probability hab
  have hc0 : 0 < |c| := (by positivity : 0 < N/4).trans_le hc
  have hnorm (γ : ℝ) : ‖((c*γ:ℝ):CircleX)‖=‖((|c| *γ:ℝ):CircleX)‖ := by
    rcases le_total 0 c with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,neg_mul,AddCircle.coe_neg,norm_neg]
  have hsub : phaseFailure b c ⊆ {γ | ‖((|c| *γ:ℝ):CircleX)‖ ≤ b} := by
    intro γ hγ
    rw [Set.mem_ofPred_eq,← hnorm]
    exact phaseFailure_norm b c γ hγ
  have hC : 1+1/(|c| *(2/N-1/N)) ≤ 5 := by
    have hh : 2/N-1/N = 1/N := by ring
    rw [hh]
    have hden : (1/4:ℝ) ≤ |c| *(1/N) := by
      have hh : (1/4:ℝ) ≤ |c| /N := (le_div_iff₀ hN).mpr (by linarith only [hc])
      simpa only [div_eq_mul_inv, mul_comm, mul_one, one_mul] using hh
    have hle := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1/4) hden
    norm_num only [one_div_div, div_one] at hle
    linarith only [hle]
  have hμ : (intervalLaw (1/N) (2/N)).real (phaseFailure b c) ≤ 10*b := by
    calc
      _ ≤ (intervalLaw (1/N) (2/N)).real {γ | ‖((|c| *γ:ℝ):CircleX)‖ ≤ b} :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
      _ ≤ (1+1/(|c| *(2/N-1/N)))*(2*b) := interval_phase_ball_bound hab hc0 hb
      _ ≤ 5*(2*b) := mul_le_mul_of_nonneg_right hC (by positivity)
      _ = 10*b := by ring
  rw [← ENNReal.ofReal_toReal (measure_ne_top (intervalLaw (1/N) (2/N)) (phaseFailure b c))]
  exact ENNReal.ofReal_le_ofReal hμ


end CircleSampling

end

end OAI
