import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Stable.SmoothRemainder

namespace OAI

section
section
namespace StandardMapEntropy.NonlinearStable
open Filter
open scoped Topology NNReal

noncomputable def unitClip (x : ℝ) : ℝ := max (min x 1) (-1)
lemma abs_unitClip_le (x : ℝ) : |unitClip x|≤1 := by
  rw [abs_le]
  exact ⟨le_max_right _ _,max_le (min_le_right _ _) (by norm_num)⟩
lemma unitClip_eq {x : ℝ} (hx : |x|≤1) : unitClip x=x := by
  rw [abs_le] at hx
  simp only [unitClip,min_eq_left hx.2,max_eq_left hx.1]
lemma unitClip_lipschitz : LipschitzWith 1 unitClip :=
  (LipschitzWith.id.min_const 1).max_const (-1)

noncomputable def planeClip (v : Plane) : Plane := (unitClip v.1,unitClip v.2)
lemma norm_planeClip_le (v : Plane) : ‖planeClip v‖≤1 :=
  max_le (abs_unitClip_le _) (abs_unitClip_le _)
lemma planeClip_eq {v : Plane} (hv : ‖v‖≤1) : planeClip v=v := by
  exact Prod.ext (unitClip_eq ((norm_fst_le v).trans hv)) (unitClip_eq ((norm_snd_le v).trans hv))
@[simp] lemma planeClip_zero : planeClip 0=0 := planeClip_eq (by simp)
lemma planeClip_lipschitz : LipschitzWith 1 planeClip := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one,one_mul,Prod.dist_eq,planeClip]
  have h1 := unitClip_lipschitz.dist_le_mul v.1 w.1
  have h2 := unitClip_lipschitz.dist_le_mul v.2 w.2
  simp only [NNReal.coe_one,one_mul] at h1 h2
  exact max_le_max h1 h2

structure LocalRecurrence (ℓ δ : ℝ≥0) where
  a : ℕ → ℝ
  b : ℕ → ℝ
  remainder : ℕ → Plane → Plane
  stable_bound : ∀ n, |a n|≤ℓ
  inverse_bound : ∀ n, |(b n)⁻¹|≤ℓ
  b_ne : ∀ n, b n≠0
  local_lipschitz : ∀ n v w, ‖v‖≤1 → ‖w‖≤1 →
    ‖remainder n v-remainder n w‖≤(δ : ℝ)*‖v-w‖
  zero : ∀ n, remainder n 0=0

variable {ℓ δ : ℝ≥0}
def LocalRecurrence.step (r : LocalRecurrence ℓ δ) (n : ℕ) (v : Plane) : Plane :=
  (r.a n*v.1+(r.remainder n v).1,r.b n*v.2+(r.remainder n v).2)
noncomputable def LocalRecurrence.extend (r : LocalRecurrence ℓ δ) : Recurrence ℓ δ where
  a := r.a
  b := r.b
  remainder n v := r.remainder n (planeClip v)
  stable_bound := r.stable_bound
  inverse_bound := r.inverse_bound
  b_ne := r.b_ne
  lipschitz n := LipschitzWith.of_dist_le_mul fun v w => by
    have hh := r.local_lipschitz n (planeClip v) (planeClip w) (norm_planeClip_le v) (norm_planeClip_le w)
    have he := planeClip_lipschitz.dist_le_mul v w
    simp only [dist_eq_norm,NNReal.coe_one,one_mul] at he ⊢
    exact hh.trans (mul_le_mul_of_nonneg_left he δ.coe_nonneg)
  zero n := by rw [planeClip_zero,r.zero]

lemma extend_step_eq (r : LocalRecurrence ℓ δ) (n : ℕ) {v : Plane} (hv : ‖v‖≤1) :
    r.extend.step n v=r.step n v := by
  simp only [LocalRecurrence.extend,Recurrence.step,LocalRecurrence.step,planeClip_eq hv]

lemma local_solution_bound (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1) {s : ℝ} (hs : |s|≤1) (n : ℕ) :
    ‖r.extend.solution h s n‖≤1 :=
  ((r.extend.solution h s).norm_coe_le_norm n).trans ((solution_norm_bound _ h s).trans hs)
lemma local_solution_orbit (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1) {s : ℝ} (hs : |s|≤1) (n : ℕ) :
    r.extend.solution h s (n+1)=r.step n (r.extend.solution h s n) := by
  rw [solution_orbit,extend_step_eq r n (local_solution_bound r h hs n)]

theorem local_stable_graph (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1) :
    ∃ g : ℝ → ℝ, g 0=0 ∧ LipschitzWith 1 g ∧
      ∀ s : ℝ, |s|≤1 → ∃ x : ℕ → Plane, x 0=(s,g s) ∧
        (∀ n, x (n+1)=r.step n (x n)) ∧
        (∀ n, ‖x n‖≤((ℓ+δ : ℝ≥0) : ℝ)^n*|s|) := by
  refine ⟨r.extend.graph h,graph_zero _ h,graph_lipschitz _ h,fun s hs =>
    ⟨r.extend.solution h s,Prod.ext (solution_initial _ h s) rfl,local_solution_orbit r h hs,?_⟩⟩
  intro n
  simpa [solution_zero] using solution_exponential_contraction r.extend h s 0 n

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

noncomputable def hyperbolicChartRate (χ : ℝ) : ℝ := Real.exp (-χ/2)
noncomputable def hyperbolicChartError (χ : ℝ) : ℝ := (1-hyperbolicChartRate χ)/2
noncomputable def hyperbolicChartScale (k χ : ℝ) : ℝ :=
  hyperbolicChartError χ/(8*(1+derivativeVariationBound k)*Real.exp χ)
lemma hyperbolicChartRate_pos (χ : ℝ) : 0<hyperbolicChartRate χ := Real.exp_pos _
lemma hyperbolicChartRate_lt_one {χ : ℝ} (hχ : 0<χ) : hyperbolicChartRate χ<1 := by
  apply Real.exp_lt_one_iff.mpr
  linarith
lemma hyperbolicChartError_pos {χ : ℝ} (hχ : 0<χ) : 0<hyperbolicChartError χ := by
  have hh := hyperbolicChartRate_lt_one hχ
  unfold hyperbolicChartError
  linarith
lemma hyperbolicChartScale_pos (k : ℝ) {χ : ℝ} (hχ : 0<χ) : 0<hyperbolicChartScale k χ := by
  exact div_pos (hyperbolicChartError_pos hχ)
    (mul_pos (mul_pos (by norm_num) (by linarith [derivativeVariationBound_nonneg k])) (Real.exp_pos χ))
lemma hyperbolicChartScale_le {k χ : ℝ} (hχ : 0<χ) : hyperbolicChartScale k χ≤1/16 := by
  have hD := derivativeVariationBound_nonneg k
  have hE : 1≤Real.exp χ := Real.one_le_exp_iff.mpr hχ.le
  have he : hyperbolicChartError χ≤1/2 := by
    unfold hyperbolicChartError
    linarith [hyperbolicChartRate_pos χ]
  have hden : 8≤8*(1+derivativeVariationBound k)*Real.exp χ := by nlinarith
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ)<8) hden)).mpr
  nlinarith

noncomputable def chartSize (k χ : ℝ) (z : Torus) : ℝ :=
  hyperbolicChartScale k χ*chartRadius k χ (χ/2) z
noncomputable def actualChartFrame (k χ : ℝ) (z : Torus) : RealPlane →L[ℝ] ℂ :=
  flatFrame (chartSize k χ z) (lyapunovFrame k χ z)
noncomputable def actualChartInverse (k χ : ℝ) (z : Torus) : ℂ →L[ℝ] RealPlane :=
  flatInverse (chartSize k χ z) (lyapunovCoframe k χ z)
noncomputable def actualStableMultiplier (k χ : ℝ) (z : Torus) : ℝ :=
  chartSize k χ z/chartSize k χ (standardMap k z)*stableMultiplier k χ z
noncomputable def actualUnstableMultiplier (k χ : ℝ) (z : Torus) : ℝ :=
  chartSize k χ z/chartSize k χ (standardMap k z)*unstableMultiplier k χ z
lemma chartSize_pos (k : ℝ) {χ : ℝ} (hχ : 0<χ) (z : Torus) : 0<chartSize k χ z :=
  mul_pos (hyperbolicChartScale_pos k hχ) (chartRadius_pos k χ (χ/2) z)
lemma chartSize_le_scale (k : ℝ) {χ : ℝ} (hχ : 0<χ) (z : Torus) :
    chartSize k χ z≤hyperbolicChartScale k χ := by
  exact (mul_le_mul_of_nonneg_left (chartRadius_le_one k χ (χ/2) z)
    (hyperbolicChartScale_pos k hχ).le).trans_eq (mul_one _)
lemma actualChartFrame_norm_le (k : ℝ) {χ : ℝ} (hχ : 0<χ) (z : Torus) :
    ‖actualChartFrame k χ z‖≤2*chartSize k χ z :=
  flatFrame_norm_le (chartSize_pos k hχ z).le (lyapunovFrame_norm_le k χ z)
lemma actualChartInverse_frame (k : ℝ) {χ : ℝ} (hχ : 0<χ) (z : Torus)
    (hw : wedge (stableVector k z) (unstableVector k z)≠0) (v : RealPlane) :
    actualChartInverse k χ z (actualChartFrame k χ z v)=v :=
  flatInverse_frame (ne_of_gt (chartSize_pos k hχ z)) (lyapunovCoframe_frame k χ z hw) v
lemma actualChartFrame_inverse (k : ℝ) {χ : ℝ} (hχ : 0<χ) (z : Torus)
    (hw : wedge (stableVector k z) (unstableVector k z)≠0) (v : ℂ) :
    actualChartFrame k χ z (actualChartInverse k χ z v)=v :=
  flatFrame_inverse (ne_of_gt (chartSize_pos k hχ z)) (lyapunovFrame_coframe k χ z hw) v

def RegularChartPoint (k χ : ℝ) (z : Torus) : Prop :=
  wedge (stableVector k z) (unstableVector k z)≠0 ∧
  (lyapunovCoframe k χ (standardMap k z)).comp
    ((standardDerivative k z).comp (lyapunovFrame k χ z)) =
      diagonalPlane (stableMultiplier k χ z) (unstableMultiplier k χ z) ∧
  |stableMultiplier k χ z|≤Real.exp (-χ) ∧
  Real.exp χ≤|unstableMultiplier k χ z| ∧
  chartRadius k χ (χ/2) z*‖lyapunovCoframe k χ z‖≤1 ∧
  Real.exp (-(χ/2))*chartRadius k χ (χ/2) z≤chartRadius k χ (χ/2) (standardMap k z) ∧
  Real.exp (-(χ/2))*chartRadius k χ (χ/2) (standardMap k z)≤chartRadius k χ (χ/2) z

lemma ae_regularChartPoint (k : ℝ) (hk : 0≤k) {χ : ℝ} (hχ : 0<χ) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ), RegularChartPoint k χ z := by
  filter_upwards [ae_restrict_mem (measurableSet_spectralGapRegion k hk χ),
    (ae_transverseLines k hk).filter_mono Measure.absolutelyContinuous_restrict.ae_le,
    ae_lyapunov_normal_form k hk χ hχ.le,ae_stableMultiplier_bound k hk χ hχ.le,
    ae_unstableMultiplier_bound k hk χ hχ.le,ae_chartRadius_control k hk χ hχ.le (χ/2) (by linarith)]
    with z hz ht hn hs hu hr
  exact ⟨ht (hχ.trans hz),hn,hs,hu,hr⟩

lemma ae_regularChartPoint_all_iterates (k : ℝ) (hk : 0≤k) {χ : ℝ} (hχ : 0<χ) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      ∀ n : ℕ, RegularChartPoint k χ ((standardMap k)^[n] z) ∧
        RegularChartPoint k χ ((inverseMap k)^[n] z) := by
  rw [ae_all_iff]
  intro n
  exact (((measurePreserving_spectralGapRegion k hk χ).iterate n).quasiMeasurePreserving.ae
    (ae_regularChartPoint k hk hχ)).and
    (((measurePreserving_inverse_spectralGapRegion k hk χ).iterate n).quasiMeasurePreserving.ae
    (ae_regularChartPoint k hk hχ))

lemma slow_radius_ratio {a b ε : ℝ} (_ha : 0<a) (hb : 0<b)
    (hab : Real.exp (-ε)*a≤b) : a/b≤Real.exp ε := by
  apply (div_le_iff₀ hb).mpr
  have hh := mul_le_mul_of_nonneg_left hab (Real.exp_pos ε).le
  have he : Real.exp ε*Real.exp (-ε)=1 := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]
  simpa only [←mul_assoc,he,one_mul] using hh

lemma chartSize_ratio (k : ℝ) {χ : ℝ} (hχ : 0<χ) (z w : Torus) :
    chartSize k χ z/chartSize k χ w=chartRadius k χ (χ/2) z/chartRadius k χ (χ/2) w := by
  unfold chartSize
  rw [mul_div_mul_left _ _ (ne_of_gt (hyperbolicChartScale_pos k hχ))]

lemma actualStableMultiplier_bound (k : ℝ) {χ : ℝ} (hχ : 0<χ) (z : Torus)
    (hz : RegularChartPoint k χ z) : |actualStableMultiplier k χ z|≤hyperbolicChartRate χ := by
  have hr := slow_radius_ratio (chartRadius_pos k χ (χ/2) z)
    (chartRadius_pos k χ (χ/2) (standardMap k z)) hz.2.2.2.2.2.1
  have he : Real.exp (χ/2)*Real.exp (-χ)=hyperbolicChartRate χ := by
    rw [←Real.exp_add]
    congr 1
    ring
  unfold actualStableMultiplier
  rw [abs_mul,abs_of_pos (div_pos (chartSize_pos k hχ z) (chartSize_pos k hχ _)),chartSize_ratio k hχ]
  exact (mul_le_mul hr hz.2.2.1 (abs_nonneg _) (Real.exp_pos _).le).trans_eq he

lemma actualUnstableMultiplier_ne (k : ℝ) {χ : ℝ} (hχ : 0<χ) (z : Torus)
    (hz : RegularChartPoint k χ z) : actualUnstableMultiplier k χ z≠0 := by
  have hb : unstableMultiplier k χ z≠0 := abs_pos.mp ((Real.exp_pos χ).trans_le hz.2.2.2.1)
  exact mul_ne_zero (div_ne_zero (ne_of_gt (chartSize_pos k hχ z)) (ne_of_gt (chartSize_pos k hχ _))) hb

lemma actualUnstableMultiplier_inverse_bound (k : ℝ) {χ : ℝ} (hχ : 0<χ) (z : Torus)
    (hz : RegularChartPoint k χ z) : |(actualUnstableMultiplier k χ z)⁻¹|≤hyperbolicChartRate χ := by
  have hr := slow_radius_ratio (chartRadius_pos k χ (χ/2) (standardMap k z))
    (chartRadius_pos k χ (χ/2) z) hz.2.2.2.2.2.2
  have hb : |unstableMultiplier k χ z|⁻¹≤Real.exp (-χ) := by
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos χ) hz.2.2.2.1
  have he : Real.exp (χ/2)*Real.exp (-χ)=hyperbolicChartRate χ := by
    rw [←Real.exp_add]
    congr 1
    ring
  unfold actualUnstableMultiplier
  rw [abs_inv,abs_mul,abs_of_pos (div_pos (chartSize_pos k hχ z) (chartSize_pos k hχ _)),
    mul_inv,inv_div,chartSize_ratio k hχ]
  exact (mul_le_mul hr hb (inv_nonneg.mpr (abs_nonneg _)) (Real.exp_pos _).le).trans_eq he

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

lemma chart_nonlinearity_coefficient (k : ℝ) {χ : ℝ} (hχ : 0<χ) (z : Torus)
    (hz : RegularChartPoint k χ z) (hn : RegularChartPoint k χ (standardMap k z)) :
    ‖actualChartInverse k χ (standardMap k z)‖*derivativeVariationBound k*
      ‖actualChartFrame k χ z‖^2≤hyperbolicChartError χ := by
  let a := chartRadius k χ (χ/2) z
  let b := chartRadius k χ (χ/2) (standardMap k z)
  let c := ‖lyapunovCoframe k χ (standardMap k z)‖
  let η := hyperbolicChartScale k χ
  have ha : 0<a := chartRadius_pos k χ (χ/2) z
  have hb : 0<b := chartRadius_pos k χ (χ/2) (standardMap k z)
  have hη : 0<η := hyperbolicChartScale_pos k hχ
  have hc : 0≤c := norm_nonneg _
  have hbc : b*c≤1 := hn.2.2.2.2.1
  have hab : a/b≤Real.exp (χ/2) := slow_radius_ratio ha hb hz.2.2.2.2.2.1
  have hD := derivativeVariationBound_nonneg k
  have hF : ‖actualChartFrame k χ z‖≤2*(η*a) := actualChartFrame_norm_le k hχ z
  have hC : ‖actualChartInverse k χ (standardMap k z)‖≤(η*b)⁻¹*c :=
    flatInverse_norm_le (chartSize_pos k hχ _).le _
  have hEF : (Real.exp (χ/2))^2=Real.exp χ := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  have hsqr : (a/b)^2≤Real.exp χ := by
    rw [←hEF]
    exact pow_le_pow_left₀ (div_nonneg ha.le hb.le) hab 2
  calc
    _ ≤ ((η*b)⁻¹*c)*derivativeVariationBound k*(2*(η*a))^2 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hC hD)
        (pow_le_pow_left₀ (norm_nonneg _) hF 2) (sq_nonneg _)
        (mul_nonneg (mul_nonneg (inv_nonneg.mpr (mul_nonneg hη.le hb.le)) hc) hD)
    _ = (4*derivativeVariationBound k*η)*((b*c)*(a/b)^2) := by
      field_simp [ne_of_gt hη,ne_of_gt hb]
      ring
    _ ≤ (4*derivativeVariationBound k*η)*(1*Real.exp χ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hbc hsqr (sq_nonneg _) (by norm_num)) (by positivity)
    _ = hyperbolicChartError χ*(derivativeVariationBound k/(2*(1+derivativeVariationBound k))) := by
      dsimp [η,hyperbolicChartScale]
      field_simp [ne_of_gt (Real.exp_pos χ),ne_of_gt (show 0<1+derivativeVariationBound k by linarith)]
      ring
    _ ≤ hyperbolicChartError χ*1 := by
      apply mul_le_mul_of_nonneg_left _ (hyperbolicChartError_pos hχ).le
      apply (div_le_iff₀ (show 0<2*(1+derivativeVariationBound k) by linarith)).mpr
      linarith
    _ = _ := mul_one _

noncomputable def actualChartRemainder (k χ : ℝ) (z : ℂ) : RealPlane → RealPlane :=
  flatRemainder k z (actualChartFrame k χ (complexProjection z))
    (actualChartInverse k χ (standardMap k (complexProjection z)))
@[simp] lemma actualChartRemainder_zero (k χ : ℝ) (z : ℂ) : actualChartRemainder k χ z 0=0 :=
  flatRemainder_zero _ _ _ _
lemma actualChartRemainder_lipschitz (k : ℝ) {χ : ℝ} (hχ : 0<χ) (z : ℂ)
    (hz : RegularChartPoint k χ (complexProjection z))
    (hn : RegularChartPoint k χ (standardMap k (complexProjection z)))
    {v w : RealPlane} (hv : ‖v‖≤1) (hw : ‖w‖≤1) :
    ‖actualChartRemainder k χ z v-actualChartRemainder k χ z w‖≤hyperbolicChartError χ*‖v-w‖ :=
  (flatRemainder_sub_bound k z _ _ hv hw).trans
    (mul_le_mul_of_nonneg_right (chart_nonlinearity_coefficient k hχ _ hz hn) (norm_nonneg _))

lemma actualChart_derivative_diagonal (k χ : ℝ) (z : Torus) (hz : RegularChartPoint k χ z) (v : RealPlane) :
    actualChartInverse k χ (standardMap k z) (standardDerivative k z (actualChartFrame k χ z v)) =
      (actualStableMultiplier k χ z*v.1,actualUnstableMultiplier k χ z*v.2) :=
  flat_diagonal _ _ _ hz.2.1 v

lemma actualChart_step (k χ : ℝ) (z : ℂ) (hz : RegularChartPoint k χ (complexProjection z)) (v : RealPlane) :
    actualChartInverse k χ (standardMap k (complexProjection z))
      (standardLift k (z+actualChartFrame k χ (complexProjection z) v)-standardLift k z) =
      (actualStableMultiplier k χ (complexProjection z)*v.1+(actualChartRemainder k χ z v).1,
        actualUnstableMultiplier k χ (complexProjection z)*v.2+(actualChartRemainder k χ z v).2) := by
  have hdiff : standardLift k (z+actualChartFrame k χ (complexProjection z) v)-standardLift k z =
      standardDerivative k (complexProjection z) (actualChartFrame k χ (complexProjection z) v)+
        liftRemainder k z (actualChartFrame k χ (complexProjection z) v) := by
    unfold liftRemainder
    abel
  rw [hdiff,map_add,actualChart_derivative_diagonal k χ _ hz]
  rfl

lemma actualChart_lift_step (k : ℝ) {χ : ℝ} (hχ : 0<χ) (z : ℂ)
    (hz : RegularChartPoint k χ (complexProjection z))
    (hn : RegularChartPoint k χ (standardMap k (complexProjection z))) (v : RealPlane) :
    standardLift k (z+actualChartFrame k χ (complexProjection z) v) = standardLift k z+
      actualChartFrame k χ (standardMap k (complexProjection z))
        (actualStableMultiplier k χ (complexProjection z)*v.1+(actualChartRemainder k χ z v).1,
          actualUnstableMultiplier k χ (complexProjection z)*v.2+(actualChartRemainder k χ z v).2) := by
  have hh := congrArg (actualChartFrame k χ (standardMap k (complexProjection z))) (actualChart_step k χ z hz v)
  rw [actualChartFrame_inverse k hχ _ hn.1] at hh
  exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

noncomputable def chartLinearRate (χ : ℝ) : ℝ≥0 := ⟨hyperbolicChartRate χ,(hyperbolicChartRate_pos χ).le⟩
noncomputable def chartErrorRate (χ : ℝ) (hχ : 0<χ) : ℝ≥0 := ⟨hyperbolicChartError χ,(hyperbolicChartError_pos hχ).le⟩
lemma chart_rates_contract {χ : ℝ} (hχ : 0<χ) : chartLinearRate χ+chartErrorRate χ hχ<1 := by
  change hyperbolicChartRate χ+hyperbolicChartError χ<1
  unfold hyperbolicChartError
  linarith [hyperbolicChartRate_lt_one hχ]

lemma regular_lift_next (k χ : ℝ) (w : ℂ)
    (hw : ∀ n : ℕ, RegularChartPoint k χ (complexProjection ((standardLift k)^[n] w))) (n : ℕ) :
    RegularChartPoint k χ (standardMap k (complexProjection ((standardLift k)^[n] w))) := by
  simpa only [Function.iterate_succ_apply',complexProjection_standardLift] using hw (n+1)

noncomputable def actualLocalRecurrence (k : ℝ) (χ : ℝ) (hχ : 0<χ) (w : ℂ)
    (hw : ∀ n : ℕ, RegularChartPoint k χ (complexProjection ((standardLift k)^[n] w))) :
    LocalRecurrence (chartLinearRate χ) (chartErrorRate χ hχ) where
  a n := actualStableMultiplier k χ (complexProjection ((standardLift k)^[n] w))
  b n := actualUnstableMultiplier k χ (complexProjection ((standardLift k)^[n] w))
  remainder n := actualChartRemainder k χ ((standardLift k)^[n] w)
  stable_bound n := actualStableMultiplier_bound k hχ _ (hw n)
  inverse_bound n := actualUnstableMultiplier_inverse_bound k hχ _ (hw n)
  b_ne n := actualUnstableMultiplier_ne k hχ _ (hw n)
  local_lipschitz n _ _ hv hu := actualChartRemainder_lipschitz k hχ _ (hw n) (regular_lift_next k χ w hw n) hv hu
  zero _ := actualChartRemainder_zero _ _ _

lemma actualLocalRecurrence_lift_step (k : ℝ) (χ : ℝ) (hχ : 0<χ) (w : ℂ)
    (hw : ∀ n : ℕ, RegularChartPoint k χ (complexProjection ((standardLift k)^[n] w)))
    (n : ℕ) (v : RealPlane) :
    standardLift k ((standardLift k)^[n] w+actualChartFrame k χ (complexProjection ((standardLift k)^[n] w)) v) =
      (standardLift k)^[n+1] w+actualChartFrame k χ (complexProjection ((standardLift k)^[n+1] w))
        ((actualLocalRecurrence k χ hχ w hw).step n v) := by
  simpa only [Function.iterate_succ_apply',complexProjection_standardLift,actualLocalRecurrence,LocalRecurrence.step] using
    actualChart_lift_step k hχ ((standardLift k)^[n] w) (hw n) (regular_lift_next k χ w hw n) v

lemma actual_local_orbit_lift (k : ℝ) (χ : ℝ) (hχ : 0<χ) (w : ℂ)
    (hw : ∀ n : ℕ, RegularChartPoint k χ (complexProjection ((standardLift k)^[n] w)))
    (x : ℕ → RealPlane) (hx : ∀ n, x (n+1)=(actualLocalRecurrence k χ hχ w hw).step n (x n)) (n : ℕ) :
    (standardLift k)^[n] (w+actualChartFrame k χ (complexProjection w) (x 0)) =
      (standardLift k)^[n] w+actualChartFrame k χ (complexProjection ((standardLift k)^[n] w)) (x n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,actualLocalRecurrence_lift_step k χ hχ w hw n,←hx n]

theorem actual_stable_curve_of_regular (k : ℝ) (χ : ℝ) (hχ : 0<χ) (w : ℂ)
    (hw : ∀ n : ℕ, RegularChartPoint k χ (complexProjection ((standardLift k)^[n] w))) :
    ∃ γ : ℝ → ℂ, γ 0=w ∧ Continuous γ ∧ Function.Injective γ ∧
      ∀ s t : ℝ, |s|≤1 → |t|≤1 → ∀ n : ℕ,
        ‖(standardLift k)^[n] (γ s)-(standardLift k)^[n] (γ t)‖≤
          (2*hyperbolicChartScale k χ)*
            (hyperbolicChartRate χ+hyperbolicChartError χ)^n*|s-t| := by
  let r := actualLocalRecurrence k χ hχ w hw
  let h := chart_rates_contract hχ
  let g := r.extend.graph h
  let γ : ℝ → ℂ := fun s => w+actualChartFrame k χ (complexProjection w) (s,g s)
  have g0 : g 0=0 := graph_zero r.extend h
  have gc : Continuous g := (graph_lipschitz r.extend h).continuous
  have hinit (s : ℝ) : r.extend.solution h s 0=(s,g s) := Prod.ext (solution_initial _ h s) rfl
  have horbit (s : ℝ) (hs : |s|≤1) (n : ℕ) :
      (standardLift k)^[n] (γ s)=(standardLift k)^[n] w+
        actualChartFrame k χ (complexProjection ((standardLift k)^[n] w)) (r.extend.solution h s n) := by
    have hh := actual_local_orbit_lift k χ hχ w hw (r.extend.solution h s) (local_solution_orbit r h hs) n
    simpa only [hinit,γ] using hh
  refine ⟨γ,?_,?_,?_,?_⟩
  · simp only [γ,g0,Prod.mk_zero_zero,map_zero,add_zero]
  · exact continuous_const.add ((actualChartFrame k χ (complexProjection w)).continuous.comp (continuous_id.prodMk gc))
  · intro s t he
    have he' : actualChartFrame k χ (complexProjection w) (s,g s)=
        actualChartFrame k χ (complexProjection w) (t,g t) := add_left_cancel he
    have hp := congrArg (actualChartInverse k χ (complexProjection w)) he'
    have hw0 : RegularChartPoint k χ (complexProjection w) := by simpa only [Function.iterate_zero, id_eq] using hw 0
    rw [actualChartInverse_frame k hχ _ hw0.1,actualChartInverse_frame k hχ _ hw0.1] at hp
    exact congrArg Prod.fst hp
  · intro s t hs ht n
    rw [horbit s hs n,horbit t ht n,add_sub_add_left_eq_sub,←map_sub]
    have hn : ‖actualChartFrame k χ (complexProjection ((standardLift k)^[n] w))‖≤2*hyperbolicChartScale k χ :=
      (actualChartFrame_norm_le k hχ _).trans (mul_le_mul_of_nonneg_left (chartSize_le_scale k hχ _) (by norm_num))
    have hx := solution_exponential_contraction r.extend h s t n
    calc
      _ ≤ ‖actualChartFrame k χ (complexProjection ((standardLift k)^[n] w))‖*
          ‖r.extend.solution h s n-r.extend.solution h t n‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (2*hyperbolicChartScale k χ)*
          (((chartLinearRate χ+chartErrorRate χ hχ : ℝ≥0) : ℝ)^n*|s-t|) :=
        mul_le_mul hn hx (norm_nonneg _) (by linarith [hyperbolicChartScale_pos k hχ])
      _ = _ := by
        change (2*hyperbolicChartScale k χ)*((hyperbolicChartRate χ+hyperbolicChartError χ)^n*|s-t|)=_
        ring

theorem ae_actual_stable_curve (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0<χ) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ), ∀ w : ℂ, complexProjection w=z →
      ∃ γ : ℝ → ℂ, γ 0=w ∧ Continuous γ ∧ Function.Injective γ ∧
        ∀ s t : ℝ, |s|≤1 → |t|≤1 → ∀ n : ℕ,
          ‖(standardLift k)^[n] (γ s)-(standardLift k)^[n] (γ t)‖≤
            (2*hyperbolicChartScale k χ)*
              (hyperbolicChartRate χ+hyperbolicChartError χ)^n*|s-t| := by
  filter_upwards [ae_regularChartPoint_all_iterates k hk hχ] with z hz
  intro w hw
  apply actual_stable_curve_of_regular k χ hχ w
  intro n
  simpa only [complexProjection_iterate,hw] using (hz n).1

end StandardMapEntropy

end
section
namespace StandardMapEntropy.NonlinearStable
open Filter
open scoped Topology NNReal
variable {ℓ δ : ℝ≥0}

noncomputable def sndSequence (x : Sequence) : BoundedContinuousFunction ℕ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun n => (x n).2) ‖x‖
    (fun n => (norm_snd_le (x n)).trans (x.norm_coe_le_norm n))
@[simp] lemma sndSequence_apply (x : Sequence) (n : ℕ) : sndSequence x n=(x n).2 := rfl

lemma linearRate_lt_one (h : ℓ+δ<1) : (ℓ : ℝ)<1 := by
  have he : ℓ≤ℓ+δ := le_add_of_nonneg_right (show (0 : ℝ≥0)≤δ from bot_le)
  exact lt_of_le_of_lt he h

lemma solution_snd_bound_of_forcing (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s t : ℝ)
    {B : ℝ} (hB : 0≤B)
    (hr : ∀ n, ‖r.remainder n (r.solution h s n)-r.remainder n (r.solution h t n)‖≤B) :
    ‖sndSequence (r.solution h s)-sndSequence (r.solution h t)‖≤(ℓ : ℝ)*B/(1-(ℓ : ℝ)) := by
  let U := ‖sndSequence (r.solution h s)-sndSequence (r.solution h t)‖
  have hU : 0≤U := norm_nonneg _
  have hcon : U≤(ℓ : ℝ)*(U+B) := by
    apply (BoundedContinuousFunction.norm_le (mul_nonneg ℓ.coe_nonneg (add_nonneg hU hB))).mpr
    intro n
    have hs := congrArg (fun x : Sequence => (x n).2) (solution_fixed r h s)
    have ht := congrArg (fun x : Sequence => (x n).2) (solution_fixed r h t)
    change (r.b n)⁻¹*((r.solution h s (n+1)).2-(r.remainder n (r.solution h s n)).2)=
      (r.solution h s n).2 at hs
    change (r.b n)⁻¹*((r.solution h t (n+1)).2-(r.remainder n (r.solution h t n)).2)=
      (r.solution h t n).2 at ht
    change |(r.solution h s n).2-(r.solution h t n).2|≤_
    rw [←hs,←ht]
    have hu : |(r.solution h s (n+1)).2-(r.solution h t (n+1)).2|≤U :=
      (sndSequence (r.solution h s)-sndSequence (r.solution h t)).norm_coe_le_norm (n+1)
    have hb : |(r.remainder n (r.solution h s n)).2-(r.remainder n (r.solution h t n)).2|≤B :=
      (norm_snd_le _).trans (hr n)
    calc
      _ = |(r.b n)⁻¹| * |((r.solution h s (n+1)).2-(r.solution h t (n+1)).2)-
          ((r.remainder n (r.solution h s n)).2-(r.remainder n (r.solution h t n)).2)| := by
        rw [←abs_mul]; congr 1; ring
      _ ≤ |(r.b n)⁻¹| * (|(r.solution h s (n+1)).2-(r.solution h t (n+1)).2|+
          |(r.remainder n (r.solution h s n)).2-(r.remainder n (r.solution h t n)).2|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
      _ ≤ _ := mul_le_mul (r.inverse_bound n) (add_le_add hu hb) (by positivity) ℓ.coe_nonneg
  apply (le_div_iff₀ (sub_pos.mpr (linearRate_lt_one h))).mpr
  dsimp [U] at hcon ⊢
  nlinarith

lemma graph_slope_bound (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s t : ℝ) :
    |r.graph h s-r.graph h t|≤((ℓ : ℝ)*(δ : ℝ)/(1-(ℓ : ℝ)))*|s-t| := by
  have hforce (n : ℕ) : ‖r.remainder n (r.solution h s n)-r.remainder n (r.solution h t n)‖≤
      (δ : ℝ)*|s-t| :=
    (remainder_sub_bound r _ _ n).trans (mul_le_mul_of_nonneg_left (solution_lipschitz r h s t) δ.coe_nonneg)
  have hh := solution_snd_bound_of_forcing r h s t (mul_nonneg δ.coe_nonneg (abs_nonneg _)) hforce
  have hb := (sndSequence (r.solution h s)-sndSequence (r.solution h t)).norm_coe_le_norm 0
  apply hb.trans
  exact hh.trans_eq (by ring)

lemma graph_bound_of_forcing (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ)
    {B : ℝ} (hB : 0≤B) (hr : ∀ n, ‖r.remainder n (r.solution h s n)‖≤B) :
    |r.graph h s|≤(ℓ : ℝ)*B/(1-(ℓ : ℝ)) := by
  have hr' (n : ℕ) : ‖r.remainder n (r.solution h s n)-r.remainder n (r.solution h 0 n)‖≤B := by
    simpa [solution_zero,r.zero] using hr n
  have hh := solution_snd_bound_of_forcing r h s 0 hB hr'
  have hb := (sndSequence (r.solution h s)-sndSequence (r.solution h 0)).norm_coe_le_norm 0
  have hle := hb.trans hh
  simpa [Recurrence.graph,solution_zero,sndSequence_apply] using hle

lemma local_graph_quadratic_bound (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    {B : ℝ} (hB : 0≤B)
    (hr : ∀ n (v : Plane), ‖v‖≤1 → ‖r.remainder n v‖≤B*‖v‖^2)
    {s : ℝ} (hs : |s|≤1) :
    |r.extend.graph h s|≤((ℓ : ℝ)*B/(1-(ℓ : ℝ)))*|s|^2 := by
  have hforce (n : ℕ) : ‖r.extend.remainder n (r.extend.solution h s n)‖≤B*|s|^2 := by
    change ‖r.remainder n (planeClip (r.extend.solution h s n))‖≤_
    rw [planeClip_eq (local_solution_bound r h hs n)]
    apply (hr n _ (local_solution_bound r h hs n)).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (((r.extend.solution h s).norm_coe_le_norm n).trans (solution_norm_bound _ h s)) 2) hB
  exact (graph_bound_of_forcing _ h s (mul_nonneg hB (sq_nonneg _)) hforce).trans_eq (by ring)

end StandardMapEntropy.NonlinearStable

end
end

end OAI
