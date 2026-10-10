import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Entropy.SupportEntropy

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

noncomputable def fineScale (k ε δ : ℝ) : ℝ := δ/(8*(1+derivativeVariationBound k)*Real.exp (2*ε))
noncomputable def fineSize (k χ ε δ : ℝ) (z : Torus) : ℝ := fineScale k ε δ*chartRadius k χ ε z
noncomputable def fineFrame (k χ ε δ : ℝ) (z : Torus) : RealPlane →L[ℝ] ℂ :=
  flatFrame (fineSize k χ ε δ z) (lyapunovFrame k χ z)
noncomputable def fineInverse (k χ ε δ : ℝ) (z : Torus) : ℂ →L[ℝ] RealPlane :=
  flatInverse (fineSize k χ ε δ z) (lyapunovCoframe k χ z)
noncomputable def fineStableMultiplier (k χ ε δ : ℝ) (z : Torus) : ℝ :=
  fineSize k χ ε δ z/fineSize k χ ε δ (standardMap k z)*stableMultiplier k χ z
noncomputable def fineUnstableMultiplier (k χ ε δ : ℝ) (z : Torus) : ℝ :=
  fineSize k χ ε δ z/fineSize k χ ε δ (standardMap k z)*unstableMultiplier k χ z
lemma fineScale_pos (k ε : ℝ) {δ : ℝ} (hδ : 0<δ) : 0<fineScale k ε δ := by
  unfold fineScale
  exact div_pos hδ (mul_pos (mul_pos (by norm_num) (by linarith [derivativeVariationBound_nonneg k])) (Real.exp_pos _))
lemma fineSize_pos (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus) : 0<fineSize k χ ε δ z :=
  mul_pos (fineScale_pos k ε hδ) (chartRadius_pos k χ ε z)
lemma fineSize_le_scale (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus) : fineSize k χ ε δ z≤fineScale k ε δ :=
  (mul_le_mul_of_nonneg_left (chartRadius_le_one k χ ε z) (fineScale_pos k ε hδ).le).trans_eq (mul_one _)
lemma fineFrame_norm_le (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus) :
    ‖fineFrame k χ ε δ z‖≤2*fineSize k χ ε δ z :=
  flatFrame_norm_le (fineSize_pos k χ ε hδ z).le (lyapunovFrame_norm_le k χ z)
lemma fineInverse_frame (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus)
    (hw : wedge (stableVector k z) (unstableVector k z)≠0) (v : RealPlane) :
    fineInverse k χ ε δ z (fineFrame k χ ε δ z v)=v :=
  flatInverse_frame (ne_of_gt (fineSize_pos k χ ε hδ z)) (lyapunovCoframe_frame k χ z hw) v
lemma fineFrame_inverse (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus)
    (hw : wedge (stableVector k z) (unstableVector k z)≠0) (v : ℂ) :
    fineFrame k χ ε δ z (fineInverse k χ ε δ z v)=v :=
  flatFrame_inverse (ne_of_gt (fineSize_pos k χ ε hδ z)) (lyapunovFrame_coframe k χ z hw) v

def FineRegular (k χ ε : ℝ) (z : Torus) : Prop :=
  wedge (stableVector k z) (unstableVector k z)≠0 ∧
  (lyapunovCoframe k χ (standardMap k z)).comp ((standardDerivative k z).comp (lyapunovFrame k χ z)) =
    diagonalPlane (stableMultiplier k χ z) (unstableMultiplier k χ z) ∧
  |stableMultiplier k χ z|≤Real.exp (-χ) ∧ Real.exp χ≤|unstableMultiplier k χ z| ∧
  chartRadius k χ ε z*‖lyapunovCoframe k χ z‖≤1 ∧
  Real.exp (-ε)*chartRadius k χ ε z≤chartRadius k χ ε (standardMap k z) ∧
  Real.exp (-ε)*chartRadius k χ ε (standardMap k z)≤chartRadius k χ ε z
lemma ae_fineRegular (k : ℝ) (hk : 0≤k) {χ ε : ℝ} (hχ : 0<χ) (hε : 0<ε) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ), FineRegular k χ ε z := by
  filter_upwards [ae_restrict_mem (measurableSet_spectralGapRegion k hk χ),
    (ae_transverseLines k hk).filter_mono Measure.absolutelyContinuous_restrict.ae_le,
    ae_lyapunov_normal_form k hk χ hχ.le,ae_stableMultiplier_bound k hk χ hχ.le,
    ae_unstableMultiplier_bound k hk χ hχ.le,ae_chartRadius_control k hk χ hχ.le ε hε]
    with z hz ht hn hs hu hr
  exact ⟨ht (hχ.trans hz),hn,hs,hu,hr⟩
lemma ae_fineRegular_all_iterates (k : ℝ) (hk : 0≤k) {χ ε : ℝ} (hχ : 0<χ) (hε : 0<ε) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      ∀ n : ℕ, FineRegular k χ ε ((standardMap k)^[n] z) ∧ FineRegular k χ ε ((inverseMap k)^[n] z) := by
  rw [ae_all_iff]
  intro n
  exact (((measurePreserving_spectralGapRegion k hk χ).iterate n).quasiMeasurePreserving.ae
    (ae_fineRegular k hk hχ hε)).and
    (((measurePreserving_inverse_spectralGapRegion k hk χ).iterate n).quasiMeasurePreserving.ae
    (ae_fineRegular k hk hχ hε))
lemma fineSize_ratio (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z w : Torus) :
    fineSize k χ ε δ z/fineSize k χ ε δ w=chartRadius k χ ε z/chartRadius k χ ε w := by
  unfold fineSize
  rw [mul_div_mul_left _ _ (ne_of_gt (fineScale_pos k ε hδ))]
lemma fineStableMultiplier_bound (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus)
    (hz : FineRegular k χ ε z) : |fineStableMultiplier k χ ε δ z|≤Real.exp (-χ+ε) := by
  have hr := slow_radius_ratio (chartRadius_pos k χ ε z) (chartRadius_pos k χ ε (standardMap k z)) hz.2.2.2.2.2.1
  have he : Real.exp ε*Real.exp (-χ)=Real.exp (-χ+ε) := by rw [←Real.exp_add,add_comm]
  unfold fineStableMultiplier
  rw [abs_mul,abs_of_pos (div_pos (fineSize_pos k χ ε hδ z) (fineSize_pos k χ ε hδ _)),fineSize_ratio k χ ε hδ]
  exact (mul_le_mul hr hz.2.2.1 (abs_nonneg _) (Real.exp_pos _).le).trans_eq he
lemma fineUnstableMultiplier_ne (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus)
    (hz : FineRegular k χ ε z) : fineUnstableMultiplier k χ ε δ z≠0 := by
  have hb : unstableMultiplier k χ z≠0 := abs_pos.mp ((Real.exp_pos χ).trans_le hz.2.2.2.1)
  exact mul_ne_zero (div_ne_zero (ne_of_gt (fineSize_pos k χ ε hδ z)) (ne_of_gt (fineSize_pos k χ ε hδ _))) hb
lemma fineUnstableMultiplier_inverse_bound (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus)
    (hz : FineRegular k χ ε z) : |(fineUnstableMultiplier k χ ε δ z)⁻¹|≤Real.exp (-χ+ε) := by
  have hr := slow_radius_ratio (chartRadius_pos k χ ε (standardMap k z)) (chartRadius_pos k χ ε z) hz.2.2.2.2.2.2
  have hb : |unstableMultiplier k χ z|⁻¹≤Real.exp (-χ) := by
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos χ) hz.2.2.2.1
  have he : Real.exp ε*Real.exp (-χ)=Real.exp (-χ+ε) := by rw [←Real.exp_add,add_comm]
  unfold fineUnstableMultiplier
  rw [abs_inv,abs_mul,abs_of_pos (div_pos (fineSize_pos k χ ε hδ z) (fineSize_pos k χ ε hδ _)),
    mul_inv,inv_div,fineSize_ratio k χ ε hδ]
  exact (mul_le_mul hr hb (inv_nonneg.mpr (abs_nonneg _)) (Real.exp_pos _).le).trans_eq he

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable def codingScale (k ε δ : ℝ) : ℝ := min 1 (fineScale k ε δ)/(100*(1+|9*growthBase k|))
noncomputable def codingRadius (k χ ε δ : ℝ) (z : Torus) : ℝ :=
  codingScale k ε δ*(chartRadius k χ ε z)^2
lemma codingScale_pos (k ε : ℝ) {δ : ℝ} (hδ : 0<δ) : 0<codingScale k ε δ := by
  unfold codingScale
  exact div_pos (lt_min zero_lt_one (fineScale_pos k ε hδ)) (by positivity)
lemma codingScale_le (k ε : ℝ) {δ : ℝ} (hδ : 0<δ) :
    codingScale k ε δ≤fineScale k ε δ/100 := by
  have hη := fineScale_pos k ε hδ
  unfold codingScale
  calc
    _ ≤ fineScale k ε δ/(100*(1+|9*growthBase k|)) := div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left hη.le (by norm_num) (by nlinarith [abs_nonneg (9*growthBase k)])
lemma codingScale_global (k ε δ : ℝ) :
    codingScale k ε δ*(1+|9*growthBase k|)≤1/100 := by
  unfold codingScale
  have hd : 0<(1+|9*growthBase k|) := by positivity
  have he : min 1 (fineScale k ε δ)/(100*(1+|9*growthBase k|))*(1+|9*growthBase k|)=min 1 (fineScale k ε δ)/100 := by
    field_simp
  rw [he]
  exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
lemma codingRadius_pos (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus) : 0<codingRadius k χ ε δ z :=
  mul_pos (codingScale_pos k ε hδ) (sq_pos_of_pos (chartRadius_pos k χ ε z))
lemma codingRadius_small (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus) :
    (1+|9*growthBase k|)*codingRadius k χ ε δ z≤1/100 := by
  have hr : (chartRadius k χ ε z)^2≤1 := by
    have h0 := (chartRadius_pos k χ ε z).le
    have h1 := chartRadius_le_one k χ ε z
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hr (codingScale_pos k ε hδ).le
  have hg := mul_le_mul_of_nonneg_left hh (by positivity : 0≤1+|9*growthBase k|)
  dsimp only [codingRadius]
  exact hg.trans (by simpa only [mul_one,one_mul,mul_comm] using codingScale_global k ε δ)
lemma codingRadius_le_one (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus) : codingRadius k χ ε δ z≤1 := by
  have hh := codingRadius_small k χ ε hδ z
  have hp := codingRadius_pos k χ ε hδ z
  nlinarith [abs_nonneg (9*growthBase k)]
lemma measurable_codingRadius (k χ ε δ : ℝ) : Measurable (codingRadius k χ ε δ) :=
  measurable_const.mul ((measurable_chartRadius k χ ε).pow_const 2)
noncomputable def codingLevel (k χ ε : ℝ) (δ : ℝ) (hδ : 0<δ) (z : Torus) : ℕ :=
  dyadicLevel (codingRadius k χ ε δ z) (codingRadius_pos k χ ε hδ z)
lemma measurable_codingLevel (k χ ε δ : ℝ) (hδ : 0<δ) : Measurable (codingLevel k χ ε δ hδ) :=
  measurable_dyadicLevel _ (codingRadius_pos k χ ε hδ) (measurable_codingRadius k χ ε δ)
lemma codingLevel_size (k χ ε δ : ℝ) (hδ : 0<δ) (z : Torus) :
    1/(2 : ℝ)^(codingLevel k χ ε δ hδ z)≤codingRadius k χ ε δ z :=
  inv_dyadicLevel_le _ _
lemma codingRadius_ratio (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus) (hz : FineRegular k χ ε z) :
    codingRadius k χ ε δ z≤Real.exp (2*ε)*codingRadius k χ ε δ (standardMap k z) ∧
    codingRadius k χ ε δ (standardMap k z)≤Real.exp (2*ε)*codingRadius k χ ε δ z := by
  have he : 0<Real.exp ε := Real.exp_pos ε
  have hex : (Real.exp ε)^2=Real.exp (2*ε) := by rw [sq,←Real.exp_add]; congr 1; ring
  have hh : chartRadius k χ ε z≤Real.exp ε*chartRadius k χ ε (standardMap k z) := by
    have ht := mul_le_mul_of_nonneg_left hz.2.2.2.2.2.1 he.le
    rw [←mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul] at ht
    exact ht
  have hh' : chartRadius k χ ε (standardMap k z)≤Real.exp ε*chartRadius k χ ε z := by
    have ht := mul_le_mul_of_nonneg_left hz.2.2.2.2.2.2 he.le
    rw [←mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul] at ht
    exact ht
  have general (x y : Torus) (h : chartRadius k χ ε x≤Real.exp ε*chartRadius k χ ε y) :
      codingRadius k χ ε δ x≤Real.exp (2*ε)*codingRadius k χ ε δ y := by
    have hs := sq_le_sq₀ (chartRadius_pos k χ ε x).le (mul_nonneg he.le (chartRadius_pos k χ ε y).le) |>.mpr h
    rw [mul_pow,hex] at hs
    have ht := mul_le_mul_of_nonneg_left hs (codingScale_pos k ε hδ).le
    simpa only [codingRadius,mul_left_comm] using ht
  exact ⟨general _ _ hh,general _ _ hh'⟩
lemma codingLevel_step (k χ ε δ : ℝ) (hδ : 0<δ) (z : Torus) (hz : FineRegular k χ ε z)
    (J : ℕ) (hJ : Real.exp (2*ε)≤(2 : ℝ)^J) :
    codingLevel k χ ε δ hδ (standardMap k z)≤codingLevel k χ ε δ hδ z+J ∧
    codingLevel k χ ε δ hδ z≤codingLevel k χ ε δ hδ (standardMap k z)+J := by
  have hr := codingRadius_ratio k χ ε hδ z hz
  exact ⟨dyadicLevel_mono_bound _ _ J (hr.1.trans (mul_le_mul_of_nonneg_right hJ (codingRadius_pos k χ ε hδ _).le)),
    dyadicLevel_mono_bound _ _ J (hr.2.trans (mul_le_mul_of_nonneg_right hJ (codingRadius_pos k χ ε hδ _).le))⟩
lemma fineInverse_codingRadius (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus) (hz : FineRegular k χ ε z) :
    ‖fineInverse k χ ε δ z‖*codingRadius k χ ε δ z≤1/100 := by
  let r := chartRadius k χ ε z
  let η := fineScale k ε δ
  let c := codingScale k ε δ
  have hr : 0<r := chartRadius_pos k χ ε z
  have hη : 0<η := fineScale_pos k ε hδ
  have hc : 0<c := codingScale_pos k ε hδ
  have hb : ‖fineInverse k χ ε δ z‖≤(η*r)⁻¹*‖lyapunovCoframe k χ z‖ :=
    flatInverse_norm_le (fineSize_pos k χ ε hδ z).le _
  calc
    _ ≤ ((η*r)⁻¹*‖lyapunovCoframe k χ z‖)*(c*r^2) := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (c/η)*(r*‖lyapunovCoframe k χ z‖) := by field_simp
    _ ≤ (c/η)*1 := mul_le_mul_of_nonneg_left hz.2.2.2.2.1 (by positivity)
    _ ≤ 1/100 := by
      rw [mul_one]
      exact (div_le_iff₀ hη).mpr (by simpa only [div_eq_mul_inv,mul_comm,one_mul,c,η] using codingScale_le k ε hδ)

end StandardMapEntropy

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma Recurrence.linearRate_pos (r : Recurrence ℓ δ) : 0<(ℓ : ℝ) :=
  (abs_pos.mpr (inv_ne_zero (r.b_ne 0))).trans_le (r.inverse_bound 0)
lemma Recurrence.unstable_size_lower (r : Recurrence ℓ δ) (n : ℕ) : 1≤(ℓ : ℝ)*|r.b n| := by
  have hh := mul_le_mul_of_nonneg_right (r.inverse_bound n) (abs_nonneg (r.b n))
  simpa only [abs_inv,inv_mul_cancel₀ (abs_ne_zero.mpr (r.b_ne n))] using hh
lemma Recurrence.unstable_size_ge_one (r : Recurrence ℓ δ) (h : ℓ+δ<1) (n : ℕ) : 1≤|r.b n| := by
  have hℓ : (ℓ : ℝ)≤1 := NNReal.coe_le_coe.mpr ((le_add_of_nonneg_right (show (0 : ℝ≥0)≤δ from bot_le)).trans h.le)
  exact (r.unstable_size_lower n).trans ((mul_le_mul_of_nonneg_right hℓ (abs_nonneg _)).trans_eq (one_mul _))
lemma Recurrence.unstable_expansion (r : Recurrence ℓ δ) (h : ℓ+δ<1) (n : ℕ) :
    1≤((ℓ+δ : ℝ≥0) : ℝ)*(|r.b n|-(δ : ℝ)) := by
  have hq : ((ℓ+δ : ℝ≥0) : ℝ)≤1 := NNReal.coe_le_coe.mpr h.le
  have hb : ((ℓ+δ : ℝ≥0) : ℝ)≤|r.b n| := hq.trans (r.unstable_size_ge_one h n)
  have hd := mul_nonneg δ.coe_nonneg (sub_nonneg.mpr hb)
  have hl := r.unstable_size_lower n
  simp only [NNReal.coe_add] at hd ⊢
  nlinarith

lemma Recurrence.step_snd_lower (r : Recurrence ℓ δ) (n : ℕ) (v w : Plane) :
    |r.b n| *|v.2-w.2|≤|(r.step n v).2-(r.step n w).2|+(δ : ℝ)*‖v-w‖ := by
  have hr := (r.lipschitz n).dist_le_mul v w
  rw [dist_eq_norm,dist_eq_norm] at hr
  have hri := (norm_snd_le (r.remainder n v-r.remainder n w)).trans hr
  have he : r.b n*(v.2-w.2)=((r.step n v).2-(r.step n w).2)-
      ((r.remainder n v).2-(r.remainder n w).2) := by dsimp only [Recurrence.step]; ring
  rw [←abs_mul,he]
  exact (abs_sub _ _).trans (add_le_add le_rfl hri)

lemma Recurrence.unstable_cone_step (r : Recurrence ℓ δ) (h : ℓ+δ<1) (n : ℕ) (v w : Plane)
    (hcone : |v.1-w.1|≤|v.2-w.2|) :
    |(r.step n v).1-(r.step n w).1|≤|(r.step n v).2-(r.step n w).2| ∧
    |v.2-w.2|≤((ℓ+δ : ℝ≥0) : ℝ)*|(r.step n v).2-(r.step n w).2| := by
  have hvw : ‖v-w‖=|v.2-w.2| := max_eq_right hcone
  have hl := r.step_snd_lower n v w
  rw [hvw] at hl
  have hl' : (|r.b n|-(δ : ℝ))*|v.2-w.2|≤|(r.step n v).2-(r.step n w).2| := by nlinarith
  have hb : |v.2-w.2|≤((ℓ+δ : ℝ≥0) : ℝ)*|(r.step n v).2-(r.step n w).2| := by
    calc
      _ ≤ (((ℓ+δ : ℝ≥0) : ℝ)*(|r.b n|-(δ : ℝ)))*|v.2-w.2| := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (r.unstable_expansion h n) (abs_nonneg (v.2-w.2))
      _ = ((ℓ+δ : ℝ≥0) : ℝ)*((|r.b n|-(δ : ℝ))*|v.2-w.2|) := mul_assoc _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hl' (ℓ+δ).coe_nonneg
  refine ⟨?_,hb⟩
  have hf := step_fst_sub_bound r n v w
  rw [hvw] at hf
  have hq : ((ℓ+δ : ℝ≥0) : ℝ)≤1 := NNReal.coe_le_coe.mpr h.le
  have hc : ((ℓ+δ : ℝ≥0) : ℝ)*|v.2-w.2|≤|v.2-w.2| :=
    (mul_le_mul_of_nonneg_right hq (abs_nonneg _)).trans_eq (one_mul _)
  have hb' : ((ℓ+δ : ℝ≥0) : ℝ)*|(r.step n v).2-(r.step n w).2|≤|(r.step n v).2-(r.step n w).2| :=
    (mul_le_mul_of_nonneg_right hq (abs_nonneg _)).trans_eq (one_mul _)
  exact hf.trans (hc.trans (hb.trans hb'))

noncomputable def Recurrence.orbit (r : Recurrence ℓ δ) (v : Plane) : ℕ → Plane
  | 0 => v
  | n+1 => r.step n (r.orbit v n)
lemma Recurrence.orbit_continuous (r : Recurrence ℓ δ) (n : ℕ) : Continuous (fun v => r.orbit v n) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih =>
    exact ((continuous_const.mul ih.fst).add ((r.lipschitz n).continuous.comp ih).fst).prodMk
      ((continuous_const.mul ih.snd).add ((r.lipschitz n).continuous.comp ih).snd)

lemma Recurrence.orbit_unstable_cone (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s t u : ℝ) (n : ℕ) :
    |(r.orbit (s,t) n).1-(r.orbit (s,u) n).1|≤|(r.orbit (s,t) n).2-(r.orbit (s,u) n).2| ∧
    |t-u|≤((ℓ+δ : ℝ≥0) : ℝ)^n*|(r.orbit (s,t) n).2-(r.orbit (s,u) n).2| := by
  induction n with
  | zero => exact ⟨by simp only [Recurrence.orbit,sub_self,abs_zero]; positivity,by simp only [Recurrence.orbit,pow_zero,one_mul,le_refl]⟩
  | succ n ih =>
    have hh := r.unstable_cone_step h n (r.orbit (s,t) n) (r.orbit (s,u) n) ih.1
    refine ⟨hh.1,ih.2.trans ?_⟩
    exact (mul_le_mul_of_nonneg_left hh.2 (pow_nonneg (ℓ+δ).coe_nonneg n)).trans_eq (by
      simp only [Recurrence.orbit,pow_succ]; ring)

def Recurrence.trappedBox (r : Recurrence ℓ δ) (n : ℕ) : Set Plane :=
  {v | ∀ j : ℕ, j≤n → ‖r.orbit v j‖≤1}
lemma Recurrence.trappedBox_closed (r : Recurrence ℓ δ) (n : ℕ) : IsClosed (r.trappedBox n) := by
  have he : r.trappedBox n=⋂ j : ℕ, ⋂ (_ : j≤n), {v | ‖r.orbit v j‖≤1} := by ext v; simp only [Recurrence.trappedBox,mem_ofPred_eq,mem_iInter]
  rw [he]
  exact isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_le (r.orbit_continuous j).norm continuous_const
lemma Recurrence.trappedBox_fiber_diameter (r : Recurrence ℓ δ) (h : ℓ+δ<1) (n : ℕ)
    {s t u : ℝ} (ht : (s,t)∈r.trappedBox n) (hu : (s,u)∈r.trappedBox n) :
    |t-u|≤2*((ℓ+δ : ℝ≥0) : ℝ)^n := by
  have htn := (norm_snd_le (r.orbit (s,t) n)).trans (ht n le_rfl)
  have hun := (norm_snd_le (r.orbit (s,u) n)).trans (hu n le_rfl)
  simp only [Real.norm_eq_abs] at htn hun
  have hb : |(r.orbit (s,t) n).2-(r.orbit (s,u) n).2|≤2 := (abs_sub _ _).trans (by linarith)
  exact (r.orbit_unstable_cone h s t u n).2.trans
    ((mul_le_mul_of_nonneg_left hb (pow_nonneg (ℓ+δ).coe_nonneg n)).trans_eq (by ring))

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma Recurrence.trappedBox_fiber_volume (r : Recurrence ℓ δ) (h : ℓ+δ<1) (n : ℕ) (s : ℝ) :
    volume (Prod.mk s ⁻¹' r.trappedBox n)≤ENNReal.ofReal (2*((ℓ+δ : ℝ≥0) : ℝ)^n) := by
  apply (Real.volume_le_diam _).trans
  apply Metric.ediam_le_iff.mpr
  intro t ht u hu
  rw [edist_dist,Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal (r.trappedBox_fiber_diameter h n ht hu)

lemma Recurrence.trappedBox_fiber_empty (r : Recurrence ℓ δ) (n : ℕ) {s : ℝ} (hs : s∉Icc (-1 : ℝ) 1) :
    Prod.mk s ⁻¹' r.trappedBox n=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hh := (norm_fst_le (s,t)).trans (ht 0 (Nat.zero_le n))
  exact hs (abs_le.mp hh)

theorem Recurrence.trappedBox_volume (r : Recurrence ℓ δ) (h : ℓ+δ<1) (n : ℕ) :
    volume (r.trappedBox n)≤ENNReal.ofReal (4*((ℓ+δ : ℝ≥0) : ℝ)^n) := by
  change ((volume : Measure ℝ).prod volume) (r.trappedBox n)≤_
  rw [Measure.prod_apply (r.trappedBox_closed n).measurableSet]
  calc
    _ ≤ ∫⁻ s : ℝ, (Icc (-1 : ℝ) 1).indicator
        (fun _ => ENNReal.ofReal (2*((ℓ+δ : ℝ≥0) : ℝ)^n)) s ∂volume := by
      apply lintegral_mono
      intro s
      change volume (Prod.mk s ⁻¹' r.trappedBox n)≤_
      by_cases hs : s∈Icc (-1 : ℝ) 1
      · rw [indicator_of_mem hs]
        exact r.trappedBox_fiber_volume h n s
      · rw [indicator_of_notMem hs,r.trappedBox_fiber_empty n hs,measure_empty]
    _ = _ := by
      rw [lintegral_indicator measurableSet_Icc,setLIntegral_const,Real.volume_Icc,
        ←ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

lemma fine_nonlinearity_coefficient (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus)
    (hz : FineRegular k χ ε z) (hn : FineRegular k χ ε (standardMap k z)) :
    ‖fineInverse k χ ε δ (standardMap k z)‖*derivativeVariationBound k*‖fineFrame k χ ε δ z‖^2≤δ := by
  let a := chartRadius k χ ε z
  let b := chartRadius k χ ε (standardMap k z)
  let c := ‖lyapunovCoframe k χ (standardMap k z)‖
  let η := fineScale k ε δ
  have ha : 0<a := chartRadius_pos k χ ε z
  have hb : 0<b := chartRadius_pos k χ ε (standardMap k z)
  have hη : 0<η := fineScale_pos k ε hδ
  have hc : 0≤c := norm_nonneg _
  have hbc : b*c≤1 := hn.2.2.2.2.1
  have hab : a/b≤Real.exp ε := slow_radius_ratio ha hb hz.2.2.2.2.2.1
  have hD := derivativeVariationBound_nonneg k
  have hF : ‖fineFrame k χ ε δ z‖≤2*(η*a) := fineFrame_norm_le k χ ε hδ z
  have hC : ‖fineInverse k χ ε δ (standardMap k z)‖≤(η*b)⁻¹*c :=
    flatInverse_norm_le (fineSize_pos k χ ε hδ _).le _
  have hEF : (Real.exp ε)^2=Real.exp (2*ε) := by rw [pow_two,←Real.exp_add]; congr 1; ring
  have hsqr : (a/b)^2≤Real.exp (2*ε) := by
    rw [←hEF]
    exact pow_le_pow_left₀ (div_nonneg ha.le hb.le) hab 2
  calc
    _ ≤ ((η*b)⁻¹*c)*derivativeVariationBound k*(2*(η*a))^2 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hC hD)
        (pow_le_pow_left₀ (norm_nonneg _) hF 2) (sq_nonneg _)
        (mul_nonneg (mul_nonneg (inv_nonneg.mpr (mul_nonneg hη.le hb.le)) hc) hD)
    _ = (4*derivativeVariationBound k*η)*((b*c)*(a/b)^2) := by
      field_simp [ne_of_gt hη,ne_of_gt hb]; ring
    _ ≤ (4*derivativeVariationBound k*η)*(1*Real.exp (2*ε)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hbc hsqr (sq_nonneg _) (by norm_num)) (by positivity)
    _ = δ*(derivativeVariationBound k/(2*(1+derivativeVariationBound k))) := by
      dsimp [η,fineScale]
      field_simp [ne_of_gt (Real.exp_pos (2*ε)),ne_of_gt (show 0<1+derivativeVariationBound k by linarith)]
      ring
    _ ≤ δ*1 := by
      apply mul_le_mul_of_nonneg_left _ hδ.le
      apply (div_le_iff₀ (show 0<2*(1+derivativeVariationBound k) by linarith)).mpr
      linarith
    _ = _ := mul_one _

noncomputable def fineRemainder (k χ ε δ : ℝ) (z : ℂ) : RealPlane → RealPlane :=
  flatRemainder k z (fineFrame k χ ε δ (complexProjection z))
    (fineInverse k χ ε δ (standardMap k (complexProjection z)))
@[simp] lemma fineRemainder_zero (k χ ε δ : ℝ) (z : ℂ) : fineRemainder k χ ε δ z 0=0 :=
  flatRemainder_zero _ _ _ _
lemma fineRemainder_lipschitz (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : ℂ)
    (hz : FineRegular k χ ε (complexProjection z)) (hn : FineRegular k χ ε (standardMap k (complexProjection z)))
    {v w : RealPlane} (hv : ‖v‖≤1) (hw : ‖w‖≤1) :
    ‖fineRemainder k χ ε δ z v-fineRemainder k χ ε δ z w‖≤δ*‖v-w‖ :=
  (flatRemainder_sub_bound k z _ _ hv hw).trans
    (mul_le_mul_of_nonneg_right (fine_nonlinearity_coefficient k χ ε hδ _ hz hn) (norm_nonneg _))
lemma fine_derivative_diagonal (k χ ε δ : ℝ) (z : Torus) (hz : FineRegular k χ ε z) (v : RealPlane) :
    fineInverse k χ ε δ (standardMap k z) (standardDerivative k z (fineFrame k χ ε δ z v)) =
      (fineStableMultiplier k χ ε δ z*v.1,fineUnstableMultiplier k χ ε δ z*v.2) :=
  flat_diagonal _ _ _ hz.2.1 v
lemma fine_step (k χ ε δ : ℝ) (z : ℂ) (hz : FineRegular k χ ε (complexProjection z)) (v : RealPlane) :
    fineInverse k χ ε δ (standardMap k (complexProjection z))
      (standardLift k (z+fineFrame k χ ε δ (complexProjection z) v)-standardLift k z) =
      (fineStableMultiplier k χ ε δ (complexProjection z)*v.1+(fineRemainder k χ ε δ z v).1,
        fineUnstableMultiplier k χ ε δ (complexProjection z)*v.2+(fineRemainder k χ ε δ z v).2) := by
  have hdiff : standardLift k (z+fineFrame k χ ε δ (complexProjection z) v)-standardLift k z =
      standardDerivative k (complexProjection z) (fineFrame k χ ε δ (complexProjection z) v)+
        liftRemainder k z (fineFrame k χ ε δ (complexProjection z) v) := by unfold liftRemainder; abel
  rw [hdiff,map_add,fine_derivative_diagonal k χ ε δ _ hz]
  rfl
lemma fine_lift_step (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : ℂ)
    (hz : FineRegular k χ ε (complexProjection z)) (hn : FineRegular k χ ε (standardMap k (complexProjection z))) (v : RealPlane) :
    standardLift k (z+fineFrame k χ ε δ (complexProjection z) v) = standardLift k z+
      fineFrame k χ ε δ (standardMap k (complexProjection z))
        (fineStableMultiplier k χ ε δ (complexProjection z)*v.1+(fineRemainder k χ ε δ z v).1,
          fineUnstableMultiplier k χ ε δ (complexProjection z)*v.2+(fineRemainder k χ ε δ z v).2) := by
  have hh := congrArg (fineFrame k χ ε δ (standardMap k (complexProjection z))) (fine_step k χ ε δ z hz v)
  rw [fineFrame_inverse k χ ε hδ _ hn.1] at hh
  exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

noncomputable def fineLinearRate (χ ε : ℝ) : ℝ≥0 := ⟨Real.exp (-χ+ε),(Real.exp_pos _).le⟩
noncomputable def fineErrorRate (δ : ℝ) (hδ : 0<δ) : ℝ≥0 := ⟨δ,hδ.le⟩
lemma fine_regular_lift_next (k χ ε : ℝ) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) (n : ℕ) :
    FineRegular k χ ε (standardMap k (complexProjection ((standardLift k)^[n] w))) := by
  simpa only [Function.iterate_succ_apply',complexProjection_standardLift] using hw (n+1)
noncomputable def fineLocalRecurrence (k χ ε δ : ℝ) (hδ : 0<δ) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) :
    LocalRecurrence (fineLinearRate χ ε) (fineErrorRate δ hδ) where
  a n := fineStableMultiplier k χ ε δ (complexProjection ((standardLift k)^[n] w))
  b n := fineUnstableMultiplier k χ ε δ (complexProjection ((standardLift k)^[n] w))
  remainder n := fineRemainder k χ ε δ ((standardLift k)^[n] w)
  stable_bound n := fineStableMultiplier_bound k χ ε hδ _ (hw n)
  inverse_bound n := fineUnstableMultiplier_inverse_bound k χ ε hδ _ (hw n)
  b_ne n := fineUnstableMultiplier_ne k χ ε hδ _ (hw n)
  local_lipschitz n _ _ hv hu := fineRemainder_lipschitz k χ ε hδ _ (hw n) (fine_regular_lift_next k χ ε w hw n) hv hu
  zero _ := fineRemainder_zero _ _ _ _ _

noncomputable def fineCoordinate (k χ ε δ : ℝ) (w p : ℂ) (n : ℕ) : RealPlane :=
  fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))
    ((standardLift k)^[n] p-(standardLift k)^[n] w)
lemma fineCoordinate_initial (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (w : ℂ)
    (hw : FineRegular k χ ε (complexProjection w)) (v : RealPlane) :
    fineCoordinate k χ ε δ w (w+fineFrame k χ ε δ (complexProjection w) v) 0=v := by
  change fineInverse k χ ε δ (complexProjection w) (w+fineFrame k χ ε δ (complexProjection w) v-w)=v
  rw [add_sub_cancel_left,fineInverse_frame k χ ε hδ _ hw.1]
lemma fineCoordinate_step (k χ ε δ : ℝ) (hδ : 0<δ) (w p : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) (n : ℕ) :
    fineCoordinate k χ ε δ w p (n+1)=
      (fineLocalRecurrence k χ ε δ hδ w hw).step n (fineCoordinate k χ ε δ w p n) := by
  have he : (standardLift k)^[n] p=(standardLift k)^[n] w+
      fineFrame k χ ε δ (complexProjection ((standardLift k)^[n] w)) (fineCoordinate k χ ε δ w p n) := by
    dsimp only [fineCoordinate]
    rw [fineFrame_inverse k χ ε hδ _ (hw n).1]
    abel
  conv_lhs => simp only [fineCoordinate,Function.iterate_succ_apply']
  rw [he]
  simpa only [Function.iterate_succ_apply',complexProjection_standardLift,fineLocalRecurrence,LocalRecurrence.step] using
    fine_step k χ ε δ ((standardLift k)^[n] w) (hw n) (fineCoordinate k χ ε δ w p n)

def fineTrapped (k χ ε δ : ℝ) (w : ℂ) (n : ℕ) : Set RealPlane :=
  {v | ∀ j : ℕ, j≤n → ‖fineCoordinate k χ ε δ w
    (w+fineFrame k χ ε δ (complexProjection w) v) j‖≤1}
lemma fineTrapped_subset (k χ ε δ : ℝ) (hδ : 0<δ) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) (n : ℕ) :
    fineTrapped k χ ε δ w n ⊆ (fineLocalRecurrence k χ ε δ hδ w hw).extend.trappedBox n := by
  intro v hv
  have he : ∀ j : ℕ, j≤n → (fineLocalRecurrence k χ ε δ hδ w hw).extend.orbit v j=
      fineCoordinate k χ ε δ w (w+fineFrame k χ ε δ (complexProjection w) v) j := by
    intro j
    induction j with
    | zero => intro _; exact (fineCoordinate_initial k χ ε hδ w (hw 0) v).symm
    | succ j ih =>
      intro hj
      rw [Recurrence.orbit,ih (by omega),extend_step_eq _ j (hv j (by omega)),fineCoordinate_step]
  intro j hj
  rw [he j hj]
  exact hv j hj

theorem fineTrapped_volume (k χ ε δ : ℝ) (hδ : 0<δ)
    (hq : Real.exp (-χ+ε)+δ<1) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) (n : ℕ) :
    volume (fineTrapped k χ ε δ w n)≤ENNReal.ofReal (4*(Real.exp (-χ+ε)+δ)^n) := by
  have hq' : fineLinearRate χ ε+fineErrorRate δ hδ<1 := hq
  exact (measure_mono (fineTrapped_subset k χ ε δ hδ w hw n)).trans
    ((fineLocalRecurrence k χ ε δ hδ w hw).extend.trappedBox_volume hq' n)

lemma fine_parameters_for_rate {a χ : ℝ} (ha : 0<a) (hχ : a<χ) :
    ∃ ε δ : ℝ, 0<ε ∧ 0<δ ∧ Real.exp (-χ+ε)+δ<1 ∧ Real.exp (-χ+ε)+δ≤Real.exp (-a) := by
  let ε := (χ-a)/2
  have he : 0<ε := by dsimp [ε]; linarith
  have hx : Real.exp (-χ+ε)<Real.exp (-a) := Real.exp_lt_exp.mpr (by dsimp [ε]; linarith)
  have h1 : Real.exp (-a)<1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
  refine ⟨ε,(Real.exp (-a)-Real.exp (-χ+ε))/2,he,?_,?_,?_⟩ <;> linarith

theorem ae_sharp_fine_volume (k : ℝ) (hk : 0≤k) {a χ : ℝ} (ha : 0<a) (hχ : a<χ) :
    ∃ ε δ : ℝ, 0<ε ∧ 0<δ ∧
      ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ), ∀ w : ℂ, complexProjection w=z → ∀ n : ℕ,
        volume (fineTrapped k χ ε δ w n)≤ENNReal.ofReal (4*Real.exp (-a*(n : ℝ))) := by
  obtain ⟨ε,δ,hε,hδ,hq,hqa⟩ := fine_parameters_for_rate ha hχ
  refine ⟨ε,δ,hε,hδ,?_⟩
  filter_upwards [ae_fineRegular_all_iterates k hk (ha.trans hχ) hε] with z hz
  intro w hw n
  have hr (j : ℕ) : FineRegular k χ ε (complexProjection ((standardLift k)^[j] w)) := by
    simpa only [complexProjection_iterate,hw] using (hz j).1
  apply (fineTrapped_volume k χ ε δ hδ hq w hr n).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ (Real.exp (-a))^n := pow_le_pow_left₀ (by positivity) hqa n
    _ = _ := by rw [←Real.exp_nat_mul]; congr 1; ring

end StandardMapEntropy

end
end

end OAI
