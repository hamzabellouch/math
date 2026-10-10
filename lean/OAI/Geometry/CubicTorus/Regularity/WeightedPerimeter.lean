import Mathlib
import OAI.Geometry.CubicTorus.Regularity.NormalFirstVariation

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open scoped RealInnerProductSpace
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace
namespace CubicTorus

theorem bv_isoperimetric_small_of_measurable {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) (hV : (torusVolume E).toReal ≤ 1 / 2) :
    (torusVolume E).toReal ^ (2 / 3 : ℝ) ≤ 12 * (perimeter E).toReal := by
  let V := (torusVolume E).toReal
  let P := (perimeter E).toReal
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hP0 : 0 ≤ P := ENNReal.toReal_nonneg
  by_cases hz : V = 0
  · change V ^ (2 / 3 : ℝ) ≤ 12 * P
    rw [hz, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)]
    positivity
  have hVp : 0 < V := lt_of_le_of_ne hV0 (Ne.symm hz)
  let r := (2 * V) ^ (1 / 3 : ℝ)
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by positivity) _
  have hr3 : r ^ 3 = 2 * V := by
    dsimp only [r]
    simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (by positivity : 0 ≤ 2 * V)
      (by norm_num : (3 : ℕ) ≠ 0)
  have hr1 : r ≤ 1 := by
    have hh : 2 * V ≤ 1 := by dsimp only [V]; linarith
    dsimp only [r]
    exact (Real.rpow_le_rpow (by positivity) hh (by norm_num)).trans_eq (Real.one_rpow _)
  have hi := bv_cubical_isoperimetric hE hP ⟨hr0.le, hr1⟩
  change V * (r ^ 3 - V) ≤ 3 * r ^ 4 * P at hi
  rw [hr3] at hi
  have hi' : V ^ 2 ≤ 3 * r ^ 4 * P := by nlinarith [hi]
  have hs : r ^ 4 * (r ^ 2 - 12 * P) ≤ 0 := by
    have hsq := congrArg (fun a : ℝ ↦ a ^ 2) hr3
    nlinarith [hsq]
  have hr2 : r ^ 2 ≤ 12 * P := by
    have hh := nonpos_of_mul_nonpos_right hs (pow_pos hr0 4)
    linarith
  have he : (2 * V) ^ (2 / 3 : ℝ) = r ^ 2 := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 2 * V)]
    congr 1
    norm_num
  change V ^ (2 / 3 : ℝ) ≤ 12 * P
  calc
    _ ≤ (2 * V) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow hV0 (by linarith) (by norm_num)
    _ = r ^ 2 := he
    _ ≤ _ := hr2

theorem bv_isoperimetric_small {E : Set Torus} (hE : FinitePerimeter E)
    (hV : (torusVolume E).toReal ≤ 1 / 2) :
    (torusVolume E).toReal ^ (2 / 3 : ℝ) ≤ 12 * (perimeter E).toReal := by
  have he := hE.1.toMeasurable_ae_eq
  have hp := perimeter_congr_ae he
  have hv : torusVolume (toMeasurable torusVolume E) = torusVolume E :=
    measure_congr he
  have hh := bv_isoperimetric_small_of_measurable
    (measurableSet_toMeasurable torusVolume E) (hp ▸ hE.2.ne) (by simpa only [hv] using hV)
  simpa only [hp, hv] using hh

theorem bv_isoperimetric {E : Set Torus} (hE : FinitePerimeter E) :
    (min (torusVolume E).toReal (1 - (torusVolume E).toReal)) ^ (2 / 3 : ℝ) ≤
      12 * (perimeter E).toReal := by
  let V := (torusVolume E).toReal
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hV1 : V ≤ 1 := by
    have hh : torusVolume E ≤ 1 := by simpa only [torusVolume_univ] using (measure_mono (μ := torusVolume) (subset_univ E))
    exact (ENNReal.toReal_mono (by simp) hh).trans_eq ENNReal.toReal_one
  have hv : torusVolume E = ENNReal.ofReal V :=
    (ENNReal.ofReal_toReal (measure_ne_top torusVolume E)).symm
  have hcomp := volume_compl_of_volume hE.1 hV0 hv
  have hc : (torusVolume Eᶜ).toReal = 1 - V := by
    rw [hcomp, ENNReal.toReal_ofReal (sub_nonneg.2 hV1)]
  by_cases hsmall : V ≤ 1 / 2
  · rw [min_eq_left (by dsimp only [V] at *; linarith)]
    exact bv_isoperimetric_small hE hsmall
  · rw [min_eq_right (by dsimp only [V] at *; linarith)]
    have hh := bv_isoperimetric_small (finitePerimeter_compl.2 hE)
      (by rw [hc]; linarith)
    rw [hc, perimeter_compl hE.1] at hh
    exact hh

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

lemma normalTest_le_one {F : Cover → Cover} (hF : AdmissibleField F) (z : NormalBundle) :
    normalTest F hF.1.continuous z ≤ 1 := by
  calc
    _ ≤ ‖(z.2 : Cover)‖ * ‖F z.1‖ := real_inner_le_norm _ _
    _ ≤ 1 := by simpa only [z.2.property, one_mul] using hF.2.2 z.1

theorem normalMeasure_weighted_saturation {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) (w : C(NormalBundle, ℝ))
    {A : ℝ} (hA : ∀ (F : Cover → Cover) (hF : AdmissibleField F),
      (∫ z, w z * normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle)) ≤ A) :
    (∫ z, w z ∂(μ : Measure NormalBundle)) ≤ A := by
  let C : ℝ := ‖w‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hwC (z : NormalBundle) : w z ≤ C := by
    exact (le_abs_self _).trans ((w.norm_coe_le_norm z).trans (by dsimp [C]; linarith))
  let P : ℝ := (perimeter E).toReal
  let I : ℝ := ∫ z, w z ∂(μ : Measure NormalBundle)
  let B : ℝ := P + (A - I) / C
  have hiw : Integrable w (μ : Measure NormalBundle) := w.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbound (F : Cover → Cover) (hF : AdmissibleField F) :
      (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x) ≤ B := by
    let T := normalTest F hF.1.continuous
    have hiT : Integrable T (μ : Measure NormalBundle) := T.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hiwT : Integrable (fun z ↦ w z * T z) (μ : Measure NormalBundle) :=
      (w.continuous.mul T.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hdef (z : NormalBundle) :
        w z - w z * T z ≤ C * (1 - T z) := by
      have hT : 0 ≤ 1 - T z := sub_nonneg.mpr (normalTest_le_one hF z)
      nlinarith [mul_le_mul_of_nonneg_right (hwC z) hT]
    have hh := integral_mono (hiw.sub hiwT)
      (((integrable_const (1 : ℝ)).sub hiT).const_mul C) hdef
    simp only [Pi.sub_apply] at hh
    rw [integral_sub hiw hiwT, integral_const_mul,
      integral_sub (integrable_const (1 : ℝ)) hiT] at hh
    have hmass : (∫ _ : NormalBundle, (1 : ℝ) ∂(μ : Measure NormalBundle)) = P := by
      simpa only [integral_const, smul_eq_mul, mul_one, P,
        FiniteMeasure.mass, FiniteMeasure.coeFn_def, Measure.real, ENNReal.toReal] using hμ.1
    rw [hmass] at hh
    have hcap : (∫ z, w z * T z ∂(μ : Measure NormalBundle)) ≤ A := hA F hF
    have hflux : (∫ z, T z ∂(μ : Measure NormalBundle)) =
        ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := hμ.2 F hF
    rw [← hflux]
    dsimp only [B]
    apply (mul_le_mul_iff_left₀ hC).mp
    rw [add_mul, div_mul_cancel₀ _ hC.ne']
    dsimp only [I] at *
    nlinarith
  have hB : 0 ≤ B := by
    simpa only [divergence_zero, integral_zero] using hbound (fun _ ↦ 0) admissible_zero
  have hP : perimeter E ≤ ENNReal.ofReal B := by
    unfold perimeter
    exact iSup_le fun F ↦ iSup_le fun hF ↦ ENNReal.ofReal_le_ofReal (hbound F hF)
  have hPB : P ≤ B := by
    simpa only [P, ENNReal.toReal_ofReal hB] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hP
  have hneg : (A - I) / C ≥ 0 := by dsimp only [B] at hPB; linarith
  have hh := mul_nonneg hneg hC.le
  rw [div_mul_cancel₀ _ hC.ne'] at hh
  exact sub_nonneg.mp hh

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

def weightedPerimeter (E : Set Torus) (w : Cover → ℝ) : ℝ≥0∞ :=
  ⨆ (F : Cover → Cover) (_ : AdmissibleField F),
    ENNReal.ofReal (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      divergence (fun y ↦ w y • F y) x)

lemma normalMeasure_weighted_flux {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ z, w z.1 * normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle)) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        divergence (fun y ↦ w y • F y) x := by
  obtain ⟨M, hM, hb⟩ := periodic_bounded hw.continuous hp
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ w x • F x) := hw.smul hF.1
  have hGp : ∀ n x, w (x + latticeVector n) • F (x + latticeVector n) = w x • F x := by
    intro n x
    rw [hp, hF.2.1]
  have hGb (x : Cover) : ‖w x • F x‖ ≤ M + 1 := by
    rw [norm_smul]
    calc
      _ ≤ ‖w x‖ * 1 := mul_le_mul_of_nonneg_left (hF.2.2 x) (norm_nonneg _)
      _ ≤ M + 1 := by simpa only [mul_one] using (hb x).trans (by linarith)
  simpa only [normalTest, ContinuousMap.coe_mk, real_inner_smul_right] using
    normalMeasure_flux hμ hG hGp (by linarith : 0 < M + 1) hGb

theorem normalMeasure_weightedPerimeter {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x) (hn : ∀ x, 0 ≤ w x) :
    weightedPerimeter E w = ENNReal.ofReal
      (∫ z, w z.1 ∂(μ : Measure NormalBundle)) := by
  let W : C(NormalBundle, ℝ) := ⟨fun z ↦ w z.1,
    hw.continuous.comp (continuous_subtype_val.comp continuous_fst)⟩
  have hiW : Integrable W (μ : Measure NormalBundle) :=
    W.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hle : weightedPerimeter E w ≤ ENNReal.ofReal (∫ z, W z ∂(μ : Measure NormalBundle)) := by
    apply iSup_le
    intro F
    apply iSup_le
    intro hF
    apply ENNReal.ofReal_le_ofReal
    rw [← normalMeasure_weighted_flux hμ hw hp hF]
    apply integral_mono ((W.continuous.mul (normalTest F hF.1.continuous).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) hiW
    intro z
    exact (mul_le_mul_of_nonneg_left (normalTest_le_one hF z) (hn z.1)).trans_eq (mul_one _)
  have htop : weightedPerimeter E w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  apply le_antisymm hle
  rw [ENNReal.ofReal_le_iff_le_toReal htop]
  apply normalMeasure_weighted_saturation hμ W
  intro F hF
  change (∫ z, w z.1 * normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle)) ≤ _
  rw [normalMeasure_weighted_flux hμ hw hp hF]
  apply (ENNReal.ofReal_le_iff_le_toReal htop).mp
  exact le_iSup_of_le F (le_iSup_of_le hF le_rfl)

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma exists_admissible_flux_gt (E : Set Torus) {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : Cover → Cover) (_hF : AdmissibleField F),
      (perimeter E).toReal - ε < ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
  by_cases h : (perimeter E).toReal < ε
  · refine ⟨fun _ ↦ 0, admissible_zero, ?_⟩
    simpa only [divergence_zero, integral_zero] using sub_neg.mpr h
  · have hn : 0 ≤ (perimeter E).toReal - ε := sub_nonneg.mpr (le_of_not_gt h)
    by_contra! hnone
    have hb : perimeter E ≤ ENNReal.ofReal ((perimeter E).toReal - ε) := by
      exact iSup_le fun F ↦ iSup_le fun hF ↦ ENNReal.ofReal_le_ofReal (hnone F hF)
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rw [ENNReal.toReal_ofReal hn] at hh
    linarith

lemma normalMeasure_approx_error {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ z, ‖F z.1 - (z.2 : Cover)‖ ^ 2 ∂(μ : Measure NormalBundle)) ≤
      2 * ((perimeter E).toReal -
        ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x) := by
  have hFc : Continuous (fun z : NormalBundle ↦ F (z.1 : Cover)) :=
    hF.1.continuous.comp (continuous_subtype_val.comp continuous_fst)
  have hNc : Continuous (fun z : NormalBundle ↦ (z.2 : Cover)) :=
    continuous_subtype_val.comp continuous_snd
  have hi : Integrable (fun z : NormalBundle ↦ ‖F z.1 - (z.2 : Cover)‖ ^ 2)
      (μ : Measure NormalBundle) :=
    ((hFc.sub hNc).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have ht : Integrable (normalTest F hF.1.continuous) (μ : Measure NormalBundle) :=
    (normalTest F hF.1.continuous).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp (z : NormalBundle) : ‖F z.1 - (z.2 : Cover)‖ ^ 2 ≤
      2 * (1 - normalTest F hF.1.continuous z) := by
    rw [norm_sub_sq_real, z.2.property, real_inner_comm]
    dsimp only [normalTest, ContinuousMap.coe_mk]
    nlinarith [hF.2.2 z.1, norm_nonneg (F z.1)]
  have hh := integral_mono hi (((integrable_const (1 : ℝ)).sub ht).const_mul 2) hp
  simp only [Pi.sub_apply] at hh
  rw [integral_const_mul, integral_sub (integrable_const _) ht, hμ.2 F hF] at hh
  have hmass : (∫ _ : NormalBundle, (1 : ℝ) ∂(μ : Measure NormalBundle)) = (perimeter E).toReal := by
    simpa only [integral_const, smul_eq_mul, mul_one,
      FiniteMeasure.mass, FiniteMeasure.coeFn_def, Measure.real, ENNReal.toReal] using hμ.1
  rwa [hmass] at hh

lemma tendstoInMeasure_of_integral_norm_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℕ → α → Cover} {g : α → Cover}
    (hi : ∀ n, Integrable (fun x ↦ ‖f n x - g x‖ ^ 2) μ)
    (hlim : Tendsto (fun n ↦ ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ f atTop g := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have he : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hh (n : ℕ) := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (Eventually.of_forall fun x ↦ sq_nonneg ‖f n x - g x‖) (hi n) (ε ^ 2)
  have hset (n : ℕ) : {x | ε ^ 2 ≤ ‖f n x - g x‖ ^ 2} = {x | ε ≤ ‖f n x - g x‖} := by
    ext x
    exact sq_le_sq₀ hε.le (norm_nonneg _)
  have hb (n : ℕ) : μ.real {x | ε ≤ ‖f n x - g x‖} ≤
      (∫ x, ‖f n x - g x‖ ^ 2 ∂μ) / (ε ^ 2) := by
    rw [le_div_iff₀ he]
    simpa only [hset n, mul_comm] using hh n
  have hzero : Tendsto (fun n ↦ (∫ x, ‖f n x - g x‖ ^ 2 ∂μ) / ε ^ 2) atTop (𝓝 0) := by
    simpa using hlim.div_const (ε ^ 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
    (fun n ↦ measureReal_nonneg) hb

theorem normalMeasure_exists_approximating_fields {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) :
    ∃ F : ℕ → Cover → Cover, (∀ n, AdmissibleField (F n)) ∧
      TendstoInMeasure (μ : Measure NormalBundle) (fun n z ↦ F n z.1) atTop
        (fun z ↦ (z.2 : Cover)) := by
  have hex (n : ℕ) := exists_admissible_flux_gt E
    (show 0 < (1 / 2 : ℝ) ^ n from pow_pos (by norm_num) n)
  choose F hF hnear using hex
  refine ⟨F, hF, tendstoInMeasure_of_integral_norm_sq ?_ ?_⟩
  · intro n
    have hc : Continuous (fun z : NormalBundle ↦ F n z.1 - (z.2 : Cover)) :=
      ((hF n).1.continuous.comp (continuous_subtype_val.comp continuous_fst)).sub
        (continuous_subtype_val.comp continuous_snd)
    exact (hc.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · have hb (n : ℕ) :
        (∫ z, ‖F n z.1 - (z.2 : Cover)‖ ^ 2 ∂(μ : Measure NormalBundle)) ≤ 2 * (1 / 2 : ℝ) ^ n := by
      have hh := normalMeasure_approx_error hμ (hF n)
      linarith [hnear n]
    have hz : Tendsto (fun n : ℕ ↦ 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
      (fun n ↦ integral_nonneg fun z ↦ sq_nonneg _) hb

theorem normalMeasure_exists_polar {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) :
    ∃ N : Torus → Cover, Measurable N ∧
      ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover) := by
  obtain ⟨F, hF, hconv⟩ := normalMeasure_exists_approximating_fields hμ
  obtain ⟨s, _, hae⟩ := hconv.exists_seq_tendsto_ae
  let G : ℕ → Torus → Cover := fun n x ↦ F (s n) (representative x)
  have hm (n : ℕ) : StronglyMeasurable (G n) :=
    ((hF (s n)).1.continuous.measurable.comp measurable_representative).stronglyMeasurable
  refine ⟨fun x ↦ limUnder atTop (G · x), (StronglyMeasurable.limUnder hm).measurable, ?_⟩
  filter_upwards [hae] with z hz
  have he : (fun n ↦ G n (quotientMap z.1)) = fun n ↦ F (s n) z.1 := by
    funext n
    exact periodic_representative (hF (s n)).2.1 z.1
  rw [he]
  exact hz.limUnder_eq

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

def IsPerimeterRepresentation (E : Set Torus) (σ : FiniteMeasure Torus) (N : Torus → Cover) : Prop :=
  (σ.mass : ℝ) = (perimeter E).toReal ∧ Measurable N ∧
  (∀ᵐ x ∂(σ : Measure Torus), ‖N x‖ = 1) ∧
  ∀ (F : Cover → Cover) (_hF : AdmissibleField F),
    (∫ x, ⟪N x, F (representative x)⟫ ∂(σ : Measure Torus)) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x

theorem exists_perimeterRepresentation {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) :
    ∃ (σ : FiniteMeasure Torus) (N : Torus → Cover), IsPerimeterRepresentation E σ N := by
  obtain ⟨μ, hmass, hflux⟩ := exists_normalMeasure hE hP
  have hμ : IsNormalMeasure E μ := ⟨hmass, hflux⟩
  obtain ⟨N, hNm, hN⟩ := normalMeasure_exists_polar hμ
  let q : NormalBundle → Torus := fun z ↦ quotientMap z.1
  have hq : Measurable q := measurable_quotientMap.comp (measurable_subtype_coe.comp measurable_fst)
  let σ : FiniteMeasure Torus := μ.map q
  refine ⟨σ, N, ?_, hNm, ?_, ?_⟩
  · have he : (σ : Measure Torus) univ = (μ : Measure NormalBundle) univ := by
      change (Measure.map q (μ : Measure NormalBundle)) univ = _
      rw [Measure.map_apply hq MeasurableSet.univ, preimage_univ]
    have hh := congrArg ENNReal.toReal he
    change (σ.mass : ℝ) = (μ.mass : ℝ) at hh
    exact hh.trans hmass
  · change ∀ᵐ x ∂Measure.map q (μ : Measure NormalBundle), ‖N x‖ = 1
    rw [ae_map_iff hq.aemeasurable (measurableSet_eq_fun hNm.norm measurable_const)]
    filter_upwards [hN] with z hz
    change ‖N (quotientMap z.1)‖ = 1
    rw [hz, z.2.property]
  · intro F hF
    have hm : Measurable (fun x ↦ ⟪N x, F (representative x)⟫) :=
      hNm.inner ((hF.1.continuous.measurable).comp measurable_representative)
    change (∫ x, ⟪N x, F (representative x)⟫ ∂Measure.map q (μ : Measure NormalBundle)) = _
    rw [integral_map hq.aemeasurable hm.aestronglyMeasurable]
    calc
      _ = ∫ z, normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle) := by
        apply integral_congr_ae
        filter_upwards [hN] with z hz
        change ⟪N (quotientMap z.1), F (representative (quotientMap z.1))⟫ = _
        rw [hz, periodic_representative hF.2.1]
        rfl
      _ = _ := hflux F hF

end CubicTorus

namespace CubicTorus

def regionDistance (E F : Set Torus) : ℝ :=
  ∫ x, ‖characteristic E x - characteristic F x‖ ∂torusVolume

lemma regionDistance_nonneg (E F : Set Torus) : 0 ≤ regionDistance E F :=
  integral_nonneg (fun _ ↦ norm_nonneg _)

lemma abs_realVolume_sub_le_regionDistance {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    |torusVolume.real E - torusVolume.real F| ≤ regionDistance E F := by
  rw [Measure.real_def, Measure.real_def, ← integral_characteristic hE.nullMeasurableSet,
    ← integral_characteristic hF.nullMeasurableSet,
    ← integral_sub (integrable_characteristic hE) (integrable_characteristic hF)]
  exact norm_integral_le_integral_norm (fun x : Torus ↦ characteristic E x - characteristic F x)

lemma regionDistance_translation (E F : Set Torus) (a : Torus) :
    regionDistance ((fun z ↦ z + a) ⁻¹' E) ((fun z ↦ z + a) ⁻¹' F) = regionDistance E F := by
  have he (x : Torus) :
      characteristic ((fun z ↦ z + a) ⁻¹' E) x = characteristic E (x + a) := by
    by_cases hx : x + a ∈ E <;> simp [characteristic, hx]
  have hf (x : Torus) :
      characteristic ((fun z ↦ z + a) ⁻¹' F) x = characteristic F (x + a) := by
    by_cases hx : x + a ∈ F <;> simp [characteristic, hx]
  unfold regionDistance
  simp_rw [he, hf]
  exact (measurePreserving_add_right torusVolume a).integral_comp
    (Homeomorph.addRight a).measurableEmbedding
      (fun x : Torus ↦ ‖characteristic E x - characteristic F x‖)

lemma characteristic_mul_eq_indicator (E : Set Torus) (g : Torus → ℝ) :
    (fun x ↦ characteristic E x * g x) = E.indicator g := by
  funext x
  by_cases hx : x ∈ E <;> simp [characteristic, hx]

lemma abs_weighted_characteristic_sub_le {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) {g : Torus → ℝ}
    (hg : Measurable g) {M : ℝ} (hb : ∀ x, ‖g x‖ ≤ M) :
    |(∫ x, characteristic E x * g x ∂torusVolume) -
      (∫ x, characteristic F x * g x ∂torusVolume)| ≤ M * regionDistance E F := by
  have hi : Integrable g torusVolume := Integrable.of_bound hg.aestronglyMeasurable M
    (Filter.Eventually.of_forall hb)
  have hiE : Integrable (fun x ↦ characteristic E x * g x) torusVolume := by
    rw [characteristic_mul_eq_indicator]
    exact hi.indicator hE
  have hiF : Integrable (fun x ↦ characteristic F x * g x) torusVolume := by
    rw [characteristic_mul_eq_indicator]
    exact hi.indicator hF
  rw [← integral_sub hiE hiF]
  calc
    _ ≤ ∫ x, ‖characteristic E x * g x - characteristic F x * g x‖ ∂torusVolume :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, M * ‖characteristic E x - characteristic F x‖ ∂torusVolume := by
      apply integral_mono (hiE.sub hiF).norm
        (((integrable_characteristic hE).sub (integrable_characteristic hF)).norm.const_mul M)
      intro x
      change ‖characteristic E x * g x - characteristic F x * g x‖ ≤
        M * ‖characteristic E x - characteristic F x‖
      rw [← sub_mul, norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := integral_const_mul _ _

lemma directionalFlux_eq_pairing (E : Set Torus) (hE : MeasurableSet E)
    (D : WallVariation) :
    directionalFlux E D.coordinate D.function =
      ∫ x, characteristic E x *
        fderiv ℝ D.function (representative x) (EuclideanSpace.single D.coordinate 1) ∂torusVolume := by
  rw [characteristic_mul_eq_indicator, integral_indicator hE]
  exact (setIntegral_lift
    ((D.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    (fun n x ↦ by rw [fderiv_periodic D.periodic]) hE).symm

lemma WallVariation.directionalDeriv_bound (D : WallVariation) (x : Cover) :
    ‖fderiv ℝ D.function x (EuclideanSpace.single D.coordinate 1)‖ ≤ (D.bound : ℝ) := by
  have hM : ‖fderiv ℝ D.function x‖ ≤ (D.bound : ℝ) := by exact_mod_cast D.derivative_bound x
  simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ D.function x)
    (EuclideanSpace.single D.coordinate 1)).trans
      (mul_le_mul_of_nonneg_right hM (norm_nonneg _))

lemma WallVariation.flux_lipschitz (D : WallVariation) {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    |directionalFlux E D.coordinate D.function - directionalFlux F D.coordinate D.function| ≤
      (D.bound : ℝ) * regionDistance E F := by
  rw [directionalFlux_eq_pairing E hE, directionalFlux_eq_pairing F hF]
  apply abs_weighted_characteristic_sub_le hE hF
    (((D.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).measurable.comp
      measurable_representative)
  intro x
  exact D.directionalDeriv_bound _

end CubicTorus

namespace CubicTorus

lemma positive_flux_nearby (D : WallVariation) {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hδ : 0 < directionalFlux E D.coordinate D.function)
    (hd : regionDistance E F < directionalFlux E D.coordinate D.function /
      (4 * ((D.bound : ℝ) + 1))) :
    directionalFlux E D.coordinate D.function / 2 <
      directionalFlux F D.coordinate D.function := by
  have hh := (le_abs_self _).trans (D.flux_lipschitz hE hF)
  have hd' := (lt_div_iff₀ (by positivity : 0 < 4 * ((D.bound : ℝ) + 1))).1 hd
  have hnon := regionDistance_nonneg E F
  have hM := D.bound.coe_nonneg
  nlinarith

theorem local_comparison_of_positive_flux {V : ℝ} {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E) (D : WallVariation)
    (hδ : 0 < directionalFlux E D.coordinate D.function) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ F : Set Torus,
      MeasurableSet F → perimeter F ≠ ⊤ → regionDistance E F < ε →
      (perimeter E).toReal ≤ (perimeter F).toReal + C * regionDistance E F := by
  let δ := directionalFlux E D.coordinate D.function
  let M : ℝ := D.bound
  let p := (perimeter E).toReal
  refine ⟨δ / (4 * (M + 1)), 4 * M * p / δ, by positivity, by positivity, ?_⟩
  intro F hF hFP hd
  have hδF := positive_flux_nearby D hE hF hδ hd
  let δF := directionalFlux F D.coordinate D.function
  let d := regionDistance E F
  have hd0 : 0 ≤ d := regionDistance_nonneg _ _
  have hM : 0 ≤ M := D.bound.coe_nonneg
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  have hδ0 : 0 < δ := hδ
  have hf0 : 0 < δF := by dsimp only [δF]; linarith
  have hδF' : δ / 2 < δF := hδF
  let t := (torusVolume.real E - torusVolume.real F) / δF
  have ht_abs : |t| ≤ d / δF := by
    dsimp only [t]
    rw [abs_div, abs_of_pos hf0]
    exact div_le_div_of_nonneg_right (abs_realVolume_sub_le_regionDistance hE hF) hf0.le
  have ht2 : |t| ≤ 2 * d / δ := by
    apply ht_abs.trans
    apply (div_le_div_iff₀ hf0 hδ0).2
    nlinarith
  have hd' : d * (4 * (M + 1)) < δ :=
    (lt_div_iff₀ (by positivity : 0 < 4 * (M + 1))).1 hd
  have htM : |t| * M < 1 := by
    have hh := mul_le_mul_of_nonneg_right ht2 hM
    have hh' : (2 * d / δ) * M < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one hδ0]
      nlinarith
    exact hh.trans_lt hh'
  obtain ⟨hG, hGv, hGP⟩ := coordinate_variation D.coordinate D.smooth D.periodic
    D.derivative_bound D.faces htM hF hFP
  have hvol : torusVolume (coordinateRegion D.coordinate D.function t F) = torusVolume E := by
    have hv : torusVolume.real (coordinateRegion D.coordinate D.function t F) =
        torusVolume.real E := by
      rw [hGv]
      change torusVolume.real F + t * δF = torusVolume.real E
      dsimp only [t]
      field_simp
      ring
    have hh := congrArg ENNReal.ofReal hv
    simpa only [Measure.real_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hh
  have hminimal : p ≤ (1 + 2 * |t| * M) * (perimeter F).toReal := by
    apply (ENNReal.toReal_mono hG.2.ne (hmin.2.2 _ hG (hvol.trans hmin.2.1))).trans hGP
  by_cases hl : p ≤ (perimeter F).toReal
  · exact hl.trans (le_add_of_nonneg_right (by positivity))
  · have hl' : (perimeter F).toReal ≤ p := le_of_not_ge hl
    have hscale : 2 * |t| * M ≤ (4 * M / δ) * d := by
      have hh := mul_le_mul_of_nonneg_right ht2 (by positivity : 0 ≤ 2 * M)
      calc
        2 * |t| * M = |t| * (2 * M) := by ring
        _ ≤ (2 * d / δ) * (2 * M) := hh
        _ = (4 * M / δ) * d := by ring
    have h1 := mul_le_mul_of_nonneg_right hscale (ENNReal.toReal_nonneg (a := perimeter F))
    have h2 := mul_le_mul_of_nonneg_left hl' (by positivity : 0 ≤ (4 * M / δ) * d)
    have heq : ((4 * M / δ) * d) * p = (4 * M * p / δ) * d := by ring
    nlinarith

end CubicTorus

namespace CubicTorus

lemma regionDistance_congr_ae {E E' F F' : Set Torus}
    (hE : E =ᵐ[torusVolume] E') (hF : F =ᵐ[torusVolume] F') :
    regionDistance E F = regionDistance E' F' := by
  apply integral_congr_ae
  filter_upwards [hE, hF] with x hx hy
  have hx' : x ∈ E ↔ x ∈ E' := Iff.of_eq hx
  have hy' : x ∈ F ↔ x ∈ F' := Iff.of_eq hy
  by_cases ha : x ∈ E <;> by_cases hb : x ∈ F <;> simp_all [characteristic]

theorem isMinimizerAt_local_quasiminimal {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ F : Set Torus,
      FinitePerimeter F → regionDistance E F < ε →
      (perimeter E).toReal ≤ (perimeter F).toReal + C * regionDistance E F := by
  let E₀ := toMeasurable torusVolume E
  have hE₀ : MeasurableSet E₀ := measurableSet_toMeasurable _ _
  have he : E₀ =ᵐ[torusVolume] E := hmin.1.1.toMeasurable_ae_eq
  have hm₀ : IsMinimizerAt V E₀ := (isMinimizerAt_congr_ae he).2 hmin
  obtain ⟨a, D, hδ⟩ := exists_positive_wallVariation hE₀
    (perimeter_pos_of_volume hV hm₀.1.1 hm₀.2.1)
  let R : Torus → Torus := fun z ↦ z + quotientMap a
  have hRm : Measurable R := (continuous_add_const _).measurable
  obtain ⟨ε, C, heps, hC, hcompare⟩ := local_comparison_of_positive_flux
    (isMinimizerAt_translation hm₀ (quotientMap a)) (hE₀.preimage hRm) D hδ
  refine ⟨ε, C, heps, hC, ?_⟩
  intro F hF hd
  let F₀ := toMeasurable torusVolume F
  have hF₀ : MeasurableSet F₀ := measurableSet_toMeasurable _ _
  have hf : F₀ =ᵐ[torusVolume] F := hF.1.toMeasurable_ae_eq
  have hfp : FinitePerimeter F₀ := (finitePerimeter_congr_ae hf).2 hF
  have hdist : regionDistance (R ⁻¹' E₀) (R ⁻¹' F₀) = regionDistance E F := by
    rw [regionDistance_translation, regionDistance_congr_ae he hf]
  have hh := hcompare (R ⁻¹' F₀) (hF₀.preimage hRm)
    (finitePerimeter_translation hfp (quotientMap a)).2.ne (hdist ▸ hd)
  rw [hdist, perimeter_translation hm₀.1.1, perimeter_translation hfp.1,
    perimeter_congr_ae he, perimeter_congr_ae hf] at hh
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma divergence_add_fields {F G : Cover → Cover} {point : Cover}
    (hF : DifferentiableAt ℝ F point) (hG : DifferentiableAt ℝ G point) :
    divergence (fun y ↦ F y + G y) point = divergence F point + divergence G point := by
  change (∑ i : Fin 3, (fderiv ℝ (F + G) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_add hF hG]
  simp [divergence, Finset.sum_add_distrib]

lemma admissible_convex_cutoff {w : Cover → ℝ}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x)
    (hb : ∀ x, w x ∈ Icc 0 1)
    {F G : Cover → Cover} (hF : AdmissibleField F) (hG : AdmissibleField G) :
    AdmissibleField (fun x ↦ w x • F x + (1 - w x) • G x) := by
  refine ⟨(hw.smul hF.1).add ((contDiff_const.sub hw).smul hG.1), ?_, ?_⟩
  · intro n x
    dsimp only
    rw [hp, hF.2.1, hG.2.1]
  · intro x
    calc
      _ ≤ ‖w x • F x‖ + ‖(1 - w x) • G x‖ := norm_add_le _ _
      _ = w x * ‖F x‖ + (1 - w x) * ‖G x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (hb x).1, abs_of_nonneg (sub_nonneg.mpr (hb x).2)]
      _ ≤ w x * 1 + (1 - w x) * 1 := add_le_add
        (mul_le_mul_of_nonneg_left (hF.2.2 x) (hb x).1)
        (mul_le_mul_of_nonneg_left (hG.2.2 x) (sub_nonneg.mpr (hb x).2))
      _ = 1 := by ring

lemma cutoff_partition_flux_le {E : Set Torus} (hP : perimeter E ≠ ⊤)
    {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x)
    (hb : ∀ x, w x ∈ Icc 0 1)
    {F G : Cover → Cover} (hF : AdmissibleField F) (hG : AdmissibleField G) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      (w x * divergence F x + (1 - w x) * divergence G x)) ≤
    (perimeter E).toReal + 2 *
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, ‖gradient w x‖ := by
  let H : Cover → Cover := fun x ↦ w x • F x + (1 - w x) • G x
  have hH : AdmissibleField H := admissible_convex_cutoff hw hp hb hF hG
  have hd (x) : divergence H x = w x * divergence F x +
      (1 - w x) * divergence G x + ⟪gradient w x, F x - G x⟫ := by
    have hwd : DifferentiableAt ℝ (fun y : Cover ↦ w y • F y) x := by
      convert! ((hw.smul hF.1).differentiable (by simp)) x using 1
    have hgd : DifferentiableAt ℝ (fun y : Cover ↦ (1 - w y) • G y) x := by
      convert! (((show ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Cover ↦ 1 - w y) from contDiff_const.sub hw).smul hG.1).differentiable (by simp)) x using 1
    dsimp only [H]
    rw [divergence_add_fields hwd hgd,
      divergence_smul_function (hw.differentiable (by simp)).differentiableAt
        (hF.1.differentiable (by simp)).differentiableAt,
      divergence_smul_function ((show ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover ↦ 1 - w x)
        from contDiff_const.sub hw).differentiable (by simp)).differentiableAt
        (hG.1.differentiable (by simp)).differentiableAt,
      gradient_const_sub, inner_neg_left, inner_sub_right]
    ring
  have hii : IntegrableOn (fun x ↦ ⟪gradient w x, F x - G x⟫)
      (fundamentalCube ∩ quotientMap ⁻¹' E) :=
    (integrableOn_periodic_continuous
      ((gradient_contDiff hw).continuous.inner (hF.1.continuous.sub hG.1.continuous))
      (fun n x ↦ by simp only [Pi.sub_apply, gradient_periodic hp, hF.2.1, hG.2.1])).mono_set inter_subset_left
  have hign : IntegrableOn (fun x ↦ ‖gradient w x‖)
      (fundamentalCube ∩ quotientMap ⁻¹' E) :=
    (integrableOn_periodic_continuous (gradient_contDiff hw).continuous.norm
      (fun n x ↦ by rw [gradient_periodic hp])).mono_set inter_subset_left
  have hiH := (integrableOn_divergence hH.1).mono_set (s := fundamentalCube ∩ quotientMap ⁻¹' E)
    inter_subset_left
  have heq : (fun x ↦ w x * divergence F x + (1 - w x) * divergence G x) =
      (fun x ↦ divergence H x - ⟪gradient w x, F x - G x⟫) := by
    funext x
    rw [hd]
    ring
  rw [heq, integral_sub hiH hii]
  have hflux := (le_abs_self _).trans (abs_flux_le_perimeter hP hH)
  have herror : -(∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      ⟪gradient w x, F x - G x⟫) ≤
      2 * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, ‖gradient w x‖ := by
    rw [← integral_neg, ← integral_const_mul]
    apply integral_mono hii.neg (hign.const_mul 2)
    intro x
    have hg : ‖F x - G x‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hF.2.2 x, hG.2.2 x])
    calc
      _ ≤ |⟪gradient w x, F x - G x⟫| := neg_le_abs _
      _ ≤ ‖gradient w x‖ * ‖F x - G x‖ := abs_real_inner_le_norm _ _
      _ ≤ _ := by nlinarith [norm_nonneg (gradient w x)]
  linarith

end CubicTorus

namespace CubicTorus

lemma smoothTransition_deriv_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    deriv Real.smoothTransition x = 0 := by
  apply IsLocalMin.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  rw [Real.smoothTransition.zero_of_nonpos hx]
  exact Real.smoothTransition.nonneg y

lemma smoothTransition_deriv_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  apply IsLocalMax.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  rw [Real.smoothTransition.one_of_one_le hx]
  exact Real.smoothTransition.le_one y

lemma smoothTransition_exists_deriv_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ x, ‖deriv Real.smoothTransition x‖ ≤ K := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := (2 : ℕ∞))).continuous_deriv (by norm_num)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) hc.continuousOn
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  by_cases h0 : x < 0
  · rw [smoothTransition_deriv_zero_of_nonpos h0.le, norm_zero]
    exact (zero_le_one : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  by_cases h1 : 1 < x
  · rw [smoothTransition_deriv_zero_of_one_le h1.le, norm_zero]
    exact (zero_le_one : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  exact (hM x ⟨le_of_not_gt h0, le_of_not_gt h1⟩).trans (le_max_left _ _)

def sublevelCutoff (q : Cover → ℝ) (t ε : ℝ) (x : Cover) : ℝ :=
  Real.smoothTransition ((t - q x) / ε)

lemma sublevelCutoff_contDiff {q : Cover → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (t ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (sublevelCutoff q t ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub hq).div_const ε)

lemma sublevelCutoff_periodic {q : Cover → ℝ}
    (hp : ∀ n x, q (x + latticeVector n) = q x) (t ε : ℝ) :
    ∀ n x, sublevelCutoff q t ε (x + latticeVector n) = sublevelCutoff q t ε x := by
  intro n x
  simp only [sublevelCutoff, hp]

lemma sublevelCutoff_mem_Icc (q : Cover → ℝ) (t ε : ℝ) (x : Cover) :
    sublevelCutoff q t ε x ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma fderiv_sublevelCutoff {q : Cover → ℝ} {x : Cover}
    (hq : DifferentiableAt ℝ q x) (t ε : ℝ) :
    fderiv ℝ (sublevelCutoff q t ε) x =
      (deriv Real.smoothTransition ((t - q x) / ε) / ε) • (-fderiv ℝ q x) := by
  have hd : DifferentiableAt ℝ Real.smoothTransition ((t - q x) / ε) :=
    (Real.smoothTransition.contDiff (n := (1 : ℕ∞))).differentiable (by norm_num) _
  have hi := (hq.hasFDerivAt.const_sub t).const_smul ε⁻¹
  have hi' : HasFDerivAt (fun y : Cover ↦ (t - q y) / ε)
      (ε⁻¹ • (-fderiv ℝ q x)) x := by
    convert! hi using 1
    ext y
    simp [div_eq_inv_mul]
  have ho := hd.hasDerivAt.comp_hasFDerivAt x hi'
  calc
    _ = deriv Real.smoothTransition ((t - q x) / ε) • (ε⁻¹ • (-fderiv ℝ q x)) := by
      convert! ho.fderiv using 1
    _ = _ := by simp only [div_eq_mul_inv, smul_smul]

lemma norm_gradient_eq_norm_fderiv (f : Cover → ℝ) (x : Cover) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ Cover).symm.norm_map _

lemma sublevelCutoff_gradient_bound {q : Cover → ℝ}
    (hq : Differentiable ℝ q) {K : ℝ}
    (hK : ∀ u, ‖deriv Real.smoothTransition u‖ ≤ K)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) (x : Cover) :
    ‖gradient (sublevelCutoff q t ε) x‖ ≤ (K / ε) * ‖gradient q x‖ := by
  rw [norm_gradient_eq_norm_fderiv, fderiv_sublevelCutoff (hq x),
    norm_smul, norm_div, norm_neg, Real.norm_of_nonneg hε.le,
    norm_gradient_eq_norm_fderiv]
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hK _) hε.le) (norm_nonneg _)

lemma sublevelCutoff_gradient_zero {q : Cover → ℝ}
    (hq : Differentiable ℝ q) {ε : ℝ} (hε : 0 < ε) (t : ℝ) (x : Cover)
    (hx : q x ≤ t - ε ∨ t ≤ q x) :
    gradient (sublevelCutoff q t ε) x = 0 := by
  apply (InnerProductSpace.toDual ℝ Cover).injective
  simp only [gradient, LinearIsometryEquiv.apply_symm_apply, map_zero]
  rw [fderiv_sublevelCutoff (hq x)]
  have hd : deriv Real.smoothTransition ((t - q x) / ε) = 0 := by
    rcases hx with hx | hx
    · apply smoothTransition_deriv_zero_of_one_le
      apply (le_div_iff₀ hε).2
      linarith
    · exact smoothTransition_deriv_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hε.le)
  rw [hd, zero_div, zero_smul]

end CubicTorus

namespace CubicTorus

lemma perimeter_partition_le_of_flux_bound {E B : Set Torus}
    (hE : NullMeasurableSet E torusVolume) (hB : MeasurableSet B) {C : ℝ}
    (hb : ∀ (F G : Cover → Cover), AdmissibleField F → AdmissibleField G →
      (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∩ B), divergence F x) +
      (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E \ B), divergence G x) ≤ C) :
    FinitePerimeter (E ∩ B) ∧ FinitePerimeter (E \ B) ∧
      (perimeter (E ∩ B)).toReal + (perimeter (E \ B)).toReal ≤ C := by
  have ha : perimeter (E ∩ B) ≤ ENNReal.ofReal C := by
    apply iSup_le
    intro F
    apply iSup_le
    intro hF
    apply ENNReal.ofReal_le_ofReal
    simpa only [divergence_zero, integral_zero, add_zero] using hb F (fun _ ↦ 0) hF admissible_zero
  have hd : perimeter (E \ B) ≤ ENNReal.ofReal C := by
    apply iSup_le
    intro G
    apply iSup_le
    intro hG
    apply ENNReal.ofReal_le_ofReal
    simpa only [divergence_zero, integral_zero, zero_add] using hb (fun _ ↦ 0) G admissible_zero hG
  refine ⟨⟨hE.inter hB.nullMeasurableSet, ha.trans_lt ENNReal.ofReal_lt_top⟩,
    ⟨hE.diff hB.nullMeasurableSet, hd.trans_lt ENNReal.ofReal_lt_top⟩, ?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨F, hF, hf⟩ := exists_admissible_flux_gt (E ∩ B) (half_pos hε)
  obtain ⟨G, hG, hg⟩ := exists_admissible_flux_gt (E \ B) (half_pos hε)
  linarith [hb F G hF hG]

lemma partition_flux_tendsto {E B : Set Torus} (hB : MeasurableSet B)
    {w : ℕ → Cover → ℝ} (hw : ∀ n, Continuous (w n))
    (hb : ∀ n x, w n x ∈ Icc (0 : ℝ) 1)
    (ht : ∀ x, Tendsto (fun n ↦ w n x) atTop (𝓝 (characteristic B (quotientMap x))))
    {F G : Cover → Cover} (hF : AdmissibleField F) (hG : AdmissibleField G) :
    Tendsto (fun n ↦ ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      w n x * divergence F x + (1 - w n x) * divergence G x) atTop
      (𝓝 ((∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∩ B), divergence F x) +
        ∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E \ B), divergence G x)) := by
  have hiF := (integrableOn_divergence hF.1).mono_set
    (s := fundamentalCube ∩ quotientMap ⁻¹' E) inter_subset_left
  have hiG := (integrableOn_divergence hG.1).mono_set
    (s := fundamentalCube ∩ quotientMap ⁻¹' E) inter_subset_left
  have hh := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E))
    (bound := fun x ↦ |divergence F x| + |divergence G x|)
    (F := fun n x ↦ w n x * divergence F x + (1 - w n x) * divergence G x)
    (f := fun x ↦ characteristic B (quotientMap x) * divergence F x +
      (1 - characteristic B (quotientMap x)) * divergence G x)
    (fun n ↦ (((hw n).mul (continuous_divergence hF.1)).add
      ((continuous_const.sub (hw n)).mul (continuous_divergence hG.1))).aestronglyMeasurable)
    (hiF.abs.add hiG.abs) (fun n ↦ Eventually.of_forall fun x ↦ ?_)
    (Eventually.of_forall fun x ↦ (ht x |>.mul tendsto_const_nhds).add
      ((tendsto_const_nhds.sub (ht x)).mul tendsto_const_nhds))
  · have heq : (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        characteristic B (quotientMap x) * divergence F x +
        (1 - characteristic B (quotientMap x)) * divergence G x) =
        (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∩ B), divergence F x) +
        ∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E \ B), divergence G x := by
      have hp (x : Cover) : characteristic B (quotientMap x) * divergence F x +
          (1 - characteristic B (quotientMap x)) * divergence G x =
          (quotientMap ⁻¹' B).indicator (divergence F) x +
          (quotientMap ⁻¹' Bᶜ).indicator (divergence G) x := by
        classical
        by_cases hx : quotientMap x ∈ B <;> simp [characteristic, hx]
      simp_rw [hp]
      rw [integral_add (hiF.indicator (measurable_quotientMap hB))
        (hiG.indicator (measurable_quotientMap hB.compl)),
        integral_indicator (measurable_quotientMap hB),
        integral_indicator (measurable_quotientMap hB.compl),
        Measure.restrict_restrict (measurable_quotientMap hB),
        Measure.restrict_restrict (measurable_quotientMap hB.compl)]
      rw [show (quotientMap ⁻¹' B) ∩ (fundamentalCube ∩ quotientMap ⁻¹' E) =
          fundamentalCube ∩ quotientMap ⁻¹' (E ∩ B) by ext x; simp only [mem_inter_iff, mem_preimage]; tauto,
        show (quotientMap ⁻¹' Bᶜ) ∩ (fundamentalCube ∩ quotientMap ⁻¹' E) =
          fundamentalCube ∩ quotientMap ⁻¹' (E \ B) by ext x; simp only [mem_inter_iff, mem_preimage, mem_compl_iff, Set.mem_sdiff]; tauto]
    exact heq ▸ hh
  · rw [Real.norm_eq_abs]
    calc
      _ ≤ |w n x * divergence F x| + |(1 - w n x) * divergence G x| := abs_add_le _ _
      _ = w n x * |divergence F x| + (1 - w n x) * |divergence G x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hb n x).1,
          abs_of_nonneg (sub_nonneg.mpr (hb n x).2)]
      _ ≤ _ := add_le_add (mul_le_of_le_one_left (abs_nonneg _) (hb n x).2)
        (mul_le_of_le_one_left (abs_nonneg _) (by linarith [(hb n x).1]))

end CubicTorus

namespace CubicTorus

def sublevelRegion (q : Cover → ℝ) (t : ℝ) : Set Torus :=
  {z | q (representative z) < t}

def sublevelVolume (E : Set Torus) (q : Cover → ℝ) (t : ℝ) : ℝ :=
  torusVolume.real (E ∩ sublevelRegion q t)

lemma measurableSet_sublevelRegion {q : Cover → ℝ} (hq : Measurable q) (t : ℝ) :
    MeasurableSet (sublevelRegion q t) :=
  measurableSet_lt (hq.comp measurable_representative) measurable_const

lemma mem_sublevelRegion_quotient {q : Cover → ℝ}
    (hp : ∀ n x, q (x + latticeVector n) = q x) (t : ℝ) (x : Cover) :
    quotientMap x ∈ sublevelRegion q t ↔ q x < t := by
  simp only [sublevelRegion, mem_ofPred_eq, periodic_representative hp]

lemma sublevelRegion_mono (q : Cover → ℝ) : Monotone (sublevelRegion q) := by
  intro s t hst z hz
  exact hz.trans_le hst

lemma sublevelVolume_mono (E : Set Torus) (q : Cover → ℝ) :
    Monotone (sublevelVolume E q) := by
  intro s t hst
  exact measureReal_mono (inter_subset_inter_right E (sublevelRegion_mono q hst))

lemma sublevelCutoff_gradient_integral_le {E : Set Torus} (hE : MeasurableSet E)
    {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hp : ∀ n x, q (x + latticeVector n) = q x) {K M t ε : ℝ}
    (hK : ∀ u, ‖deriv Real.smoothTransition u‖ ≤ K)
    (hgrad : ∀ x, q x < t → ‖gradient q x‖ ≤ M) (hε : 0 < ε) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      ‖gradient (sublevelCutoff q t ε) x‖) ≤
      K * M * ((sublevelVolume E q t - sublevelVolume E q (t - ε)) / ε) := by
  let A := sublevelRegion q t \ sublevelRegion q (t - ε)
  have hmA : MeasurableSet A := (measurableSet_sublevelRegion hq.continuous.measurable t).diff
    (measurableSet_sublevelRegion hq.continuous.measurable (t - ε))
  have hqdiff := hq.differentiable (by simp)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hb (x : Cover) : ‖gradient (sublevelCutoff q t ε) x‖ ≤
      (quotientMap ⁻¹' A).indicator (fun _ ↦ K * M / ε) x := by
    classical
    by_cases hx : x ∈ quotientMap ⁻¹' A
    · rw [Set.indicator_of_mem hx]
      have hxt : q x < t := (mem_sublevelRegion_quotient hp t x).1 hx.1
      calc
        _ ≤ (K / ε) * ‖gradient q x‖ := sublevelCutoff_gradient_bound hqdiff hK hε t x
        _ ≤ (K / ε) * M := mul_le_mul_of_nonneg_left (hgrad x hxt) (div_nonneg hK0 hε.le)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hx]
      rw [sublevelCutoff_gradient_zero hqdiff hε t x, norm_zero]
      have hn : ¬(q x < t ∧ ¬q x < t - ε) := by
        simpa only [A, mem_preimage, Set.mem_sdiff, mem_sublevelRegion_quotient hp] using hx
      rcases le_or_gt t (q x) with h | h
      · exact Or.inr h
      · exact Or.inl (le_of_lt (not_not.mp (fun hh ↦ hn ⟨h, hh⟩)))
  have hig : IntegrableOn (fun x ↦ ‖gradient (sublevelCutoff q t ε) x‖)
      (fundamentalCube ∩ quotientMap ⁻¹' E) :=
    (integrableOn_periodic_continuous (gradient_contDiff (sublevelCutoff_contDiff hq t ε)).continuous.norm
      (fun n x ↦ by rw [gradient_periodic (sublevelCutoff_periodic hp t ε)])).mono_set inter_subset_left
  have hic : IntegrableOn (fun _ : Cover ↦ K * M / ε)
      (fundamentalCube ∩ quotientMap ⁻¹' E) :=
    (integrableOn_periodic_continuous continuous_const (fun _ _ ↦ rfl)).mono_set inter_subset_left
  have hh := integral_mono hig (hic.indicator (measurable_quotientMap hmA)) hb
  rw [integral_indicator (measurable_quotientMap hmA),
    Measure.restrict_restrict (measurable_quotientMap hmA)] at hh
  have heq : quotientMap ⁻¹' A ∩ (fundamentalCube ∩ quotientMap ⁻¹' E) =
      fundamentalCube ∩ quotientMap ⁻¹' (E ∩ A) := by ext x; simp only [mem_inter_iff, mem_preimage]; tauto
  rw [heq, integral_const] at hh
  simp only [Measure.real_def, Measure.restrict_apply_univ, smul_eq_mul] at hh
  change _ ≤ volume.real (fundamentalCube ∩ quotientMap ⁻¹' (E ∩ A)) * (K * M / ε) at hh
  rw [← realVolume_lift (hE.inter hmA)] at hh
  have hsets : E ∩ A = (E ∩ sublevelRegion q t) \ (E ∩ sublevelRegion q (t - ε)) := by
    ext z; simp only [A, mem_inter_iff, Set.mem_sdiff]; tauto
  have hsubset : E ∩ sublevelRegion q (t - ε) ⊆ E ∩ sublevelRegion q t :=
    inter_subset_inter_right E (sublevelRegion_mono q (by linarith))
  rw [hsets, measureReal_sdiff hsubset
    (hE.inter (measurableSet_sublevelRegion hq.continuous.measurable (t - ε)))] at hh
  change _ ≤ (sublevelVolume E q t - sublevelVolume E q (t - ε)) * (K * M / ε) at hh
  convert hh using 1
  ring

end CubicTorus

namespace CubicTorus

lemma sublevelCutoff_tendsto {q : Cover → ℝ}
    (hp : ∀ n x, q (x + latticeVector n) = q x)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (t : ℝ) (x : Cover) :
    Tendsto (fun n ↦ sublevelCutoff q t (ε n) x) atTop
      (𝓝 (characteristic (sublevelRegion q t) (quotientMap x))) := by
  classical
  by_cases hx : q x < t
  · have hmem := (mem_sublevelRegion_quotient hp t x).2 hx
    have he : ∀ᶠ n in atTop, sublevelCutoff q t (ε n) x = 1 := by
      filter_upwards [hεlim.eventually (gt_mem_nhds (sub_pos.mpr hx))] with n hn
      apply Real.smoothTransition.one_of_one_le
      apply (le_div_iff₀ (hε n)).2
      linarith
    rw [characteristic, indicator_of_mem hmem]
    exact tendsto_const_nhds.congr' (he.mono fun _ hn ↦ hn.symm)
  · have hmem : quotientMap x ∉ sublevelRegion q t :=
      fun h ↦ hx ((mem_sublevelRegion_quotient hp t x).1 h)
    rw [characteristic, indicator_of_notMem hmem]
    have he (n) : sublevelCutoff q t (ε n) x = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hx)) (hε n).le
    simpa only [he] using (tendsto_const_nhds (x := (0 : ℝ)) :
      Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))

lemma tendsto_backward_quotient_of_hasDerivAt {m : ℝ → ℝ} {d t : ℝ}
    (hm : HasDerivAt m d t) {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ (m t - m (t - ε n)) / ε n) atTop (𝓝 d) := by
  have hlim : Tendsto (fun n ↦ t - ε n) atTop (𝓝[≠] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using tendsto_const_nhds.sub hεlim, Eventually.of_forall fun n ↦ ?_⟩
    simp only [mem_compl_iff, mem_singleton_iff]
    linarith [hε n]
  have hs := hm.tendsto_slope.comp hlim
  convert hs using 1
  ext n
  rw [Function.comp_apply, slope_def_field, show t - ε n - t = -(ε n) by ring, div_neg]
  ring

theorem perimeter_sublevel_partition {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) {q : Cover → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hp : ∀ n x, q (x + latticeVector n) = q x)
    {K M t d : ℝ} (hK : ∀ u, ‖deriv Real.smoothTransition u‖ ≤ K)
    (hgrad : ∀ x, q x < t → ‖gradient q x‖ ≤ M)
    (hd : HasDerivAt (sublevelVolume E q) d t) :
    FinitePerimeter (E ∩ sublevelRegion q t) ∧
    FinitePerimeter (E \ sublevelRegion q t) ∧
    (perimeter (E ∩ sublevelRegion q t)).toReal +
      (perimeter (E \ sublevelRegion q t)).toReal ≤ (perimeter E).toReal + 2 * K * M * d := by
  let ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n ↦ by dsimp [ε]; positivity
  have helim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb := measurableSet_sublevelRegion hq.continuous.measurable t
  apply perimeter_partition_le_of_flux_bound hE.nullMeasurableSet hb
  intro F G hF hG
  have hlim := partition_flux_tendsto (E := E) hb
    (fun n ↦ (sublevelCutoff_contDiff hq t (ε n)).continuous)
    (fun n x ↦ sublevelCutoff_mem_Icc q t (ε n) x)
    (sublevelCutoff_tendsto hp hε helim t) hF hG
  have hh := tendsto_backward_quotient_of_hasDerivAt hd hε helim
  have hrlim : Tendsto (fun n ↦ (perimeter E).toReal + 2 * K * M *
      ((sublevelVolume E q t - sublevelVolume E q (t - ε n)) / ε n)) atTop
        (𝓝 ((perimeter E).toReal + 2 * K * M * d)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hh)
  apply le_of_tendsto_of_tendsto' hlim hrlim
  intro n
  calc
    _ ≤ (perimeter E).toReal + 2 * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        ‖gradient (sublevelCutoff q t (ε n)) x‖ :=
      cutoff_partition_flux_le hP (sublevelCutoff_contDiff hq t (ε n))
        (sublevelCutoff_periodic hp t (ε n)) (sublevelCutoff_mem_Icc q t (ε n)) hF hG
    _ ≤ (perimeter E).toReal + 2 * (K * M *
        ((sublevelVolume E q t - sublevelVolume E q (t - ε n)) / ε n)) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
        (sublevelCutoff_gradient_integral_le hE hq hp hK hgrad (hε n)) (show (0 : ℝ) ≤ 2 by norm_num))
    _ = _ := by ring

end CubicTorus

namespace CubicTorus

lemma regionDistance_sdiff {E B : Set Torus} (hE : NullMeasurableSet E torusVolume)
    (hB : NullMeasurableSet B torusVolume) :
    regionDistance E (E \ B) = torusVolume.real (E ∩ B) := by
  have heq (x : Torus) : ‖characteristic E x - characteristic (E \ B) x‖ =
      characteristic (E ∩ B) x := by
    classical
    by_cases he : x ∈ E <;> by_cases hb : x ∈ B <;> simp [characteristic, he, hb]
  unfold regionDistance
  simp_rw [heq]
  exact integral_characteristic (hE.inter hB)

theorem isMinimizerAt_sublevel_comparison {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (q : Cover → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) q → (∀ n x, q (x + latticeVector n) = q x) →
      ∀ K M t d : ℝ, (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      (∀ x, q x < t → ‖gradient q x‖ ≤ M) →
      HasDerivAt (sublevelVolume E q) d t → sublevelVolume E q t < η →
      (perimeter (E ∩ sublevelRegion q t)).toReal ≤
        C * sublevelVolume E q t + 2 * K * M * d := by
  obtain ⟨η, C, hη, hC, hc⟩ := isMinimizerAt_local_quasiminimal hV hmin
  refine ⟨η, C, hη, hC, ?_⟩
  intro q hq hp K M t d hK hgrad hd ht
  obtain ⟨_, hdiff, hpart⟩ := perimeter_sublevel_partition hE hmin.1.2.ne hq hp hK hgrad hd
  have hdist : regionDistance E (E \ sublevelRegion q t) = sublevelVolume E q t :=
    regionDistance_sdiff hmin.1.1 (measurableSet_sublevelRegion hq.continuous.measurable t).nullMeasurableSet
  have hcomp := hc (E \ sublevelRegion q t) hdiff (by rwa [hdist])
  rw [hdist] at hcomp
  linarith

theorem isMinimizerAt_sublevel_density_inequality {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ η C K : ℝ, 0 < η ∧ 0 ≤ C ∧ 0 < K ∧
      ∀ (q : Cover → ℝ), ContDiff ℝ (⊤ : ℕ∞) q →
      (∀ n x, q (x + latticeVector n) = q x) →
      ∀ᵐ t : ℝ, ∀ M : ℝ, (∀ x, q x < t → ‖gradient q x‖ ≤ M) →
        sublevelVolume E q t < η → sublevelVolume E q t ≤ 1/2 →
        sublevelVolume E q t ^ (2 / 3 : ℝ) ≤
          12 * C * sublevelVolume E q t + 24 * K * M * deriv (sublevelVolume E q) t := by
  obtain ⟨η, C, hη, hC, hc⟩ := isMinimizerAt_sublevel_comparison hV hE hmin
  obtain ⟨K, hKpos, hK⟩ := smoothTransition_exists_deriv_bound
  refine ⟨η, C, K, hη, hC, hKpos, ?_⟩
  intro q hq hp
  filter_upwards [(sublevelVolume_mono E q).ae_differentiableAt] with t ht
  intro M hgrad hm hhalf
  have hcomp := hc q hq hp K M t (deriv (sublevelVolume E q) t) hK hgrad ht.hasDerivAt hm
  obtain ⟨hcut, _, _⟩ := perimeter_sublevel_partition hE hmin.1.2.ne hq hp hK hgrad ht.hasDerivAt
  have hiso := bv_isoperimetric_small hcut hhalf
  change sublevelVolume E q t ^ (2 / 3 : ℝ) ≤ _ at hiso
  linarith

end CubicTorus

end
end

end

end OAI
