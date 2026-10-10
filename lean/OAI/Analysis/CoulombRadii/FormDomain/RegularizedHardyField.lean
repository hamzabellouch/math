import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.Space

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open ContinuousLinearMap
open scoped Convolution

noncomputable def regularizedHardyField {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (ε : ℝ) (b : Fin 3) (x : Configuration n) : ℝ :=
  R.coord b x / (blockRadiusSq i R x + ε)

lemma contDiff_regularizedHardyField {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (b : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedHardyField i R ε b) := by
  exact (R.smooth b).div ((contDiff_blockRadiusSq i R).add contDiff_const)
    (fun x => ne_of_gt (add_pos_of_nonneg_of_pos (blockRadiusSq_nonneg i R x) hε))

lemma fderiv_regularizedHardyField {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (b : Fin 3) (x : Configuration n) :
    fderiv ℝ (regularizedHardyField i R ε b) x (EuclideanSpace.single (i,b) 1) =
      (blockRadiusSq i R x + ε)⁻¹ -
        2 * (R.coord b x)^2 / (blockRadiusSq i R x + ε)^2 := by
  have hd := ((contDiff_blockRadiusSq i R).differentiable (by simp) x).hasFDerivAt.add_const ε
  have hne : blockRadiusSq i R x + ε ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (blockRadiusSq_nonneg i R x) hε)
  have hi := (hasFDerivAt_inv hne).comp x hd
  have hn := ((R.smooth b).differentiable (by simp) x).hasFDerivAt
  have hm := hn.fun_mul hi
  change fderiv ℝ (fun y : Configuration n =>
    R.coord b y * (blockRadiusSq i R y + ε)⁻¹) x _ = _
  simp only [Function.comp_apply] at hm
  rw [hm.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    ContinuousLinearMap.toSpanSingleton_apply]
  rw [fderiv_blockRadiusSq, R.directional]
  simp only [ite_true, mul_one]
  ring

lemma regularizedHardyField_sq_sum {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (ε : ℝ) (x : Configuration n) :
    (∑ b : Fin 3, (regularizedHardyField i R ε b x)^2) =
      blockRadiusSq i R x / (blockRadiusSq i R x + ε)^2 := by
  simp only [regularizedHardyField, div_pow, ← Finset.sum_div]
  rfl

lemma regularizedHardyField_divergence {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (x : Configuration n) :
    (∑ b : Fin 3, fderiv ℝ (regularizedHardyField i R ε b) x
      (EuclideanSpace.single (i,b) 1)) =
      (blockRadiusSq i R x + 3 * ε) / (blockRadiusSq i R x + ε)^2 := by
  simp_rw [fderiv_regularizedHardyField i R hε]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_div, ← Finset.mul_sum]
  change 3 * (blockRadiusSq i R x + ε)⁻¹ -
    2 * blockRadiusSq i R x / (blockRadiusSq i R x + ε)^2 = _
  have hne : blockRadiusSq i R x + ε ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (blockRadiusSq_nonneg i R x) hε)
  field_simp
  ring

lemma regularizedHardyField_weight {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (x : Configuration n) :
    (blockRadiusSq i R x + ε)⁻¹ ≤
      2 * (∑ b : Fin 3, fderiv ℝ (regularizedHardyField i R ε b) x
        (EuclideanSpace.single (i,b) 1)) -
      ∑ b : Fin 3, (regularizedHardyField i R ε b x)^2 := by
  rw [regularizedHardyField_divergence i R hε, regularizedHardyField_sq_sum]
  have hpos : 0 < blockRadiusSq i R x + ε :=
    add_pos_of_nonneg_of_pos (blockRadiusSq_nonneg i R x) hε
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hpos)).mp
  field_simp
  nlinarith

lemma integrable_smooth_mul_compact_deriv {n : ℕ} (u F : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u)
    (hF : Continuous F) (v : Configuration n) :
    Integrable (fun x => F x * fderiv ℝ u x v) := by
  exact (hF.mul ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport (huC.fderiv_apply ℝ v).mul_left

lemma integrable_smooth_deriv_mul_compact {n : ℕ} (u F : Configuration n → ℝ)
    (hu : Continuous u) (huC : HasCompactSupport u)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (v : Configuration n) :
    Integrable (fun x => fderiv ℝ F x v * u x) := by
  exact (((hF.continuous_fderiv (by simp)).clm_apply continuous_const).mul hu).integrable_of_hasCompactSupport huC.mul_left

lemma integral_compact_ibp {n : ℕ} (u F : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (v : Configuration n) :
    (∫ x, F x * fderiv ℝ u x v) = -(∫ x, fderiv ℝ F x v * u x) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact integrable_smooth_deriv_mul_compact u F hu.continuous huC hF v
  · exact integrable_smooth_mul_compact_deriv u F hu huC hF.continuous v
  · exact (hF.continuous.mul hu.continuous).integrable_of_hasCompactSupport huC.mul_left
  · intro x _; exact hF.differentiable (by simp) x
  · intro x _; exact hu.differentiable (by simp) x

lemma smooth_square_fderiv {n : ℕ} (u : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x v : Configuration n) :
    fderiv ℝ (fun y => (u y)^2) x v = 2 * u x * fderiv ℝ u x v := by
  rw [((hu.differentiable (by simp) x).hasFDerivAt.pow 2).fderiv]
  simp only [smul_apply, smul_eq_mul, Nat.reduceSub, pow_one, nsmul_eq_mul,
    Nat.cast_ofNat]

lemma integral_compact_ibp_deriv_form {n : ℕ} (u F : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (v : Configuration n) :
    (∫ x, fderiv ℝ F x v * u x + F x * fderiv ℝ u x v) = 0 := by
  rw [integral_add
    (integrable_smooth_deriv_mul_compact u F hu.continuous huC hF v)
    (integrable_smooth_mul_compact_deriv u F hu huC hF.continuous v),
    integral_compact_ibp u F hu huC hF v]
  exact add_neg_cancel _

lemma integral_compact_ibp_square {n : ℕ} (u F : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (v : Configuration n) :
    (∫ x, fderiv ℝ F x v * (u x)^2 + 2 * F x * u x * fderiv ℝ u x v) = 0 := by
  have hu2 : ContDiff ℝ (⊤ : ℕ∞) (fun x => (u x)^2) := hu.pow 2
  have hu2C : HasCompactSupport (fun x => (u x)^2) := huC.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have heq := integral_compact_ibp_deriv_form (fun x => (u x)^2) F hu2 hu2C hF v
  calc
    _ = (∫ x, fderiv ℝ F x v * (u x)^2 + F x * fderiv ℝ (fun y => (u y)^2) x v) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [smooth_square_fderiv u hu]
      ring
    _ = 0 := heq

lemma hardy_pointwise_algebra {ι : Type*} [Fintype ι]
    (u w : ℝ) (F D G : ι → ℝ)
    (hw : w ≤ 2 * ∑ b, D b - ∑ b, (F b)^2) :
    w * u^2 ≤ 4 * ∑ b, (G b)^2 +
      2 * ∑ b, (D b * u^2 + 2 * F b * u * G b) := by
  have hs : 0 ≤ ∑ b, (2 * G b + F b * u)^2 :=
    Finset.sum_nonneg (fun b _ => sq_nonneg _)
  have hid : (∑ b, (2 * G b + F b * u)^2) =
      4 * ∑ b, (G b)^2 + 4 * u * ∑ b, F b * G b +
        u^2 * ∑ b, (F b)^2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hid2 : (∑ b, (D b * u^2 + 2 * F b * u * G b)) =
      u^2 * ∑ b, D b + 2 * u * ∑ b, F b * G b := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hp := mul_nonneg (sub_nonneg.mpr hw) (sq_nonneg u)
  rw [hid] at hs
  rw [hid2]
  nlinarith

lemma regularizedHardy_pointwise {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (u : Configuration n → ℝ) (x : Configuration n) :
    (blockRadiusSq i R x + ε)⁻¹ * (u x)^2 ≤
      4 * ∑ b : Fin 3, (fderiv ℝ u x (EuclideanSpace.single (i,b) 1))^2 +
      2 * ∑ b : Fin 3,
        (fderiv ℝ (regularizedHardyField i R ε b) x (EuclideanSpace.single (i,b) 1) *
          (u x)^2 + 2 * regularizedHardyField i R ε b x * u x *
          fderiv ℝ u x (EuclideanSpace.single (i,b) 1)) :=
  hardy_pointwise_algebra (u x) (blockRadiusSq i R x + ε)⁻¹
    (fun b => regularizedHardyField i R ε b x)
    (fun b => fderiv ℝ (regularizedHardyField i R ε b) x (EuclideanSpace.single (i,b) 1))
    (fun b => fderiv ℝ u x (EuclideanSpace.single (i,b) 1))
    (regularizedHardyField_weight i R hε x)

lemma integrable_compact_deriv_sq {n : ℕ} (u : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u) (v : Configuration n) :
    Integrable (fun x => (fderiv ℝ u x v)^2) := by
  have hc : Continuous (fun x => fderiv ℝ u x v) :=
    (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hs : HasCompactSupport (fun x => fderiv ℝ u x v) := huC.fderiv_apply ℝ v
  have hs2 : HasCompactSupport (fun x => (fderiv ℝ u x v)^2) :=
    hs.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  exact (hc.pow 2).integrable_of_hasCompactSupport hs2

lemma integrable_compact_ibp_square {n : ℕ} (u F : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (v : Configuration n) :
    Integrable (fun x => fderiv ℝ F x v * (u x)^2 +
      2 * F x * u x * fderiv ℝ u x v) := by
  have hu2C : HasCompactSupport (fun x => (u x)^2) :=
    huC.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have h1 := integrable_smooth_deriv_mul_compact (fun x => (u x)^2)
    F (hu.pow 2).continuous hu2C hF v
  have h2 := integrable_smooth_mul_compact_deriv u (fun x => 2 * F x * u x)
    hu huC ((continuous_const.mul hF.continuous).mul hu.continuous) v
  exact h1.add h2

lemma integral_hardy_algebra {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (W : X → ℝ) (G D : ι → X → ℝ)
    (hW : Integrable W μ) (hG : ∀ b, Integrable (G b) μ)
    (hD : ∀ b, Integrable (D b) μ) (hD0 : ∀ b, (∫ x, D b x ∂μ) = 0)
    (hle : ∀ x, W x ≤ 4 * ∑ b, G b x + 2 * ∑ b, D b x) :
    (∫ x, W x ∂μ) ≤ 4 * ∑ b, ∫ x, G b x ∂μ := by
  have hGs : Integrable (fun x => ∑ b, G b x) μ :=
    integrable_finsetSum _ (fun b _ => hG b)
  have hDs : Integrable (fun x => ∑ b, D b x) μ :=
    integrable_finsetSum _ (fun b _ => hD b)
  have h := integral_mono hW ((hGs.const_mul 4).add (hDs.const_mul 2)) hle
  simp only [Pi.add_apply] at h
  rw [integral_add (hGs.const_mul 4) (hDs.const_mul 2),
    integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun b _ => hG b),
    integral_finsetSum _ (fun b _ => hD b)] at h
  simpa only [hD0, Finset.sum_const_zero, mul_zero, add_zero] using h

lemma integrable_compact_regularized_weight {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (u : Configuration n → ℝ)
    (hu : Continuous u) (huC : HasCompactSupport u) :
    Integrable (fun x => (blockRadiusSq i R x + ε)⁻¹ * (u x)^2) := by
  have hwcont : Continuous (fun x => (blockRadiusSq i R x + ε)⁻¹) :=
    ((contDiff_blockRadiusSq i R).continuous.add continuous_const).inv₀
      (fun x => ne_of_gt (add_pos_of_nonneg_of_pos (blockRadiusSq_nonneg i R x) hε))
  have hs : HasCompactSupport (fun x => (u x)^2) :=
    huC.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  exact (hwcont.mul (hu.pow 2)).integrable_of_hasCompactSupport hs.mul_left

lemma smooth_compact_regularized_hardy {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    {ε : ℝ} (hε : 0 < ε) (u : Configuration n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u) :
    (∫ x, (blockRadiusSq i R x + ε)⁻¹ * (u x)^2) ≤
      4 * ∑ b : Fin 3, ∫ x, (fderiv ℝ u x (EuclideanSpace.single (i,b) 1))^2 := by
  let G : Fin 3 → Configuration n → ℝ := fun b x =>
    (fderiv ℝ u x (EuclideanSpace.single (i,b) 1))^2
  let D : Fin 3 → Configuration n → ℝ := fun b x =>
    fderiv ℝ (regularizedHardyField i R ε b) x (EuclideanSpace.single (i,b) 1) *
      (u x)^2 + 2 * regularizedHardyField i R ε b x * u x *
      fderiv ℝ u x (EuclideanSpace.single (i,b) 1)
  have hG : ∀ b, Integrable (G b) := fun b => integrable_compact_deriv_sq u hu huC
    (EuclideanSpace.single (i,b) 1)
  have hD : ∀ b, Integrable (D b) := fun b => integrable_compact_ibp_square u
    (regularizedHardyField i R ε b) hu huC (contDiff_regularizedHardyField i R hε b)
    (EuclideanSpace.single (i,b) 1)
  have hD0 : ∀ b, (∫ x, D b x) = 0 := fun b => integral_compact_ibp_square u
    (regularizedHardyField i R ε b) hu huC (contDiff_regularizedHardyField i R hε b)
    (EuclideanSpace.single (i,b) 1)
  exact integral_hardy_algebra volume
    (fun x => (blockRadiusSq i R x + ε)⁻¹ * (u x)^2) G D
    (integrable_compact_regularized_weight i R hε u hu.continuous huC)
    hG hD hD0 (regularizedHardy_pointwise i R hε u)

lemma nonneg_fatou_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (F : ℕ → X → ℝ) (C : ℝ)
    (hF : ∀ n, Integrable (F n) μ) (hn : ∀ n x, 0 ≤ F n x)
    (hf : ∀ x, 0 ≤ f x)
    (ht : ∀ x, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f x)))
    (hC : ∀ n, (∫ x, F n x ∂μ) ≤ C) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ C := by
  have hfm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n => (hF n).aestronglyMeasurable)
      (Filter.Eventually.of_forall ht)
  have hb : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (F n x)) Filter.atTop ∂μ := by
        apply lintegral_congr
        intro x
        exact ((ENNReal.continuous_ofReal.tendsto _).comp (ht x)).liminf_eq.symm
      _ ≤ Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) Filter.atTop :=
        lintegral_liminf_le' (fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal C := by
        apply Filter.liminf_le_of_frequently_le (hu_le := Filter.isBoundedUnder_of ⟨0, fun _ => bot_le⟩)
        apply Filter.Eventually.frequently
        apply Filter.Eventually.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (Filter.Eventually.of_forall (hn n))]
        exact ENNReal.ofReal_le_ofReal (hC n)
  have hfinite : Integrable f μ := ⟨hfm,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf)).2
      (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)⟩
  refine ⟨hfinite, ?_⟩
  have hCn : 0 ≤ C := (integral_nonneg (hn 0)).trans (hC 0)
  rw [← ofReal_integral_eq_lintegral_ofReal hfinite (Filter.Eventually.of_forall hf)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hCn).1 hb

lemma smooth_compact_hardy {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (u : Configuration n → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huC : HasCompactSupport u) :
    Integrable (fun x => (blockRadiusSq i R x)⁻¹ * (u x)^2) ∧
    (∫ x, (blockRadiusSq i R x)⁻¹ * (u x)^2) ≤
      4 * ∑ b : Fin 3, ∫ x, (fderiv ℝ u x (EuclideanSpace.single (i,b) 1))^2 := by
  let eps : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have heps : ∀ k, 0 < eps k := fun k => one_div_pos.mpr (by positivity)
  let A := {x : Configuration n | blockRadiusSq i R x ≠ 0}
  have hA : MeasurableSet A :=
    ((contDiff_blockRadiusSq i R).continuous.measurable (measurableSet_singleton 0)).compl
  let F : ℕ → Configuration n → ℝ := fun k =>
    A.indicator (fun x => (blockRadiusSq i R x + eps k)⁻¹ * (u x)^2)
  have hF : ∀ k, Integrable (F k) := fun k =>
    (integrable_compact_regularized_weight i R (heps k) u hu.continuous huC).indicator hA
  have hFn : ∀ k x, 0 ≤ F k x := by
    intro k x
    exact Set.indicator_nonneg (fun x _ =>
      mul_nonneg (inv_nonneg.mpr (add_nonneg (blockRadiusSq_nonneg i R x) (heps k).le))
        (sq_nonneg (u x))) x
  have ht : ∀ x, Filter.Tendsto (fun k => F k x) Filter.atTop
      (nhds ((blockRadiusSq i R x)⁻¹ * (u x)^2)) := by
    intro x
    by_cases hx : x ∈ A
    · simp only [F, Set.indicator_of_mem hx]
      have ht0 : Filter.Tendsto eps Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have htt := (Filter.Tendsto.const_add (blockRadiusSq i R x) ht0).inv₀ (by simpa only [A, Set.mem_ofPred_eq, add_zero] using hx)
      simpa only [add_zero] using htt.mul_const ((u x)^2)
    · have hx0 : blockRadiusSq i R x = 0 := by simpa only [A, Set.mem_ofPred_eq, not_not] using hx
      simp only [F, Set.indicator_of_notMem hx, hx0, inv_zero, zero_mul]
      exact tendsto_const_nhds
  apply nonneg_fatou_integrable volume _ F _ hF hFn
    (fun x => mul_nonneg (inv_nonneg.mpr (blockRadiusSq_nonneg i R x)) (sq_nonneg (u x))) ht
  intro k
  calc
    (∫ x, F k x) ≤ ∫ x, (blockRadiusSq i R x + eps k)⁻¹ * (u x)^2 := by
      apply integral_mono (hF k)
        (integrable_compact_regularized_weight i R (heps k) u hu.continuous huC)
      intro x
      exact Set.indicator_le_self' (fun x _ =>
        mul_nonneg (inv_nonneg.mpr (add_nonneg (blockRadiusSq_nonneg i R x) (heps k).le))
          (sq_nonneg (u x))) x
    _ ≤ _ := smooth_compact_regularized_hardy i R (heps k) u hu huC

lemma convolution_sq_le {n : ℕ} (κ u : Configuration n → ℝ)
    (hκ : Continuous κ) (hκC : HasCompactSupport κ)
    (hκn : ∀ x, 0 ≤ κ x) (hκI : (∫ x, κ x) = 1)
    (hu : LocallyIntegrable u) (hu2 : Integrable (fun x => (u x)^2))
    (x : Configuration n) :
    ((κ ⋆ u) x)^2 ≤ (κ ⋆ (fun x => (u x)^2)) x := by
  have h1 : Integrable (fun y => κ (x-y) * u y) := by
    simpa only [ConvolutionExistsAt, lsmul_apply, smul_eq_mul, mul_comm] using
      hκC.convolutionExists_right (lsmul ℝ ℝ) hu hκ x
  have h2 : Integrable (fun y => κ (x-y) * (u y)^2) := by
    simpa only [ConvolutionExistsAt, lsmul_apply, smul_eq_mul, mul_comm] using
      hκC.convolutionExists_right (lsmul ℝ ℝ) hu2.locallyIntegrable hκ x
  have h0 : Integrable (fun y => κ (x-y)) :=
    (hκ.integrable_of_hasCompactSupport hκC).comp_sub_left x
  have heq : (∫ y, κ (x-y) * u y) = (κ ⋆ u) x := by
    rw [convolution_eq_swap]
    rfl
  have heq0 : (∫ y, κ (x-y)) = 1 := by
    rw [integral_sub_left_eq_self, hκI]
  have hm : (∫ y, (2 * (κ ⋆ u) x) * (κ (x-y) * u y) -
      ((κ ⋆ u) x)^2 * κ (x-y)) ≤ ∫ y, κ (x-y) * (u y)^2 := by
    apply integral_mono ((h1.const_mul _).sub (h0.const_mul _)) h2
    intro y
    simp only [Pi.sub_apply]
    nlinarith [mul_nonneg (hκn (x-y)) (sq_nonneg (u y - (κ ⋆ u) x))]
  rw [integral_sub (h1.const_mul _) (h0.const_mul _), integral_const_mul,
    integral_const_mul, heq, heq0] at hm
  have heq2 : (κ ⋆ (fun x => (u x)^2)) x = ∫ y, κ (x-y) * (u y)^2 := by
    rw [convolution_eq_swap]
    rfl
  rw [heq2]
  nlinarith

lemma convolution_sq_integral_le {n : ℕ} (κ u : Configuration n → ℝ)
    (hκ : Continuous κ) (hκC : HasCompactSupport κ)
    (hκn : ∀ x, 0 ≤ κ x) (hκI : (∫ x, κ x) = 1)
    (hu : LocallyIntegrable u) (hu2 : Integrable (fun x => (u x)^2)) :
    Integrable (fun x => ((κ ⋆ u) x)^2) ∧
    (∫ x, ((κ ⋆ u) x)^2) ≤ ∫ x, (u x)^2 := by
  have hdom : Integrable (κ ⋆ (fun x => (u x)^2)) :=
    (hκ.integrable_of_hasCompactSupport hκC).integrable_convolution (lsmul ℝ ℝ) hu2
  have hcont : Continuous (κ ⋆ u) :=
    hκC.continuous_convolution_left (lsmul ℝ ℝ) hκ hu
  have hsq : Integrable (fun x => ((κ ⋆ u) x)^2) := by
    apply hdom.mono' (hcont.pow 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact convolution_sq_le κ u hκ hκC hκn hκI hu hu2 x
  refine ⟨hsq, ?_⟩
  calc
    _ ≤ ∫ x, (κ ⋆ (fun x => (u x)^2)) x :=
      integral_mono hsq hdom (convolution_sq_le κ u hκ hκC hκn hκI hu hu2)
    _ = _ := by
      rw [integral_convolution (lsmul ℝ ℝ)
        (hκ.integrable_of_hasCompactSupport hκC) hu2, hκI]
      simp

lemma real_convolution_comm {n : ℕ} (u κ : Configuration n → ℝ) :
    u ⋆ κ = κ ⋆ u := by
  ext x
  rw [convolution_eq_swap, convolution_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => mul_comm _ _)

lemma fderiv_const_sub_comp {n : ℕ} (κ : Configuration n → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (x y v : Configuration n) :
    fderiv ℝ (fun z => κ (x - z)) y v = -(fderiv ℝ κ (x-y) v) := by
  have hd := ((hκ.differentiable (by simp) (x-y)).hasFDerivAt).comp y
    ((hasFDerivAt_id y).const_sub x)
  change HasFDerivAt (fun z => κ (x-z)) _ y at hd
  rw [hd.fderiv]
  simp

lemma weak_convolution_partial {n : ℕ} (u g κ : Configuration n → ℝ)
    (v : Configuration n) (hu : LocallyIntegrable u)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκC : HasCompactSupport κ)
    (hw : ∀ φ : Configuration n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * fderiv ℝ φ x v) = -(∫ x, g x * φ x))
    (x : Configuration n) :
    fderiv ℝ (κ ⋆ u) x v = (κ ⋆ g) x := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun y => κ (x-y)) :=
    hκ.comp (contDiff_const.sub contDiff_id)
  have hφC : HasCompactSupport (fun y => κ (x-y)) :=
    hκC.comp_homeomorph (Homeomorph.subLeft x)
  have ht := hw (fun y => κ (x-y)) hφ hφC
  simp_rw [fderiv_const_sub_comp κ hκ x] at ht
  simp only [mul_neg, integral_neg, neg_inj] at ht
  rw [real_convolution_comm κ u,
    (hκC.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hu (hκ.of_le (by simp)) x).fderiv,
    convolution_precompR_apply (lsmul ℝ ℝ) hu (hκC.fderiv ℝ)
      (hκ.continuous_fderiv (by simp)) x v]
  rw [real_convolution_comm κ g]
  simpa only [convolution_def, lsmul_apply, smul_eq_mul] using ht

lemma ae_nonneg_fatou_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (F : ℕ → X → ℝ) (C : ℝ)
    (hF : ∀ n, Integrable (F n) μ) (hn : ∀ n x, 0 ≤ F n x)
    (hf : ∀ x, 0 ≤ f x)
    (ht : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f x)))
    (hC : ∀ n, (∫ x, F n x ∂μ) ≤ C) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ C := by
  have hfm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n => (hF n).aestronglyMeasurable)
      ht
  have hb : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (F n x)) Filter.atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ht] with x hx
        exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
      _ ≤ Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) Filter.atTop :=
        lintegral_liminf_le' (fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal C := by
        apply Filter.liminf_le_of_frequently_le (hu_le := Filter.isBoundedUnder_of ⟨0, fun _ => bot_le⟩)
        apply Filter.Eventually.frequently
        apply Filter.Eventually.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (Filter.Eventually.of_forall (hn n))]
        exact ENNReal.ofReal_le_ofReal (hC n)
  have hfinite : Integrable f μ := ⟨hfm,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf)).2
      (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)⟩
  refine ⟨hfinite, ?_⟩
  have hCn : 0 ≤ C := (integral_nonneg (hn 0)).trans (hC 0)
  rw [← ofReal_integral_eq_lintegral_ofReal hfinite (Filter.Eventually.of_forall hf)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hCn).1 hb

end Coulomb
end
end

end OAI
