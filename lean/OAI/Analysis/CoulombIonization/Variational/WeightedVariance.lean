import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.SquareCompletion

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
section WeightedVariance
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma weighted_integral_norm_sq_le {k : α → ℝ} {f : α → ℂ}
    (hk : Integrable k μ) (hk0 : ∀ᵐ x ∂μ, 0 ≤ k x) (hk1 : ∫ x, k x ∂μ = 1)
    (hkf : Integrable (fun x => k x • f x) μ)
    (hkf2 : Integrable (fun x => k x * ‖f x‖ ^ 2) μ) :
    ‖∫ x, k x • f x ∂μ‖ ^ 2 ≤ ∫ x, k x * ‖f x‖ ^ 2 ∂μ := by
  let m : ℂ := ∫ x, k x • f x ∂μ
  have hi : Integrable (fun x => ⟪m, k x • f x⟫_ℝ) μ := hkf.const_inner m
  have heq (x : α) : k x * ‖f x - m‖ ^ 2 =
      (k x * ‖f x‖ ^ 2 - 2 * ⟪m, k x • f x⟫_ℝ) + k x * ‖m‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm (f x) m]
    ring
  have hzero : 0 ≤ ∫ x, k x * ‖f x - m‖ ^ 2 ∂μ :=
    integral_nonneg_of_ae (hk0.mono fun x hx => mul_nonneg hx (sq_nonneg _))
  have hint : (∫ x, k x * ‖f x - m‖ ^ 2 ∂μ) =
      (∫ x, k x * ‖f x‖ ^ 2 ∂μ) - ‖m‖ ^ 2 := by
    calc
      _ = ∫ x, (k x * ‖f x‖ ^ 2 - 2 * ⟪m, k x • f x⟫_ℝ) +
          k x * ‖m‖ ^ 2 ∂μ := integral_congr_ae (Eventually.of_forall heq)
      _ = ((∫ x, k x * ‖f x‖ ^ 2 ∂μ) - 2 * ⟪m, m⟫_ℝ) + ‖m‖ ^ 2 := by
        have hh := integral_add (hkf2.sub (hi.const_mul 2)) (hk.mul_const (‖m‖ ^ 2))
        simp only [Pi.sub_apply] at hh
        rw [hh, integral_sub hkf2 (hi.const_mul 2), integral_const_mul,
          integral_inner hkf m, integral_mul_const, hk1, one_mul]
      _ = _ := by rw [real_inner_self_eq_norm_sq]; ring
  rw [hint] at hzero
  exact sub_nonneg.mp hzero

end WeightedVariance

section FatouBound
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma integral_le_of_nonneg_ae_limit {u : ℕ → α → ℝ} {f : α → ℝ}
    (hi : ∀ n, Integrable (u n) μ) (hf : Integrable f μ)
    (h0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ u n x) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (f x)))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, (∫ x, u n x ∂μ) ≤ C) :
    (∫ x, f x ∂μ) ≤ C := by
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [ofReal_integral_eq_lintegral_ofReal hf hf0]
  calc
    _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (u n x)) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ht] with x hx
      exact ((ENNReal.continuous_ofReal.tendsto (f x)).comp hx).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (u n x) ∂μ) atTop :=
      lintegral_liminf_le' (fun n => ENNReal.continuous_ofReal.measurable.comp_aemeasurable
        (hi n).aestronglyMeasurable.aemeasurable)
    _ ≤ ENNReal.ofReal C := by
      apply liminf_le_of_frequently_le'
      exact (Eventually.of_forall fun n => by
        rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (h0 n)]
        exact ENNReal.ofReal_le_ofReal (hb n)).frequently

end FatouBound

section Mollification
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

lemma convolution_l2_contraction {k : E → ℝ} (hk : Continuous k)
    (hkc : HasCompactSupport k) (hk0 : ∀ x, 0 ≤ k x) (hk1 : ∫ x, k x = 1)
    {f : E → ℂ} (hf : MemLp f 2) :
    MemLp (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) 2 ∧
      (∫ x, ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x‖ ^ 2) ≤ ∫ x, ‖f x‖ ^ 2 := by
  let L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)
  let A := ContinuousLinearMap.mul ℝ ℝ
  have hik : Integrable k := hk.integrable_of_hasCompactSupport hkc
  have hif : LocallyIntegrable f := hf.locallyIntegrable (by norm_num)
  have hif2 : Integrable (fun x => ‖f x‖ ^ 2) := hf.norm.integrable_sq
  have hc : Continuous (k ⋆[L] f) := hkc.continuous_convolution_left L hk hif
  have hib : Integrable (k ⋆[A] (fun x => ‖f x‖ ^ 2)) :=
    hik.integrable_convolution A hif2
  have hbound (x : E) : ‖(k ⋆[L] f) x‖ ^ 2 ≤
      (k ⋆[A] (fun x => ‖f x‖ ^ 2)) x := by
    exact weighted_integral_norm_sq_le hik (Eventually.of_forall hk0) hk1
      ((hkc.convolutionExists_left L hk hif x).integrable)
      ((hkc.convolutionExists_left A hk hif2.locallyIntegrable x).integrable)
  have hisq : Integrable (fun x => ‖(k ⋆[L] f) x‖ ^ 2) :=
    hib.mono' (hc.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hbound x)
  refine ⟨(memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 hisq, ?_⟩
  calc
    _ ≤ ∫ x, (k ⋆[A] (fun x => ‖f x‖ ^ 2)) x := integral_mono hisq hib hbound
    _ = _ := by rw [integral_convolution A hik hif2, hk1]; simp [A]

lemma mollified_weak_derivative {k : E → ℝ} (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) {f g : E → ℂ} (hf : LocallyIntegrable f)
    (v : E)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y v)) =
        -(∫ y, g y * (φ y : ℂ))) (x : E) :
    fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x v =
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g) x := by
  let L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)
  have hφ : ContDiff ℝ ∞ (fun y => k (x - y)) := hk.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport (fun y => k (x - y)) :=
    hkc.comp_homeomorph (Homeomorph.subLeft x)
  have hdφ (y : E) : lineDeriv ℝ (fun y => k (x - y)) y v =
      -(fderiv ℝ k (x - y) v) := by
    have hh := (hk.differentiable (by simp) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    have hs := (hh.hasLineDerivAt v).lineDeriv
    simpa [Function.comp_def] using hs
  have hw := hweak (fun y => k (x - y)) hφ hcφ
  simp only [hdφ, Complex.ofReal_neg, mul_neg, integral_neg, neg_inj] at hw
  have hid : Integrable (fun y => (L.precompL E) (fderiv ℝ k (x - y)) (f y)) :=
    ((hkc.fderiv ℝ).convolutionExists_left (L.precompL E)
      (hk.continuous_fderiv (by simp)) hf x).integrable_swap
  rw [(hkc.hasFDerivAt_convolution_left L (hk.of_le (by simp)) hf x).fderiv,
    convolution_eq_swap, ContinuousLinearMap.integral_apply hid, convolution_eq_swap]
  simpa only [ContinuousLinearMap.precompL_apply, L, ContinuousLinearMap.lsmul_apply,
    Complex.real_smul, mul_comm] using hw

def shrinkingBump (n : ℕ) : ContDiffBump (0 : E) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 * (1 / ((n : ℝ) + 1))
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E]
  [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
lemma shrinkingBump_tendsto :
    Tendsto (fun n => (shrinkingBump (E := E) n).rOut) atTop (𝓝 0) := by
  simpa [shrinkingBump] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2

lemma weak_square_completion_bound {ι : Type*} [Fintype ι]
    {f : E → ℂ} {g : ι → E → ℂ} (hf : MemLp f 2) (hg : ∀ i, MemLp (g i) 2)
    (v : ι → E)
    (hweak : ∀ i (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (v i))) =
        -(∫ y, g i y * (φ y : ℂ)))
    {b : ι → E → ℝ} (hb : ∀ i, ContDiff ℝ ∞ (b i))
    {B D : ι → ℝ} (hbb : ∀ i x, ‖b i x‖ ≤ B i)
    (hdb : ∀ i x, ‖fderiv ℝ (b i) x (v i)‖ ≤ D i)
    {V : E → ℝ} (hV : Continuous V) (hV0 : ∀ x, 0 ≤ V x)
    {BV C : ℝ} (hVC : ∀ x, ‖V x‖ ≤ BV) (hC : 0 ≤ C)
    (hbnd : ∀ x, ∑ i, (b i x) ^ 2 ≤ C)
    (hdiv : ∀ x, V x ≤ ∑ i, fderiv ℝ (b i) x (v i)) :
    (∫ x, V x * ‖f x‖ ^ 2) ≤
      (∑ i, ∫ x, ‖g i x‖ ^ 2) + C * (∫ x, ‖f x‖ ^ 2) := by
  let k : ℕ → E → ℝ := fun n => (shrinkingBump n).normed volume
  let L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)
  let u : ℕ → E → ℂ := fun n => k n ⋆[L] f
  have hk (n : ℕ) : ContDiff ℝ ∞ (k n) := (shrinkingBump n).contDiff_normed
  have hkc (n : ℕ) : HasCompactSupport (k n) := (shrinkingBump n).hasCompactSupport_normed
  have hk0 (n : ℕ) : ∀ x, 0 ≤ k n x := (shrinkingBump n).nonneg_normed
  have hk1 (n : ℕ) : (∫ x, k n x) = 1 := (shrinkingBump n).integral_normed
  have hlocal := hf.locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hu (n : ℕ) : ContDiff ℝ ∞ (u n) :=
    (hkc n).contDiff_convolution_left L (hk n) hlocal
  have hu2 (n : ℕ) : MemLp (u n) 2 ∧
      (∫ x, ‖u n x‖ ^ 2) ≤ ∫ x, ‖f x‖ ^ 2 :=
    convolution_l2_contraction (hk n).continuous (hkc n) (hk0 n) (hk1 n) hf
  have hdu (n : ℕ) (i : ι) : (fun x => fderiv ℝ (u n) x (v i)) = k n ⋆[L] g i := by
    funext x
    exact mollified_weak_derivative (hk n) (hkc n) hlocal (v i) (hweak i) x
  have hdu2 (n : ℕ) (i : ι) : MemLp (fun x => fderiv ℝ (u n) x (v i)) 2 ∧
      (∫ x, ‖fderiv ℝ (u n) x (v i)‖ ^ 2) ≤ ∫ x, ‖g i x‖ ^ 2 := by
    have hh := convolution_l2_contraction (hk n).continuous (hkc n) (hk0 n) (hk1 n) (hg i)
    change MemLp (k n ⋆[L] g i) 2 ∧
      (∫ x, ‖(k n ⋆[L] g i) x‖ ^ 2) ≤ ∫ x, ‖g i x‖ ^ 2 at hh
    simpa only [← hdu n i] using hh
  have hVu (n : ℕ) : Integrable (fun x => V x * ‖u n x‖ ^ 2) :=
    (hu2 n).1.norm.integrable_sq.bdd_mul hV.aestronglyMeasurable (Eventually.of_forall hVC)
  have hVf : Integrable (fun x => V x * ‖f x‖ ^ 2) :=
    hf.norm.integrable_sq.bdd_mul hV.aestronglyMeasurable (Eventually.of_forall hVC)
  have ht : ∀ᵐ x, Tendsto (fun n => u n x) atTop (𝓝 (f x)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      shrinkingBump_tendsto
      (Eventually.of_forall fun n => le_refl (2 * (shrinkingBump (E := E) n).rIn)) hlocal
  apply integral_le_of_nonneg_ae_limit hVu hVf
    (fun n => Eventually.of_forall fun x => mul_nonneg (hV0 x) (sq_nonneg _))
    (Eventually.of_forall fun x => mul_nonneg (hV0 x) (sq_nonneg _))
  · filter_upwards [ht] with x hx
    exact (hx.norm.pow 2).const_mul (V x)
  · exact add_nonneg (Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _)
      (mul_nonneg hC (integral_nonneg fun x => sq_nonneg _))
  · intro n
    exact (square_completion_bound_of_memLp (hu n) (hu2 n).1 hb v
      (fun i => (hdu2 n i).1) hbb hdb (hVu n) hbnd hdiv).trans
      (add_le_add (Finset.sum_le_sum fun i _ => (hdu2 n i).2)
        (mul_le_mul_of_nonneg_left (hu2 n).2 hC))

end Mollification

lemma regularized_nuclear_bound {N : ℕ} (i : Fin N) {Z ε : ℝ}
    (hZ : 0 ≤ Z) (hε : 0 < ε) {f : Configuration N → ℂ}
    {g : Fin 3 → Configuration N → ℂ}
    (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : Configuration N → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (direction i a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    (∫ x, 2 * Z * regularizedCoulomb ε (x i) * ‖f x‖ ^ 2) ≤
      (∑ a, ∫ x, ‖g a x‖ ^ 2) + Z ^ 2 * (∫ x, ‖f x‖ ^ 2) := by
  let b : Fin 3 → Configuration N → ℝ := fun a x => Z * radialField ε a (x i)
  have hb (a : Fin 3) : ContDiff ℝ ∞ (b a) :=
    contDiff_const.mul ((radialField_smooth hε a).comp
      (ContinuousLinearMap.proj i : Configuration N →L[ℝ] Space).contDiff)
  have hdb (a : Fin 3) (x : Configuration N) :
      fderiv ℝ (b a) x (direction i a) =
        Z * fderiv ℝ (radialField ε a) (x i) (EuclideanSpace.single a 1) := by
    have hh := ((radialField_smooth hε a).comp
      (ContinuousLinearMap.proj i : Configuration N →L[ℝ] Space).contDiff
      ).differentiable (by simp) x
    change DifferentiableAt ℝ (fun y : Configuration N => radialField ε a (y i)) x at hh
    change (fderiv ℝ (fun y : Configuration N => Z * radialField ε a (y i)) x) _ = _
    rw [(hh.hasFDerivAt.const_mul Z).fderiv]
    simpa only [smul_apply, smul_eq_mul] using
      congrArg (Z * ·) (coordinate_radialField_fderiv hε i a x)
  refine weak_square_completion_bound hf hg (fun a => direction i a) hweak hb
    (B := fun _ => Z) (D := fun _ => Z * ε⁻¹)
    (BV := 2 * Z * ε⁻¹) (C := Z ^ 2)
    (V := fun x => 2 * Z * regularizedCoulomb ε (x i)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a x
    change ‖Z * radialField ε a (x i)‖ ≤ Z
    rw [norm_mul, Real.norm_of_nonneg hZ]
    exact (mul_le_mul_of_nonneg_left (radialField_norm_le hε a (x i)) hZ).trans_eq
      (mul_one Z)
  · intro a x
    rw [hdb, Real.norm_of_nonneg
      (mul_nonneg hZ (radialField_derivative_bounds hε a (x i)).1)]
    exact mul_le_mul_of_nonneg_left (radialField_derivative_bounds hε a (x i)).2 hZ
  · exact continuous_const.mul ((regularizedCoulomb_continuous hε).comp
      (continuous_apply i))
  · intro x
    exact mul_nonneg (by positivity) (regularizedCoulomb_nonneg ε (x i))
  · intro x
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (regularizedCoulomb_nonneg ε (x i)))]
    exact mul_le_mul_of_nonneg_left (regularizedCoulomb_le hε (x i)) (by positivity)
  · positivity
  · intro x
    simp only [b, mul_pow, ← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (sum_radialField_sq_le hε (x i))
      (sq_nonneg Z)).trans_eq (mul_one _)
  · intro x
    simp only [hdb, ← Finset.mul_sum]
    have hh := mul_le_mul_of_nonneg_left (radialField_divergence hε (x i)) hZ
    simpa only [regularizedCoulomb, mul_div_assoc, mul_left_comm Z 2, mul_assoc] using hh

lemma regularizedCoulomb_tendsto {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (x : Space) :
    Tendsto (fun n => regularizedCoulomb (ε n) x) atTop (𝓝 (1 / ‖x‖)) := by
  by_cases hx : x = 0
  · simp [hx, regularizedCoulomb]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hh := (tendsto_const_nhds (x := ‖x‖) (f := atTop)).div
      (tendsto_const_nhds.add (hε.pow 2))
      (by simpa using pow_ne_zero 2 hn : ‖x‖ ^ 2 + (0 : ℝ) ^ 2 ≠ 0)
    have heq : ‖x‖ / (‖x‖ ^ 2 + (0 : ℝ) ^ 2) = 1 / ‖x‖ := by
      simp only [zero_pow (by decide : 2 ≠ 0), add_zero]
      field_simp
    change Tendsto (fun n : ℕ => ‖x‖ / (‖x‖ ^ 2 + ε n ^ 2)) atTop
      (𝓝 (‖x‖ / (‖x‖ ^ 2 + (0 : ℝ) ^ 2))) at hh
    simpa only [regularizedCoulomb, regularizedRadius_sq, heq] using hh

lemma nuclear_bound {N : ℕ} (i : Fin N) {Z : ℝ} (hZ : 0 ≤ Z)
    {f : Configuration N → ℂ} {g : Fin 3 → Configuration N → ℂ}
    (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : Configuration N → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (direction i a))) =
        -(∫ y, g a y * (φ y : ℂ)))
    (hnu : Integrable (fun x => ‖f x‖ ^ 2 / ‖x i‖)) :
    2 * Z * (∫ x, ‖f x‖ ^ 2 / ‖x i‖) ≤
      (∑ a, ∫ x, ‖g a x‖ ^ 2) + Z ^ 2 * (∫ x, ‖f x‖ ^ 2) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have htε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let u : ℕ → Configuration N → ℝ :=
    fun n x => 2 * Z * regularizedCoulomb (ε n) (x i) * ‖f x‖ ^ 2
  have hi (n : ℕ) : Integrable (u n) := by
    apply hf.norm.integrable_sq.bdd_mul (c := 2 * Z * (ε n)⁻¹)
      (continuous_const.mul ((regularizedCoulomb_continuous (hε n)).comp
        (continuous_apply i))).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change ‖2 * Z * regularizedCoulomb (ε n) (x i)‖ ≤ _
      rw [Real.norm_of_nonneg (mul_nonneg (by positivity)
        (regularizedCoulomb_nonneg (ε n) (x i)))]
      exact mul_le_mul_of_nonneg_left (regularizedCoulomb_le (hε n) (x i)) (by positivity)
  rw [← integral_const_mul]
  apply integral_le_of_nonneg_ae_limit hi (hnu.const_mul (2 * Z))
  · intro n
    exact Eventually.of_forall fun x => mul_nonneg
      (mul_nonneg (by positivity) (regularizedCoulomb_nonneg (ε n) (x i))) (sq_nonneg _)
  · exact Eventually.of_forall fun x => mul_nonneg (by positivity) (by positivity)
  · exact Eventually.of_forall fun x => by
      have hh := ((regularizedCoulomb_tendsto htε (x i)).const_mul (2 * Z)
        ).mul_const (‖f x‖ ^ 2)
      have heq : 2 * Z * (1 / ‖x i‖) * ‖f x‖ ^ 2 =
          2 * Z * (‖f x‖ ^ 2 / ‖x i‖) := by ring
      simpa only [heq] using hh
  · exact add_nonneg (Finset.sum_nonneg fun a _ => integral_nonneg fun x => sq_nonneg _)
      (mul_nonneg (sq_nonneg Z) (integral_nonneg fun x => sq_nonneg _))
  · intro n
    exact regularized_nuclear_bound i hZ (hε n) hf hg hweak

theorem formEnergy_lower_bound {N : ℕ} {Z : ℝ} (hZ : 0 ≤ Z)
    {ψ : FormVector N} (hψ : FormAdmissible ψ) :
    -(N : ℝ) * Z ^ 2 / 2 ≤ formEnergy Z ψ := by
  rcases hψ with ⟨hf, hg, hw, _, hnorm, hnu, _⟩
  have hb (s : Spins N) (i : Fin N) := nuclear_bound i hZ (hf s) (hg s i)
    (hw s i) (hnu s i)
  have hs := Finset.sum_le_sum (s := Finset.univ) fun s _ =>
    Finset.sum_le_sum (s := Finset.univ) fun i _ => hb s i
  have heq : (∑ s : Spins N, ∑ i : Fin N,
      ((∑ a : Fin 3, ∫ x, ‖ψ.gradient s i a x‖ ^ 2) +
        Z ^ 2 * (∫ x, ‖ψ.value s x‖ ^ 2))) =
      (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3, ∫ x, ‖ψ.gradient s i a x‖ ^ 2) +
        (N : ℝ) * Z ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← Finset.mul_sum]
    rw [hnorm, mul_one]
  rw [heq] at hs
  simp only [← Finset.mul_sum] at hs
  have hr : 0 ≤ (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
      if i < j then (∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i - x j‖) else 0) := by
    apply Finset.sum_nonneg
    intro s _
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact integral_nonneg fun x => div_nonneg (sq_nonneg _) (norm_nonneg _)
    · exact le_refl 0
  unfold formEnergy
  linarith

theorem sector_energies_bddBelow (Z : ℝ) (hZ : 0 ≤ Z) (N : ℕ) :
    BddBelow {e | ∃ ψ : FormVector N, FormAdmissible ψ ∧ formEnergy Z ψ = e} := by
  refine ⟨-(N : ℝ) * Z ^ 2 / 2, ?_⟩
  rintro e ⟨ψ, hψ, rfl⟩
  exact formEnergy_lower_bound hZ hψ

end CoulombAtom

end

end OAI
