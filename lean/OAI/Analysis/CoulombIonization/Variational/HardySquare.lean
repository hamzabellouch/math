import Mathlib
import OAI.Analysis.CoulombIonization.Variational.WeightedVariance

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

lemma square_completion_potential_bound {ι : Type*} [Fintype ι]
    {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (hf2 : MemLp f 2)
    {b : ι → E → ℝ} (hb : ∀ i, ContDiff ℝ ∞ (b i)) (v : ι → E)
    (hdf2 : ∀ i, MemLp (fun x => fderiv ℝ f x (v i)) 2)
    {B D : ι → ℝ} (hbb : ∀ i x, ‖b i x‖ ≤ B i)
    (hdb : ∀ i x, ‖fderiv ℝ (b i) x (v i)‖ ≤ D i)
    {V : E → ℝ} (hVq : Integrable (fun x => V x * ‖f x‖ ^ 2))
    (hdiv : ∀ x, V x ≤ ∑ i, (fderiv ℝ (b i) x (v i) - (b i x) ^ 2)) :
    (∫ x, V x * ‖f x‖ ^ 2) ≤ ∑ i, ∫ x, ‖fderiv ℝ f x (v i)‖ ^ 2 := by
  have iq : Integrable (fun x => ‖f x‖ ^ 2) := hf2.norm.integrable_sq
  have ib (i : ι) : Integrable (fun x => (b i x) ^ 2 * ‖f x‖ ^ 2) :=
    iq.bdd_mul ((hb i).continuous.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbb i x) _)
  have idb (i : ι) : Integrable (fun x => fderiv ℝ (b i) x (v i) * ‖f x‖ ^ 2) :=
    iq.bdd_mul (((hb i).continuous_fderiv (by simp)).clm_apply continuous_const
      ).aestronglyMeasurable (Eventually.of_forall (hdb i))
  have isub (i : ι) : Integrable (fun x =>
      (fderiv ℝ (b i) x (v i) - (b i x) ^ 2) * ‖f x‖ ^ 2) := by
    convert (idb i).sub (ib i) using 1
    funext x
    simp only [Pi.sub_apply]
    ring
  calc
    _ ≤ ∫ x, ∑ i, (fderiv ℝ (b i) x (v i) - (b i x) ^ 2) * ‖f x‖ ^ 2 := by
      apply integral_mono hVq (integrable_finsetSum _ fun i _ => isub i)
      intro x
      simpa only [Finset.sum_mul] using
        mul_le_mul_of_nonneg_right (hdiv x) (sq_nonneg ‖f x‖)
    _ = ∑ i, ∫ x, (fderiv ℝ (b i) x (v i) - (b i x) ^ 2) * ‖f x‖ ^ 2 :=
      integral_finsetSum _ fun i _ => isub i
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      have hn : 0 ≤ (∫ x : E, ‖fderiv ℝ f x (v i) + b i x • f x‖ ^ 2) :=
        integral_nonneg (fun x => sq_nonneg _)
      rw [square_completion_integral_of_memLp hf hf2 (hb i) (v i) (hdf2 i)
        (hbb i) (hdb i)] at hn
      simp only [sub_mul]
      rw [integral_sub (idb i) (ib i)]
      linarith

lemma weak_square_completion_potential_bound {ι : Type*} [Fintype ι]
    {f : E → ℂ} {g : ι → E → ℂ} (hf : MemLp f 2) (hg : ∀ i, MemLp (g i) 2)
    (v : ι → E)
    (hweak : ∀ i (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (v i))) =
        -(∫ y, g i y * (φ y : ℂ)))
    {b : ι → E → ℝ} (hb : ∀ i, ContDiff ℝ ∞ (b i))
    {B D : ι → ℝ} (hbb : ∀ i x, ‖b i x‖ ≤ B i)
    (hdb : ∀ i x, ‖fderiv ℝ (b i) x (v i)‖ ≤ D i)
    {V : E → ℝ} (hV : Continuous V) (hV0 : ∀ x, 0 ≤ V x)
    {BV : ℝ} (hVC : ∀ x, ‖V x‖ ≤ BV)
    (hdiv : ∀ x, V x ≤ ∑ i, (fderiv ℝ (b i) x (v i) - (b i x) ^ 2)) :
    (∫ x, V x * ‖f x‖ ^ 2) ≤
      ∑ i, ∫ x, ‖g i x‖ ^ 2 := by
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
  · exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  · intro n
    exact (square_completion_potential_bound (hu n) (hu2 n).1 hb v
      (fun i => (hdu2 n i).1) hbb hdb (hVu n) hdiv).trans
      (Finset.sum_le_sum fun i _ => (hdu2 n i).2)

end CoulombAtom

end

end OAI
