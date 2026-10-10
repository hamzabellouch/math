import Mathlib
import OAI.Probability.LogConcave.JetEstimates.Growth

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma integral_mul_sq_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x*g x ∂μ)^2 ≤ (∫ x, (f x)^2 ∂μ)*(∫ x, (g x)^2 ∂μ) := by
  have hi (f g : X → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
      inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x*g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    simp [hx,hy,mul_comm]
  have hh := sq_le_sq₀ (norm_nonneg (inner ℝ (hf.toLp f) (hg.toLp g)))
    (mul_nonneg (norm_nonneg (hf.toLp f)) (norm_nonneg (hg.toLp g))) |>.mpr
      (norm_inner_le_norm (𝕜 := ℝ) (hf.toLp f) (hg.toLp g))
  rw [Real.norm_eq_abs,sq_abs,mul_pow,← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq,hi,hi,hi] at hh
  simpa only [pow_two] using hh

namespace Appell
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι ϑ κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ϑ] [DecidableEq ϑ]
  [Fintype κ] [DecidableEq κ]

def crossMoment (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (c : ϑ → κ) : ℝ :=
  ∫ x, slotPolynomial μ b a Finset.univ x * slotPolynomial μ b c Finset.univ x ∂μ

omit [DecidableEq κ] in
lemma sum_crossMoment (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    (b : OrthonormalBasis κ ℝ E) (T : (ι → κ) → ℝ) (U : (ϑ → κ) → ℝ) :
    (∑ a, ∑ c, T a * crossMoment μ b a c * U c) =
      ∫ x, tensorPolynomial μ b T x * tensorPolynomial μ b U x ∂μ := by
  have hh (a : ι → κ) (c : ϑ → κ) : Integrable
      (fun x => T a * slotPolynomial μ b a Finset.univ x *
        (U c * slotPolynomial μ b c Finset.univ x)) μ :=
    ((((slotPolynomial_growth μ b a _).mul (slotPolynomial_growth μ b c _)).integrable
      ((slotPolynomial_smooth μ b a _).continuous.mul
        (slotPolynomial_smooth μ b c _).continuous).aestronglyMeasurable hμ).const_mul
      (T a*U c)).congr (Filter.Eventually.of_forall (fun x => by ring))
  simp only [tensorPolynomial,Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ (fun a ha => integrable_finsetSum _ (fun c hc => hh a c))]
  simp_rw [integral_finsetSum _ (fun c hc => hh _ c)]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro c hc
  rw [show (fun x => T a * slotPolynomial μ b a Finset.univ x *
      (U c * slotPolynomial μ b c Finset.univ x)) =
      (fun x => (T a*U c) * (slotPolynomial μ b a Finset.univ x *
        slotPolynomial μ b c Finset.univ x)) by funext x; ring,integral_const_mul]
  simp only [crossMoment]
  ring

theorem crossMoment_sq_bound (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    {β : ℝ} (hβ : 0 ≤ β) (hP : HasPoincare μ β) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) (U : (ϑ → κ) → ℝ) :
    (∑ a, ∑ c, T a * crossMoment μ b a c * U c)^2 ≤
      (β^(Fintype.card ι)*((Fintype.card ι).factorial:ℝ)^2) *
      (β^(Fintype.card ϑ)*((Fintype.card ϑ).factorial:ℝ)^2) *
      (∑ a, (T a)^2)*(∑ c, (U c)^2) := by
  rw [sum_crossMoment μ hμ]
  have hh := (integral_mul_sq_le (tensorPolynomial_memLp μ hμ b T)
    (tensorPolynomial_memLp μ hμ b U)).trans
    (mul_le_mul (tensorPolynomial_L2 μ hμ hβ hP b T)
      (tensorPolynomial_L2 μ hμ hβ hP b U)
      (integral_nonneg (fun _ => sq_nonneg _)) (by positivity))
  exact hh.trans_eq (by ring)
end Appell
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
