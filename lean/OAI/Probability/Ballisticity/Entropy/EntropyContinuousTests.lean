import Mathlib
import OAI.Probability.Ballisticity.Entropy.EntropyVariational

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory TopologicalSpace
open scoped ENNReal Classical Topology BoundedContinuousFunction
namespace DirectionalTransience.Entropy

lemma exp_sub_le_exp_mul {x y : ℝ} (h : x≤y) :
    Real.exp y-Real.exp x ≤ Real.exp y*(y-x) := by
  rcases h.eq_or_lt with rfl | _
  · simp
  · have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (x-y)) (Real.exp_pos y).le
    rw [← Real.exp_add,add_sub_cancel] at hh
    nlinarith

lemma abs_exp_sub_le {x y B : ℝ} (hx : x≤B) (hy : y≤B) :
    |Real.exp x-Real.exp y| ≤ Real.exp B*|x-y| := by
  rcases le_total x y with h|h
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonpos (sub_nonpos.mpr h),neg_sub,neg_sub]
    exact (exp_sub_le_exp_mul h).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hy) (sub_nonneg.mpr h))
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),abs_of_nonneg (sub_nonneg.mpr h)]
    exact (exp_sub_le_exp_mul h).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hx) (sub_nonneg.mpr h))

lemma abs_sub_min_le {x y B : ℝ} (hx : x≤B) : |x-min y B| ≤ |x-y| := by
  by_cases hy : y≤B
  · simp [min_eq_left hy]
  · have hy : B≤y := le_of_not_ge hy
    rw [min_eq_right hy,abs_of_nonpos (sub_nonpos.mpr hx),
      abs_of_nonpos (sub_nonpos.mpr (hx.trans hy))]
    linarith

section Approximation
variable {X : Type*} [TopologicalSpace X] [MetrizableSpace X] [MeasurableSpace X] [BorelSpace X]

lemma continuous_exp_test_approx (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (F : X → ℝ) (hF : Measurable F)
    (hB : ∃ B : ℝ, ∀ x, |F x|≤B) {ε : ℝ} (hε : 0<ε) :
    ∃ g : X →ᵇ ℝ,
      |(∫ x, F x ∂μ)-(∫ x, g x ∂μ)| ≤ ε ∧
      |(∫ x, Real.exp (F x) ∂ν)-(∫ x, Real.exp (g x) ∂ν)| ≤ ε := by
  obtain ⟨B,hB⟩ := hB
  let δ := ε/(Real.exp B+1)
  have hδ : 0<δ := div_pos hε (by positivity)
  have hi : Integrable F (μ+ν) := integrable_of_bounded hF ⟨B,hB⟩
  obtain ⟨g,hg,hgi⟩ := hi.exists_boundedContinuous_integral_sub_le hδ
  let k : X →ᵇ ℝ := min g (BoundedContinuousFunction.const X B)
  have hk : ∀ x, k x≤B := fun x => min_le_right (g x) B
  have hkB : ∃ b : ℝ, ∀ x, |k x|≤b :=
    ⟨‖k‖,fun x => by simpa only [Real.norm_eq_abs] using k.norm_coe_le_norm x⟩
  have hμF : Integrable F μ := integrable_of_bounded hF ⟨B,hB⟩
  have hνF : Integrable F ν := integrable_of_bounded hF ⟨B,hB⟩
  have herr (x : X) : |F x-k x|≤|F x-g x| := abs_sub_min_le ((le_abs_self _).trans (hB x))
  have hgμ : (∫ x, |F x-g x| ∂μ)≤δ := by
    have h1 := integral_add_measure ((hμF.sub (g.integrable μ)).norm)
      ((hνF.sub (g.integrable ν)).norm)
    simp only [Real.norm_eq_abs, Pi.sub_apply] at h1 hg
    rw [h1] at hg
    have hn : 0 ≤ ∫ x, |F x-g x| ∂ν := integral_nonneg (fun x => abs_nonneg (F x-g x))
    linarith
  have hgν : (∫ x, |F x-g x| ∂ν)≤δ := by
    have h1 := integral_add_measure ((hμF.sub (g.integrable μ)).norm)
      ((hνF.sub (g.integrable ν)).norm)
    simp only [Real.norm_eq_abs, Pi.sub_apply] at h1 hg
    rw [h1] at hg
    have hn : 0 ≤ ∫ x, |F x-g x| ∂μ := integral_nonneg (fun x => abs_nonneg (F x-g x))
    linarith
  have hkμ : (∫ x, |F x-k x| ∂μ)≤δ :=
    (integral_mono (hμF.sub (k.integrable μ)).abs (hμF.sub (g.integrable μ)).abs herr).trans hgμ
  have hkν : (∫ x, |F x-k x| ∂ν)≤δ :=
    (integral_mono (hνF.sub (k.integrable ν)).abs (hνF.sub (g.integrable ν)).abs herr).trans hgν
  have hδle : δ≤ε := by
    apply (div_le_iff₀ (show 0<Real.exp B+1 by positivity)).mpr
    nlinarith [Real.exp_pos B]
  refine ⟨k,?_,?_⟩
  · rw [← integral_sub hμF (k.integrable μ)]
    exact (abs_integral_le_integral_abs).trans (hkμ.trans hδle)
  · have heF : Integrable (fun x => Real.exp (F x)) ν := exp_integrable_of_bounded hF ⟨B,hB⟩
    have hek : Integrable (fun x => Real.exp (k x)) ν := exp_integrable_of_bounded k.continuous.measurable hkB
    rw [← integral_sub heF hek]
    calc
      _ ≤ ∫ x, |Real.exp (F x)-Real.exp (k x)| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ x, Real.exp B*|F x-k x| ∂ν := integral_mono (heF.sub hek).abs
        (((hνF.sub (k.integrable ν)).abs).const_mul _) (fun x =>
          abs_exp_sub_le ((le_abs_self _).trans (hB x)) (hk x))
      _ = Real.exp B*(∫ x, |F x-k x| ∂ν) := integral_const_mul _ _
      _ ≤ Real.exp B*δ := mul_le_mul_of_nonneg_left hkν (Real.exp_pos B).le
      _ ≤ ε := by
        dsimp only [δ]
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (show 0<Real.exp B+1 by positivity)).mpr
        nlinarith

theorem expBudget_of_continuous (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C : ℝ}
    (h : ∀ g : X →ᵇ ℝ, (∫ x, g x ∂μ)-(∫ x, Real.exp (g x) ∂ν)+1≤C) :
    ExpBudget μ ν C := by
  intro F hF hB
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨g,hg,hge⟩ := continuous_exp_test_approx μ ν F hF hB (half_pos hε)
  have h1 := (abs_le.mp hg).2
  have h2 := (abs_le.mp hge).1
  have h3 := h g
  linarith

end Approximation
end DirectionalTransience.Entropy

end

section

open MeasureTheory ProbabilityTheory InformationTheory TopologicalSpace Filter
open scoped ENNReal Topology BoundedContinuousFunction
namespace DirectionalTransience.Entropy

variable {X I : Type*} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma kl_le_of_weak_limit {l : Filter I} [l.NeBot]
    (μs νs : I → ProbabilityMeasure X) (μ ν : ProbabilityMeasure X)
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν))
    {C : ℝ} (hC : 0≤C)
    (hbudget : ∀ᶠ i in l, klDiv (μs i : Measure X) (νs i : Measure X) ≤ ENNReal.ofReal C) :
    klDiv (μ : Measure X) (ν : Measure X) ≤ ENNReal.ofReal C := by
  apply kl_le_of_expBudget
  apply expBudget_of_continuous
  intro f
  let ef : X →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨fun x => Real.exp (f x), Real.continuous_exp.comp f.continuous⟩
  have h1 := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f
  have h2 := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν ef
  apply le_of_tendsto ((h1.sub h2).add_const 1)
  filter_upwards [hbudget] with i hi
  exact expBudget_of_kl_le (μs i : Measure X) (νs i : Measure X) hC hi
    f f.continuous.measurable ⟨‖f‖,fun x => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x⟩

end DirectionalTransience.Entropy

end

end OAI
