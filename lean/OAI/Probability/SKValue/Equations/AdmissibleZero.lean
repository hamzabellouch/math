import Mathlib
import OAI.Probability.SKValue.Control.ControlIntegral

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma admissible_zero (W : BrownianSpace) (t : ℝ) :
    Admissible W t (fun _ _ ↦ (0 : ℝ)) := by
  constructor
  · intro s
    exact measurable_const
  · intro s ω
    norm_num

lemma brownian_increment_integrable (W : BrownianSpace) (t : ℝ) :
    Integrable (fun ω ↦ W.B 1 ω-W.B t.toNNReal ω) W.μ :=
  (W.brownian.integrable_eval 1).sub (W.brownian.integrable_eval _)

lemma brownian_increment_mean (W : BrownianSpace) (t : ℝ) :
    (∫ ω, W.B 1 ω-W.B t.toNNReal ω ∂W.μ)=0 := by
  rw [integral_sub (W.brownian.integrable_eval 1) (W.brownian.integrable_eval _),
    W.brownian.integral_eval, W.brownian.integral_eval, sub_self]

lemma controlPayoff_eq (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) (α : ℝ≥0 → W.Ω → ℝ) :
    controlPayoff W γ t x α = ∫ ω,
      |x+(W.B 1 ω-W.B t.toNNReal ω)+controlIntegral γ t α 1 ω|-
        (1/2 : ℝ)*controlIntegral γ t α 2 ω ∂W.μ := by
  simp only [controlPayoff, controlIntegral_eq W γ ht, pow_one]
  congr 1
  funext ω
  congr 2
  ring

lemma controlPayoff_integrable {W : BrownianSpace} (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) {α : ℝ≥0 → W.Ω → ℝ} (hα : Admissible W t α) :
    Integrable (fun ω ↦ |x+(W.B 1 ω-W.B t.toNNReal ω)+controlIntegral γ t α 1 ω|-
      (1/2 : ℝ)*controlIntegral γ t α 2 ω) W.μ :=
  (((integrable_const x).add (brownian_increment_integrable W t)).add
    (controlIntegral_integrable γ ht hα 1)).abs.sub
      ((controlIntegral_integrable γ ht hα 2).const_mul _)

lemma controlPayoff_upper {W : BrownianSpace} (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) {α : ℝ≥0 → W.Ω → ℝ} (hα : Admissible W t α) :
    controlPayoff W γ t x α ≤ |x|+(∫ ω, |W.B 1 ω-W.B t.toNNReal ω| ∂W.μ)+
      (1/2 : ℝ)*∫ s in t..1, γ.cutoff s := by
  rw [controlPayoff_eq W γ ht]
  calc
    _ ≤ ∫ ω, |x|+|W.B 1 ω-W.B t.toNNReal ω|+
        (1/2 : ℝ)*(∫ s in t..1, γ.cutoff s) ∂W.μ := by
      apply integral_mono (controlPayoff_integrable γ ht x hα)
        (((integrable_const _).add (brownian_increment_integrable W t).abs).add (integrable_const _))
      intro ω
      dsimp only [Pi.add_apply]
      have hc := control_cost_bound γ ht hα ω
      have h1 := abs_add_le (x+(W.B 1 ω-W.B t.toNNReal ω)) (controlIntegral γ t α 1 ω)
      have h2 := abs_add_le x (W.B 1 ω-W.B t.toNNReal ω)
      linarith
    _ = _ := by
      have hi : Integrable (fun ω ↦ |x|+|W.B 1 ω-W.B t.toNNReal ω|) W.μ :=
        (integrable_const |x|).add (brownian_increment_integrable W t).abs
      rw [integral_add hi (integrable_const ((1/2 : ℝ)*(∫ s in t..1, γ.cutoff s))),
        integral_add (integrable_const |x|) (brownian_increment_integrable W t).abs]
      simp

lemma controlPayoff_zero (W : BrownianSpace) (γ : OrderParameter) (t x : ℝ) :
    controlPayoff W γ t x (fun _ _ ↦ (0 : ℝ)) =
      ∫ ω, |x+(W.B 1 ω-W.B t.toNNReal ω)| ∂W.μ := by
  simp only [controlPayoff, mul_zero, zero_pow (by norm_num : 2≠0),
    intervalIntegral.integral_zero, add_zero, sub_zero]
  congr 1
  funext ω
  congr 1
  ring

lemma controlPayoff_zero_lower (W : BrownianSpace) (γ : OrderParameter) (t x : ℝ) :
    |x|≤controlPayoff W γ t x (fun _ _ ↦ (0 : ℝ)) := by
  rw [controlPayoff_zero]
  have hm : (∫ ω, x+(W.B 1 ω-W.B t.toNNReal ω) ∂W.μ)=x := by
    rw [integral_add (integrable_const _) (brownian_increment_integrable W t), brownian_increment_mean]
    simp
  simpa only [Real.norm_eq_abs, hm] using
    norm_integral_le_integral_norm (μ := W.μ) (fun ω ↦ x+(W.B 1 ω-W.B t.toNNReal ω))

lemma control_values_nonempty (W : BrownianSpace) (γ : OrderParameter) (t x : ℝ) :
    {r | ∃ α, Admissible W t α ∧ r=controlPayoff W γ t x α}.Nonempty :=
  ⟨_, ⟨_, admissible_zero W t, rfl⟩⟩

lemma control_values_bddAbove (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) :
    BddAbove {r | ∃ α, Admissible W t α ∧ r=controlPayoff W γ t x α} := by
  refine ⟨|x|+(∫ ω, |W.B 1 ω-W.B t.toNNReal ω| ∂W.μ)+
      (1/2 : ℝ)*∫ s in t..1, γ.cutoff s, ?_⟩
  rintro r ⟨α,hα,rfl⟩
  exact controlPayoff_upper γ ht x hα

lemma phi_lower (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) : |x|≤phi W γ t x := by
  exact (controlPayoff_zero_lower W γ t x).trans
    (le_csSup (control_values_bddAbove W γ ht x) ⟨_, admissible_zero W t, rfl⟩)

lemma phi_upper (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) :
    phi W γ t x≤|x|+(∫ ω, |W.B 1 ω-W.B t.toNNReal ω| ∂W.μ)+
      (1/2 : ℝ)*∫ s in t..1, γ.cutoff s := by
  apply csSup_le (control_values_nonempty W γ t x)
  rintro r ⟨α,hα,rfl⟩
  exact controlPayoff_upper γ ht x hα

lemma controlPayoff_le_add_dist {W : BrownianSpace} (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x y : ℝ) {α : ℝ≥0 → W.Ω → ℝ} (hα : Admissible W t α) :
    controlPayoff W γ t x α ≤ controlPayoff W γ t y α+|x-y| := by
  rw [controlPayoff_eq W γ ht, controlPayoff_eq W γ ht]
  have hi := controlPayoff_integrable γ ht y hα
  have hh : ∫ ω, |x+(W.B 1 ω-W.B t.toNNReal ω)+controlIntegral γ t α 1 ω|-
      (1/2 : ℝ)*controlIntegral γ t α 2 ω ∂W.μ ≤
      ∫ ω, (|y+(W.B 1 ω-W.B t.toNNReal ω)+controlIntegral γ t α 1 ω|-
      (1/2 : ℝ)*controlIntegral γ t α 2 ω)+|x-y| ∂W.μ := by
    apply integral_mono (controlPayoff_integrable γ ht x hα) (hi.add (integrable_const _))
    intro ω
    dsimp only [Pi.add_apply]
    have he : x+(W.B 1 ω-W.B t.toNNReal ω)+controlIntegral γ t α 1 ω =
        (y+(W.B 1 ω-W.B t.toNNReal ω)+controlIntegral γ t α 1 ω)+(x-y) := by ring
    rw [he]
    linarith [abs_add_le (y+(W.B 1 ω-W.B t.toNNReal ω)+controlIntegral γ t α 1 ω) (x-y)]
  simpa only [integral_add hi (integrable_const _), integral_const, probReal_univ, one_smul] using hh

lemma phi_le_add_dist (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x y : ℝ) : phi W γ t x ≤ phi W γ t y+|x-y| := by
  apply csSup_le (control_values_nonempty W γ t x)
  rintro r ⟨α,hα,rfl⟩
  exact (controlPayoff_le_add_dist γ ht x y hα).trans
    (add_le_add (le_csSup (control_values_bddAbove W γ ht y) ⟨α,hα,rfl⟩) le_rfl)

lemma phi_lipschitz (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) : LipschitzWith 1 (phi W γ t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
  apply abs_le.mpr
  constructor
  · have h := phi_le_add_dist W γ ht y x
    rw [abs_sub_comm y x] at h
    linarith
  · linarith [phi_le_add_dist W γ ht x y]

end SKValue

end

end OAI
