import Mathlib
import OAI.Probability.SKValue.Equations.AdmissibleZero

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

lemma controlPayoff_convex {W : BrownianSpace} (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) {α : ℝ≥0 → W.Ω → ℝ} (hα : Admissible W t α) :
    ConvexOn ℝ univ (fun x ↦ controlPayoff W γ t x α) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  rw [controlPayoff_eq W γ ht, controlPayoff_eq W γ ht, controlPayoff_eq W γ ht]
  have hxI := controlPayoff_integrable γ ht x hα
  have hyI := controlPayoff_integrable γ ht y hα
  rw [← integral_const_mul a, ← integral_const_mul b, ← integral_add (hxI.const_mul _) (hyI.const_mul _)]
  apply integral_mono (controlPayoff_integrable γ ht (a*x+b*y) hα)
    ((hxI.const_mul _).add (hyI.const_mul _))
  intro ω
  dsimp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  let q := W.B 1 ω-W.B t.toNNReal ω+controlIntegral γ t α 1 ω
  have he : a*x+b*y+q = a*(x+q)+b*(y+q) := by
    calc
      _ = a*x+b*y+(a+b)*q := by rw [hab,one_mul]
      _ = _ := by ring
  have hh : |a*x+b*y+q|≤a*|x+q|+b*|y+q| := by
    rw [he]
    calc
      _ ≤ |a*(x+q)|+|b*(y+q)| := abs_add_le _ _
      _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
  dsimp [q] at hh
  have hc : a*((1/2 : ℝ)*controlIntegral γ t α 2 ω)+
      b*((1/2 : ℝ)*controlIntegral γ t α 2 ω) = (1/2 : ℝ)*controlIntegral γ t α 2 ω := by
    rw [← add_mul,hab,one_mul]
  simp only [add_assoc] at hh ⊢
  nlinarith

lemma phi_convex (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) : ConvexOn ℝ univ (phi W γ t) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  apply csSup_le (control_values_nonempty W γ t (a*x+b*y))
  rintro r ⟨α,hα,rfl⟩
  have hh := (controlPayoff_convex γ ht hα).2 (mem_univ x) (mem_univ y) ha hb hab
  simp only [smul_eq_mul] at hh
  apply hh.trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (le_csSup (control_values_bddAbove W γ ht x) ⟨α,hα,rfl⟩) ha
  · exact mul_le_mul_of_nonneg_left (le_csSup (control_values_bddAbove W γ ht y) ⟨α,hα,rfl⟩) hb

lemma brownian_increment_memLp (W : BrownianSpace) (t : ℝ) :
    MemLp (fun ω ↦ W.B 1 ω-W.B t.toNNReal ω) 2 W.μ :=
  (W.brownian.hasLaw_sub 1 t.toNNReal).hasGaussianLaw.memLp (by norm_num)

lemma brownian_increment_second (W : BrownianSpace) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    (∫ ω, (W.B 1 ω-W.B t.toNNReal ω)^2 ∂W.μ)=1-t := by
  have h := (W.brownian.hasLaw_sub 1 t.toNNReal).integral_comp
    (f := fun x : ℝ ↦ x^2) (by fun_prop)
  change (∫ ω, (W.B 1 ω-W.B t.toNNReal ω)^2 ∂W.μ)=_ at h
  rw [h]
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := nndist ((1 : ℝ≥0) : ℝ) (t.toNNReal : ℝ))
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hv
  simp only [sub_zero] at hv
  exact hv.trans (by simp only [NNReal.coe_one, coe_nndist, Real.dist_eq, Real.coe_toNNReal t ht.1,
    abs_of_nonneg (sub_nonneg.mpr ht.2)])

lemma brownian_increment_abs_bound (W : BrownianSpace) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    (∫ ω, |W.B 1 ω-W.B t.toNNReal ω| ∂W.μ)≤Real.sqrt (1-t) := by
  have hf := brownian_increment_memLp W t
  have hab : MemLp (fun ω ↦ |W.B 1 ω-W.B t.toNNReal ω|) 2 W.μ := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hv := variance_nonneg (fun ω ↦ |W.B 1 ω-W.B t.toNNReal ω|) W.μ
  rw [variance_eq_sub hab] at hv
  simp only [Pi.pow_apply, sq_abs, brownian_increment_second W ht] at hv
  apply (Real.le_sqrt (integral_nonneg (fun _ ↦ abs_nonneg _)) (sub_nonneg.mpr ht.2)).mpr
  linarith

lemma phi_terminal_bound (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) :
    0≤phi W γ t x-|x| ∧
      phi W γ t x-|x|≤Real.sqrt (1-t)+(1/2 : ℝ)*∫ s in t..1, γ.cutoff s := by
  constructor
  · exact sub_nonneg.mpr (phi_lower W γ ht x)
  · linarith [phi_upper W γ ht x, brownian_increment_abs_bound W ht]

end SKValue

end

end OAI
