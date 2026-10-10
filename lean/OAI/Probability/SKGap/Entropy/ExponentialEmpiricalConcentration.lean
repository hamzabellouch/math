import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianRankCorrection

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKGapCutoff.Regression

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

omit [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma integrable_bounded_lipschitz {F : Type*} [PseudoMetricSpace F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [IsProbabilityMeasure μ]
    {f : F → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (B : ℝ) (hB : ∀ x, |f x| ≤ B) : Integrable f μ := by
  apply Integrable.of_bound hf.continuous.measurable.aestronglyMeasurable B
  exact Filter.Eventually.of_forall (by simpa only [Real.norm_eq_abs] using hB)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma lipschitz_slice_right {f : E × ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (x : E) : LipschitzWith K (fun z => f (x,z)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using
    hf.dist_le_mul (x,z) (x,w)

omit [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma gaussian_average_bound {f : E × ℝ → ℝ} (B : ℝ)
    (hB : ∀ z, |f z| ≤ B) (x : E) :
    |∫ z, f (x,z) ∂gaussianReal 0 1| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1)
    (C := B) (f := fun z => f (x,z))
    (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hB (x,z)))
  simpa using h

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma gaussian_average_lipschitz {f : E × ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (B : ℝ) (hB : ∀ z, |f z| ≤ B) :
    LipschitzWith K (fun x => ∫ z, f (x,z) ∂gaussianReal 0 1) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hix := integrable_bounded_lipschitz (gaussianReal 0 1)
    (lipschitz_slice_right hf x) B (fun z => hB (x,z))
  have hiy := integrable_bounded_lipschitz (gaussianReal 0 1)
    (lipschitz_slice_right hf y) B (fun z => hB (y,z))
  rw [Real.dist_eq, ← integral_sub hix hiy]
  have hi := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1)
    (C := (K:ℝ)*dist x y) (f := fun z => f (x,z)-f (y,z))
    (Filter.Eventually.of_forall (fun z => by
      simpa only [Real.norm_eq_abs, ← Real.dist_eq, Prod.dist_eq, dist_self,
        max_eq_left (dist_nonneg)] using hf.dist_le_mul (x,z) (y,z)))
  simpa using hi

def ExponentialEmpiricalConcentration {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) (X : ∀ n, H n → Fin n → E) (ν : Measure E) : Prop :=
  ∀ (f : E → ℝ) (K : ℝ≥0), LipschitzWith K f → ∀ B : ℝ,
    (∀ x, |f x| ≤ B) → ∀ ε : ℝ, 0 < ε →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n in atTop,
      ρ n {h | ε ≤ |(∑ i, f (X n h i))/(n:ℝ) - ∫ x, f x ∂ν|} ≤
        ENNReal.ofReal (C * Real.exp (-c*(n:ℝ)))

theorem adaptive_empirical_extension_tail {n r : ℕ} (hn : 0 < n)
    {H : Type*} [MeasurableSpace H] (ρ : Measure H) [IsProbabilityMeasure ρ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (X : H → Fin n → E) (hXm : Measurable X)
    (U : H → Fin n → Fin r → ℝ) (q : H → Fin n → ℝ)
    (hUm : Measurable U) (hqm : Measurable q)
    (hU : ∀ h a, ∑ i, U h i a^2 ≤ 1) (hq : ∀ h, ∑ i, q h i^2 ≤ 1)
    (f : E × ℝ → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ z, |f z| ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    (ρ.prod (standardArrayLaw (Fin n ⊕ Unit))) {z | ε ≤
      |(∑ i, f (X z.1 i, Real.sqrt n *
          queryInnovation (residualProjection (U z.1)) (q z.1) z.2 i))/(n:ℝ) -
        ∫ w, f w ∂ν.prod (gaussianReal 0 1)|} ≤
      ρ {h | ε/2 ≤ |(∑ i, ∫ x, f (X h i,x) ∂gaussianReal 0 1)/(n:ℝ) -
        ∫ x, ∫ z, f (x,z) ∂gaussianReal 0 1 ∂ν|} +
      (2 * ENNReal.ofReal (Real.exp (-(ε^2*(n:ℝ))/(32*B^2))) +
      (2*(r+2) : ℝ≥0∞) * ENNReal.ofReal
        (Real.exp (-((n:ℝ)*ε^2)/(256*((K:ℝ)+1)^2*((r:ℝ)+2)^2)))) := by
  let ψ : E → ℝ := fun x => ∫ z, f (x,z) ∂gaussianReal 0 1
  let M := ∫ x, ψ x ∂ν
  let A (h : H) := (∑ i, ψ (X h i))/(n:ℝ)
  let C (z : H × ((Fin n ⊕ Unit) → ℝ)) :=
    (∑ i, f (X z.1 i, Real.sqrt n *
      queryInnovation (residualProjection (U z.1)) (q z.1) z.2 i))/(n:ℝ)
  have hMean : ∫ w, f w ∂ν.prod (gaussianReal 0 1) = M :=
    integral_prod f (integrable_bounded_lipschitz _ hf B hbound)
  rw [hMean]
  have hi := adaptive_queryInnovation_empirical_tail hn ρ U q hUm hqm hU hq
    (fun h i z => f (X h i,z))
    (fun i => hf.continuous.measurable.comp
      (((measurable_pi_apply i).comp (hXm.comp measurable_fst)).prodMk measurable_snd))
    (fun h i => lipschitz_slice_right hf (X h i)) B hB
    (fun h i z => hbound (X h i,z)) (ε/2) (by positivity)
  have hi' : (ρ.prod (standardArrayLaw (Fin n ⊕ Unit))) {z | ε/2 ≤ |C z-A z.1|} ≤
      2 * ENNReal.ofReal (Real.exp (-(ε^2*(n:ℝ))/(32*B^2))) +
      (2*(r+2) : ℝ≥0∞) * ENNReal.ofReal
        (Real.exp (-((n:ℝ)*ε^2)/(256*((K:ℝ)+1)^2*((r:ℝ)+2)^2))) := by
    have he1 : -((ε/2)^2*(n:ℝ))/(8*B^2) = -(ε^2*(n:ℝ))/(32*B^2) := by ring
    have he2 : -((n:ℝ)*(ε/2)^2)/(64*((K:ℝ)+1)^2*((r:ℝ)+2)^2) =
        -((n:ℝ)*ε^2)/(256*((K:ℝ)+1)^2*((r:ℝ)+2)^2) := by
      simp only [div_mul_eq_div_div]
      ring
    simpa only [C, A, ψ, sub_div, he1, he2] using hi

  have hs : {z | ε ≤ |C z-M|} ⊆
      ({h | ε/2 ≤ |A h-M|} ×ˢ Set.univ) ∪ {z | ε/2 ≤ |C z-A z.1|} := by
    intro z hz
    by_cases ha : ε/2 ≤ |A z.1-M|
    · exact Or.inl ⟨ha,Set.mem_univ _⟩
    apply Or.inr
    by_contra hc
    have ht := abs_add_le (C z-A z.1) (A z.1-M)
    rw [sub_add_sub_cancel] at ht
    exact (not_lt_of_ge hz) (ht.trans_lt (by
      have ha' := lt_of_not_ge ha
      have hc' : |C z-A z.1| < ε/2 := lt_of_not_ge hc
      linarith))
  exact (measure_mono hs).trans ((measure_union_le _ _).trans (by
    rw [Measure.prod_prod, measure_univ, mul_one]
    exact add_le_add le_rfl hi'))

theorem ExponentialEmpiricalConcentration.adaptive_gaussian
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) [∀ n, IsProbabilityMeasure (ρ n)]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (X : ∀ n, H n → Fin n → E) (hXm : ∀ n, Measurable (X n))
    (hX : ExponentialEmpiricalConcentration ρ X ν) (r : ℕ)
    (U : ∀ n, H n → Fin n → Fin r → ℝ) (q : ∀ n, H n → Fin n → ℝ)
    (hUm : ∀ n, Measurable (U n)) (hqm : ∀ n, Measurable (q n))
    (hU : ∀ n h a, ∑ i, U n h i a^2 ≤ 1) (hq : ∀ n h, ∑ i, q n h i^2 ≤ 1) :
    ExponentialEmpiricalConcentration
      (fun n => (ρ n).prod (standardArrayLaw (Fin n ⊕ Unit)))
      (fun n z i => (X n z.1 i, Real.sqrt n *
        queryInnovation (residualProjection (U n z.1)) (q n z.1) z.2 i))
      (ν.prod (gaussianReal 0 1)) := by
  intro f K hf B hbound ε hε
  let ψ : E → ℝ := fun x => ∫ z, f (x,z) ∂gaussianReal 0 1
  obtain ⟨C,c,hC,hc,hold⟩ := hX ψ K (gaussian_average_lipschitz hf B hbound)
    B (gaussian_average_bound B hbound) (ε/2) (by positivity)
  let B' := |B|+1
  have hB' : 0 < B' := by dsimp [B']; positivity
  have hb' : ∀ z, |f z| ≤ B' := fun z => (hbound z).trans (by
    dsimp [B']; linarith [le_abs_self B])
  let a := ε^2/(32*B'^2)
  let b := ε^2/(256*((K:ℝ)+1)^2*((r:ℝ)+2)^2)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  let c' := min c (min a b)
  have hc' : 0 < c' := lt_min hc (lt_min ha hb)
  let C' := C+2+2*((r:ℝ)+2)
  refine ⟨C',c',by dsimp [C']; positivity,hc',?_⟩
  filter_upwards [hold, eventually_ge_atTop 1] with n hn hpos
  have hnpos : 0 < n := hpos
  have ht := adaptive_empirical_extension_tail hnpos (ρ n) ν (X n) (hXm n)
    (U n) (q n) (hUm n) (hqm n) (hU n) (hq n) f hf B' hB'.le hb' ε hε
  have hnew := ht.trans (add_le_add hn le_rfl)
  refine hnew.trans ?_
  have he1 : Real.exp (-c*(n:ℝ)) ≤ Real.exp (-c'*(n:ℝ)) :=
    Real.exp_le_exp.mpr (by
      have hcc : c' ≤ c := min_le_left _ _
      nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have he2 : Real.exp (-(ε^2*(n:ℝ))/(32*B'^2)) ≤ Real.exp (-c'*(n:ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hca : c' ≤ a := (min_le_right c (min a b)).trans (min_le_left a b)
    have heq : -(ε^2*(n:ℝ))/(32*B'^2) = -a*(n:ℝ) := by dsimp [a]; ring
    rw [heq]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have he3 : Real.exp (-((n:ℝ)*ε^2)/(256*((K:ℝ)+1)^2*((r:ℝ)+2)^2)) ≤
      Real.exp (-c'*(n:ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hcb : c' ≤ b := (min_le_right c (min a b)).trans (min_le_right a b)
    have heq : -((n:ℝ)*ε^2)/(256*((K:ℝ)+1)^2*((r:ℝ)+2)^2) = -b*(n:ℝ) := by
      dsimp [b]; ring
    rw [heq]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have h1 : ENNReal.ofReal (C*Real.exp (-c*(n:ℝ))) ≤
      ENNReal.ofReal (C*Real.exp (-c'*(n:ℝ))) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left he1 hC.le)
  have h2 : (2:ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(ε^2*(n:ℝ))/(32*B'^2))) ≤
      2 * ENNReal.ofReal (Real.exp (-c'*(n:ℝ))) := by
    gcongr
  have h3 : (2*(r+2):ℝ≥0∞) * ENNReal.ofReal
      (Real.exp (-((n:ℝ)*ε^2)/(256*((K:ℝ)+1)^2*((r:ℝ)+2)^2))) ≤
      (2*(r+2):ℝ≥0∞) * ENNReal.ofReal (Real.exp (-c'*(n:ℝ))) := by
    gcongr
  refine (add_le_add h1 (add_le_add h2 h3)).trans_eq ?_
  dsimp [C']
  rw [add_mul, add_mul, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
    ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2*((r:ℝ)+2))]
  norm_num [ENNReal.ofReal_add, ENNReal.ofReal_mul, add_assoc]

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise

end

end OAI
