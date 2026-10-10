import Mathlib
import OAI.Probability.SKGap.Entropy.ParameterMapWeight

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
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
namespace SKGapCutoff.Regression

lemma linear_combination_lipschitz {E : Type*} [PseudoMetricSpace E]
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ) {K : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (c : ι → ℝ) :
    LipschitzWith (∑ i, ‖c i‖₊ * K) (fun x => ∑ i, c i*f i x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, ← Finset.sum_sub_distrib]
  calc
    |∑ i, (c i*f i x-c i*f i y)| ≤ ∑ i, |c i*f i x-c i*f i y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |c i| *((K:ℝ)*dist x y) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hf i |>.dist_le_mul x y) (abs_nonneg _)
    _ = _ := by simp only [NNReal.coe_sum, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs];
                rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring

lemma linear_combination_coefficient_bound {E : Type*}
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ) {B : ℝ≥0}
    (hB : ∀ i x, |f i x| ≤ B) (a c : ι → ℝ) (x : E) :
    dist (∑ i, a i*f i x) (∑ i, c i*f i x) ≤
      (Fintype.card ι:ℝ)*B*dist a c := by
  rw [Real.dist_eq, ← Finset.sum_sub_distrib]
  calc
    |∑ i, (a i*f i x-c i*f i x)| ≤ ∑ i, |a i*f i x-c i*f i x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, dist a c*(B:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← sub_mul, abs_mul]
      exact mul_le_mul (dist_le_pi_dist a c i) (hB i x) (abs_nonneg _) dist_nonneg
    _ = _ := by simp; ring

 theorem ExponentialEmpiricalConcentration.linear_combination
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E} {ν : Measure E}
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ) {K B : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (hB : ∀ i x, |f i x| ≤ B)
    (C : ∀ n, H n → ι → ℝ) (c : ι → ℝ) (hC : ExponentialConvergence ρ C c) :
    ExponentialEmpiricalConcentration ρ (fun n h a => ∑ i, C n h i*f i (X n h a))
      (ν.map (fun x => ∑ i, c i*f i x)) := by
  exact hX.parameter_map C c hC (fun c x => ∑ i, c i*f i x)
    (linear_combination_lipschitz f hf c) ((Fintype.card ι:ℝ)*B) (by positivity)
    (fun a x => linear_combination_coefficient_bound f hB a c x)

lemma integral_quadratic_expansion
    {E : Type*} [MeasurableSpace E] {ν : Measure E}
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ) (c : ι → ℝ)
    (hf : ∀ i j, Integrable (fun x => f i x*f j x) ν) :
    (∫ x, (∑ i, c i*f i x)^2 ∂ν) =
      ∑ i, ∑ j, c i*(∫ x, f i x*f j x ∂ν)*c j := by
  have hid x : (∑ i, c i*f i x)^2 = ∑ i, ∑ j, c i*(f i x*f j x)*c j := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hid]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · simp only [integral_mul_const, integral_const_mul]
    · intro j _
      exact ((hf i j).const_mul (c i)).mul_const (c j)
  · intro i _
    exact integrable_finsetSum _ (fun j _ => ((hf i j).const_mul (c i)).mul_const (c j))

lemma ExponentialEmpiricalConcentration.linear_combination_energy
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E} {ν : Measure E}
    [IsProbabilityMeasure ν] (hX : ExponentialEmpiricalConcentration ρ X ν)
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ) {K B : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (hB : ∀ i x, |f i x| ≤ B)
    (C : ∀ n, H n → ι → ℝ) (c : ι → ℝ) (hC : ExponentialConvergence ρ C c) :
    ExponentialConvergence ρ (fun n h => (∑ a, (∑ i, C n h i*f i (X n h a))^2)/(n:ℝ))
      (∫ x, (∑ i, c i*f i x)^2 ∂ν) := by
  rw [integral_quadratic_expansion f c]
  · exact hX.linear_combination_second_moment f hf hB C c hC
  · intro i j
    apply integrable_bounded_lipschitz ν
      (bounded_product_lipschitz (hf i) (hf j) (hB i) (hB j)) ((B:ℝ)^2)
    intro x
    rw [abs_mul, pow_two]
    exact mul_le_mul (hB i x) (hB j x) (abs_nonneg _) B.coe_nonneg

def residualRecipe {E ι : Type*} [Fintype ι]
    (f : ι → E → ℝ) (g : E → ℝ) (c : ι → ℝ) (x : E) : ℝ :=
  g x - ∑ i, c i*f i x

lemma ExponentialConvergence.residual_coefficients
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)] {ρ : ∀ n, Measure (H n)}
    {ι : Type*} [Fintype ι] {C : ∀ n, H n → ι → ℝ} {c : ι → ℝ}
    (hC : ExponentialConvergence ρ C c) :
    ExponentialConvergence ρ (fun n h (i : Option ι) => i.elim 1 (fun j => -C n h j))
      (fun i : Option ι => i.elim 1 (fun j => -c j)) := by
  apply hC.continuous_map (f := fun a (i : Option ι) => i.elim 1 (fun j => -a j))
  apply Continuous.continuousAt
  apply continuous_pi
  intro i
  cases i <;> simp only [Option.elim_none, Option.elim_some] <;> fun_prop

lemma residualRecipe_eq_option {E ι : Type*} [Fintype ι]
    (f : ι → E → ℝ) (g : E → ℝ) (c : ι → ℝ) (x : E) :
    residualRecipe f g c x =
      ∑ i : Option ι, i.elim 1 (fun j => -c j)*i.elim (g x) (fun j => f j x) := by
  simp [residualRecipe, Fintype.sum_option, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

lemma ExponentialEmpiricalConcentration.residual
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E} {ν : Measure E}
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ) (g : E → ℝ) {K B : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (hg : LipschitzWith K g)
    (hB : ∀ i x, |f i x| ≤ B) (hBg : ∀ x, |g x| ≤ B)
    (C : ∀ n, H n → ι → ℝ) (c : ι → ℝ) (hC : ExponentialConvergence ρ C c) :
    ExponentialEmpiricalConcentration ρ
      (fun n h a => residualRecipe f g (C n h) (X n h a))
      (ν.map (residualRecipe f g c)) := by
  change ExponentialEmpiricalConcentration ρ
    (fun n h a => residualRecipe f g (C n h) (X n h a))
    (ν.map (fun x => residualRecipe f g c x))
  have hh := hX.linear_combination
    (fun i : Option ι => i.elim g f)
    (K := K) (B := B) (fun i => by cases i <;> simp_all)
    (fun i x => by cases i <;> simp_all)
    _ _ hC.residual_coefficients
  simpa only [residualRecipe, Fintype.sum_option, Option.elim_apply, Option.elim_none,
    Option.elim_some, one_mul, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg] using hh

lemma ExponentialEmpiricalConcentration.residual_energy
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E} {ν : Measure E}
    [IsProbabilityMeasure ν] (hX : ExponentialEmpiricalConcentration ρ X ν)
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ) (g : E → ℝ) {K B : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (hg : LipschitzWith K g)
    (hB : ∀ i x, |f i x| ≤ B) (hBg : ∀ x, |g x| ≤ B)
    (C : ∀ n, H n → ι → ℝ) (c : ι → ℝ) (hC : ExponentialConvergence ρ C c) :
    ExponentialConvergence ρ
      (fun n h => (∑ a, (residualRecipe f g (C n h) (X n h a))^2)/(n:ℝ))
      (∫ x, (residualRecipe f g c x)^2 ∂ν) := by
  have hh := hX.linear_combination_energy
    (fun i : Option ι => i.elim g f)
    (K := K) (B := B) (fun i => by cases i <;> simp_all)
    (fun i x => by cases i <;> simp_all)
    _ _ hC.residual_coefficients
  simpa only [residualRecipe, Fintype.sum_option, Option.elim_apply, Option.elim_none,
    Option.elim_some, one_mul, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg] using hh

theorem ExponentialEmpiricalConcentration.normalized_residual
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E} {ν : Measure E}
    [IsProbabilityMeasure ν] (hX : ExponentialEmpiricalConcentration ρ X ν)
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ) (g : E → ℝ) {K B : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (hg : LipschitzWith K g)
    (hB : ∀ i x, |f i x| ≤ B) (hBg : ∀ x, |g x| ≤ B)
    (C : ∀ n, H n → ι → ℝ) (c : ι → ℝ) (hC : ExponentialConvergence ρ C c)
    (hs : 0 < ∫ x, (residualRecipe f g c x)^2 ∂ν) :
    ExponentialEmpiricalConcentration ρ
      (fun n h a => residualRecipe f g (C n h) (X n h a) /
        Real.sqrt ((∑ b, (residualRecipe f g (C n h) (X n h b))^2)/(n:ℝ)))
      (ν.map (fun x => residualRecipe f g c x /
        Real.sqrt (∫ y, (residualRecipe f g c y)^2 ∂ν))) := by
  let S n h := (∑ b, (residualRecipe f g (C n h) (X n h b))^2)/(n:ℝ)
  let s := ∫ x, (residualRecipe f g c x)^2 ∂ν
  have hS : ExponentialConvergence ρ S s := hX.residual_energy f g hf hg hB hBg C c hC
  have hc : ContinuousAt (fun z : (Option ι → ℝ) × ℝ =>
      fun i => z.1 i / Real.sqrt z.2)
      ((fun i : Option ι => i.elim 1 (fun j => -c j)),s) := by
    apply continuousAt_pi.mpr
    intro i
    exact (by fun_prop : Continuous (fun z : (Option ι → ℝ) × ℝ => z.1 i)).continuousAt.div
      (Real.continuous_sqrt.comp continuous_snd).continuousAt (ne_of_gt (Real.sqrt_pos.mpr hs))
  have hcoeff := (hC.residual_coefficients.prod hS).continuous_map hc
  have hh := hX.linear_combination (fun i : Option ι => i.elim g f)
    (K := K) (B := B) (fun i => by cases i <;> simp_all)
    (fun i x => by cases i <;> simp_all) _ _ hcoeff
  simp only [Option.elim_apply, Fintype.sum_option, Option.elim_none, Option.elim_some] at hh
  simpa only [residualRecipe, one_div, div_mul_eq_mul_div, neg_mul,
    ← Finset.sum_div, Finset.sum_neg_distrib, neg_div, ← sub_eq_add_neg, ← sub_div, S, s,
    inv_mul_eq_div] using hh

lemma ExponentialConvergence.positive_rare
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)] {ρ : ∀ n, Measure (H n)}
    {S : ∀ n, H n → ℝ} {s : ℝ} (hS : ExponentialConvergence ρ S s) (hs : 0 < s) :
    ExponentiallyRare ρ (fun n => {h | S n h ≤ 0}) := by
  apply (hS s hs).mono
  refine Filter.Eventually.of_forall ?_
  intro n h hh
  change S n h ≤ 0 at hh
  change s ≤ dist (S n h) s
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

lemma empirical_normalized_square {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ)
    (hv : 0 < (∑ i, (v i)^2)/(n:ℝ)) :
    (∑ i, (v i/Real.sqrt ((∑ j, (v j)^2)/(n:ℝ)))^2)/(n:ℝ) = 1 := by
  simp only [div_pow]
  rw [← Finset.sum_div, Real.sq_sqrt hv.le]
  have hn' : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hv' : (∑ i, (v i)^2) ≠ 0 := by
    intro hz
    rw [hz, zero_div] at hv
    exact (lt_irrefl 0) hv
  field_simp

noncomputable def empiricalProjection {n : ℕ} {E ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Fin n → E) (f : ι → E → ℝ) (g : E → ℝ) : ι → ℝ :=
  (show Matrix ι ι ℝ from fun i j => (∑ a, f i (x a)*f j (x a))/(n:ℝ))⁻¹ *ᵥ
    (fun i => (∑ a, f i (x a)*g (x a))/(n:ℝ))

noncomputable def limitingProjection {E ι : Type*} [MeasurableSpace E] [Fintype ι] [DecidableEq ι]
    (ν : Measure E) (f : ι → E → ℝ) (g : E → ℝ) : ι → ℝ :=
  (show Matrix ι ι ℝ from fun i j => ∫ x, f i x*f j x ∂ν)⁻¹ *ᵥ
    (fun i => ∫ x, f i x*g x ∂ν)

lemma empirical_residual_orthogonal {n : ℕ} {E ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Fin n → E) (f : ι → E → ℝ) (g : E → ℝ)
    (hdet : Matrix.det (fun i j => (∑ a, f i (x a)*f j (x a))/(n:ℝ)) ≠ 0) (i : ι) :
    (∑ a, f i (x a)*residualRecipe f g (empiricalProjection x f g) (x a))/(n:ℝ) = 0 := by
  let A : Matrix ι ι ℝ := fun i j => (∑ a, f i (x a)*f j (x a))/(n:ℝ)
  let b : ι → ℝ := fun i => (∑ a, f i (x a)*g (x a))/(n:ℝ)
  have he : A *ᵥ (A⁻¹ *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have hi := congrFun he i
  change (∑ j, A i j*(empiricalProjection x f g) j) = b i at hi
  have hexp : (∑ a, f i (x a)*residualRecipe f g (empiricalProjection x f g) (x a))/(n:ℝ) =
      b i - ∑ j, A i j*(empiricalProjection x f g) j := by
    simp only [residualRecipe, mul_sub, Finset.sum_sub_distrib, sub_div, A, b]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [div_mul_eq_mul_div, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hexp, hi, sub_self]

lemma ExponentialConvergence.nonzero_rare
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)] {ρ : ∀ n, Measure (H n)}
    {S : ∀ n, H n → ℝ} {s : ℝ} (hS : ExponentialConvergence ρ S s) (hs : s ≠ 0) :
    ExponentiallyRare ρ (fun n => {h | S n h = 0}) := by
  apply (hS |s| (abs_pos.mpr hs)).mono
  refine Filter.Eventually.of_forall ?_
  intro n h hh
  change S n h = 0 at hh
  change |s| ≤ dist (S n h) s
  simp [hh, Real.dist_eq]

lemma ExponentialEmpiricalConcentration.singular_gram_rare
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E} {ν : Measure E}
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → E → ℝ) {K B : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (hB : ∀ i x, |f i x| ≤ B)
    (hdet : Matrix.det (fun i j => ∫ x, f i x*f j x ∂ν) ≠ 0) :
    ExponentiallyRare ρ (fun n => {h |
      Matrix.det (fun i j => (∑ a, f i (X n h a)*f j (X n h a))/(n:ℝ)) = 0}) := by
  apply ExponentialConvergence.nonzero_rare _ hdet
  exact (hX.gram f hf hB).continuous_map (f := fun a : ι → ι → ℝ => Matrix.det a)
    continuous_id.matrix_det.continuousAt

theorem ExponentialEmpiricalConcentration.gram_residual
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E} {ν : Measure E}
    [IsProbabilityMeasure ν] (hX : ExponentialEmpiricalConcentration ρ X ν)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → E → ℝ) (g : E → ℝ) {K B : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (hg : LipschitzWith K g)
    (hB : ∀ i x, |f i x| ≤ B) (hBg : ∀ x, |g x| ≤ B)
    (hdet : Matrix.det (fun i j => ∫ x, f i x*f j x ∂ν) ≠ 0) :
    ExponentialEmpiricalConcentration ρ
      (fun n h a => residualRecipe f g (empiricalProjection (X n h) f g) (X n h a))
      (ν.map (residualRecipe f g (limitingProjection ν f g))) ∧
    ExponentialConvergence ρ
      (fun n h => (∑ a, (residualRecipe f g (empiricalProjection (X n h) f g) (X n h a))^2)/(n:ℝ))
      (∫ x, (residualRecipe f g (limitingProjection ν f g) x)^2 ∂ν) := by
  have hc : ExponentialConvergence ρ (fun n h => empiricalProjection (X n h) f g)
      (limitingProjection ν f g) := hX.projection_coefficients f g hf hg hB hBg hdet
  exact ⟨hX.residual f g hf hg hB hBg _ _ hc, hX.residual_energy f g hf hg hB hBg _ _ hc⟩

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology

end

end OAI
