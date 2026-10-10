import Mathlib
import OAI.Probability.SKGap.Gaussian.ReplicaTailWeight

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
namespace SKGapCutoff.RandomMatrix

local instance : ENNReal.HolderTriple 8 8 4 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
  norm_num [ENNReal.toReal_add]⟩
local instance : ENNReal.HolderTriple 4 4 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
  norm_num [ENNReal.toReal_add]⟩

lemma matrix_opNorm_sq_le_frobenius {n : ℕ} (A : Interaction n) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖^2 ≤ ∑ i, ∑ j, A i j^2 := by
  let S := ∑ i, ∑ j, A i j^2
  have hS : 0 ≤ S := by unfold S; positivity
  have hN : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ ≤ Real.sqrt S := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ Real.sqrt S * ‖x‖)).mp
    rw [mul_pow, Real.sq_sqrt hS]
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    change ∑ i, (∑ j, A i j*x j)^2 ≤ S * ∑ j, x j^2
    calc
      _ ≤ ∑ i, (∑ j, A i j^2)*(∑ j, x j^2) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) x)
      _ = _ := by rw [← Finset.sum_mul]
  exact (pow_le_pow_left₀ (norm_nonneg _) hN 2).trans_eq (Real.sq_sqrt hS)

lemma matrix_fourth_trace_bound {n : ℕ} (A : Interaction n) (hA : ∀ i j, A i j = A j i) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖^4 ≤
      ∑ i, ∑ j, ∑ k, ∑ l, A i j*A j k*A k l*A l i := by
  have hstar : A.conjTranspose = A := by ext i j; simpa using hA j i
  have he : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (A*A)‖ =
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖^2 := by
    simpa only [Matrix.cstar_norm_def, hstar, pow_two] using Matrix.l2_opNorm_conjTranspose_mul_self A
  have hh := matrix_opNorm_sq_le_frobenius (A*A)
  rw [he, ← pow_mul] at hh
  convert! hh using 1
  simp only [Matrix.mul_apply, pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm (f := fun j k => ∑ l, A i j*A j k*A k l*A l i)]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  rw [hA k l, hA l i]
  ring

lemma gaussian_sq_integral (v : ℝ≥0) : ∫ x : ℝ, x^2 ∂gaussianReal 0 v = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa only [integral_id_gaussianReal, sub_zero] using h

lemma gaussian_squared_centered_integral (v : ℝ≥0) :
    ∫ x : ℝ, (x^2-(v:ℝ)) ∂gaussianReal 0 v = 0 := by
  have h2 : Integrable (fun x : ℝ => x^2) (gaussianReal 0 v) := by
    have h : MemLp (fun x : ℝ => x*x) 1 (gaussianReal 0 v) :=
      (memLp_id_gaussianReal' (μ := 0) (v := v) 2 (by norm_num)).mul (memLp_id_gaussianReal' 2 (by norm_num))
    simpa only [pow_two] using h.integrable (le_refl 1)
  rw [integral_sub h2 (integrable_const _), gaussian_sq_integral]
  simp

lemma gaussian_squared_centered_memLp_four (v : ℝ≥0) :
    MemLp (fun x : ℝ => x^2-(v:ℝ)) 4 (gaussianReal 0 v) := by
  have h : MemLp (fun x : ℝ => x*x) 4 (gaussianReal 0 v) :=
    (memLp_id_gaussianReal' (μ := 0) (v := v) 8 (by norm_num)).mul
      (memLp_id_gaussianReal' 8 (by norm_num))
  convert! h.sub (memLp_const (v:ℝ)) using 1; (ext x; simp only [pow_two, Pi.sub_apply])

noncomputable def squaredGaussianFourth : ℝ := ∫ x : ℝ, (x^2-1)^4 ∂gaussianReal 0 1

lemma squaredGaussianFourth_nonneg : 0 ≤ squaredGaussianFourth := by
  apply integral_nonneg
  intro x
  positivity

lemma gaussian_squared_fourth_integral (v : ℝ≥0) :
    ∫ x : ℝ, (x^2-(v:ℝ))^4 ∂gaussianReal 0 v = (v:ℝ)^4*squaredGaussianFourth := by
  have hm : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v*x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp only [NNReal.coe_mk, mul_one,
        Real.sq_sqrt v.coe_nonneg]
  rw [← hm, integral_map (by fun_prop) (by fun_prop)]
  have he (x : ℝ) : ((Real.sqrt v*x)^2-(v:ℝ))^4 = (v:ℝ)^4*(x^2-1)^4 := by
    rw [mul_pow, Real.sq_sqrt v.coe_nonneg]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  rfl

def centeredSquareCoordinate {ι : Type*} (v : ℝ≥0) (i : ι) (g : ι → ℝ) : ℝ := g i^2-(v:ℝ)

def centeredSquared {n : ℕ} (v : ℝ≥0) (g : GaussianCoordinates n) : Interaction n :=
  fun i j => if i = j then 0 else centeredSquareCoordinate v (min i j, max i j) g

lemma centeredSquared_diag {n : ℕ} (v : ℝ≥0) (g : GaussianCoordinates n) (i : Fin n) :
    centeredSquared v g i i = 0 := by simp [centeredSquared]

lemma centeredSquared_symm {n : ℕ} (v : ℝ≥0) (g : GaussianCoordinates n) (i j : Fin n) :
    centeredSquared v g i j = centeredSquared v g j i := by
  simp only [centeredSquared, eq_comm, min_comm i j, max_comm i j]

lemma centeredSquareCoordinate_memLp {ι : Type*} [Fintype ι] (v : ℝ≥0) (i : ι) :
    MemLp (centeredSquareCoordinate v i) 4 (Measure.pi (fun _ : ι => gaussianReal 0 v)) :=
  (gaussian_squared_centered_memLp_four v).comp_measurePreserving
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 v) i)

lemma centeredSquareCoordinate_mean {ι : Type*} [Fintype ι] (v : ℝ≥0) (i : ι) :
    ∫ g, centeredSquareCoordinate v i g ∂Measure.pi (fun _ : ι => gaussianReal 0 v) = 0 := by
  change ∫ g, (g i^2-(v:ℝ)) ∂Measure.pi (fun _ : ι => gaussianReal 0 v) = 0
  convert! ((measurePreserving_eval (fun _ : ι => gaussianReal 0 v) i).hasLaw.integral_comp
    (show AEStronglyMeasurable (fun x : ℝ => x^2-(v:ℝ)) (gaussianReal 0 v) from by fun_prop)).trans
      (gaussian_squared_centered_integral v) using 1

lemma centeredSquareCoordinate_fourth {ι : Type*} [Fintype ι] (v : ℝ≥0) (i : ι) :
    ∫ g, (centeredSquareCoordinate v i g)^4 ∂Measure.pi (fun _ : ι => gaussianReal 0 v) =
      (v:ℝ)^4*squaredGaussianFourth := by
  change ∫ g, (g i^2-(v:ℝ))^4 ∂Measure.pi (fun _ : ι => gaussianReal 0 v) = _
  convert! ((measurePreserving_eval (fun _ : ι => gaussianReal 0 v) i).hasLaw.integral_comp
    (show AEStronglyMeasurable (fun x : ℝ => (x^2-(v:ℝ))^4) (gaussianReal 0 v) from by fun_prop)).trans
      (gaussian_squared_fourth_integral v) using 1

lemma centeredSquareCoordinate_independent {ι : Type*} [Fintype ι] (v : ℝ≥0) :
    iIndepFun (centeredSquareCoordinate (ι := ι) v) (Measure.pi (fun _ : ι => gaussianReal 0 v)) := by
  exact (iIndepFun_pi (fun _ : ι => measurable_id.aemeasurable)).comp
    (fun _ (x : ℝ) => x^2-(v:ℝ)) (fun _ => by fun_prop)

lemma centeredSquared_memLp {n : ℕ} (v : ℝ≥0) (i j : Fin n) :
    MemLp (fun g : GaussianCoordinates n => centeredSquared v g i j) 4
      (Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 v)) := by
  by_cases h : i = j
  · subst j; simpa only [centeredSquared_diag] using (memLp_const (0:ℝ))
  · simpa only [centeredSquared, h, ite_false] using
      centeredSquareCoordinate_memLp v (min i j, max i j)

lemma centeredSquared_fourth_integrable {n : ℕ} (v : ℝ≥0) (i j : Fin n) :
    Integrable (fun g : GaussianCoordinates n => centeredSquared v g i j^4)
      (Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 v)) := by
  simpa only [Real.norm_eq_abs, (show Even (4:ℕ) by decide).pow_abs] using
    (centeredSquared_memLp v i j).integrable_norm_pow (by decide : (4:ℕ) ≠ 0)

lemma centeredSquared_fourth_le {n : ℕ} (v : ℝ≥0) (i j : Fin n) :
    ∫ g : GaussianCoordinates n, centeredSquared v g i j^4
      ∂(Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 v)) ≤
        (v:ℝ)^4*squaredGaussianFourth := by
  by_cases h : i = j
  · subst j; simp only [centeredSquared_diag, zero_pow (by decide : (4:ℕ) ≠ 0), integral_zero]
    exact mul_nonneg (by positivity) squaredGaussianFourth_nonneg
  · simp only [centeredSquared, h, ite_false, centeredSquareCoordinate_fourth, le_refl]

lemma centeredSquared_cyclic_integrable {n : ℕ} (v : ℝ≥0) (i j k l : Fin n) :
    Integrable (fun g : GaussianCoordinates n => centeredSquared v g i j*centeredSquared v g j k*
      centeredSquared v g k l*centeredSquared v g l i)
      (Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 v)) := by
  have hab : MemLp (fun g : GaussianCoordinates n => centeredSquared v g i j*centeredSquared v g j k) 2
      (Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 v)) :=
    (centeredSquared_memLp v i j).mul (centeredSquared_memLp v j k)
  have hcd : MemLp (fun g : GaussianCoordinates n => centeredSquared v g k l*centeredSquared v g l i) 2
      (Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 v)) :=
    (centeredSquared_memLp v k l).mul (centeredSquared_memLp v l i)
  convert! hab.integrable_mul hcd using 1; (ext g; simp only [Pi.mul_apply]; ring)

lemma minmax_eq_iff {α : Type*} [LinearOrder α] (a b c d : α) :
    (min a b, max a b) = (min c d, max c d) ↔
      (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  constructor
  · intro h
    rcases le_total a b with hab | hab
    · rcases le_total c d with hcd | hcd
      · left; simpa only [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd,
          Prod.mk.injEq] using h
      · right; simpa only [min_eq_left hab, max_eq_right hab, min_eq_right hcd, max_eq_left hcd,
          Prod.mk.injEq] using h
    · rcases le_total c d with hcd | hcd
      · right
        have hh : b=c ∧ a=d := by
          simpa only [min_eq_right hab, max_eq_left hab,
            min_eq_left hcd, max_eq_right hcd, Prod.mk.injEq] using h
        exact ⟨hh.2, hh.1⟩
      · left
        have hh : b=d ∧ a=c := by
          simpa only [min_eq_right hab, max_eq_left hab,
            min_eq_right hcd, max_eq_left hcd, Prod.mk.injEq] using h
        exact ⟨hh.2, hh.1⟩
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rfl
    · simp only [min_comm, max_comm]

lemma integral_sq_mul_sq_le_fourth {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f g : Ω → ℝ) (hint : Integrable (fun x => f x^2*g x^2) μ)
    (hf : Integrable (fun x => f x^4) μ) (hg : Integrable (fun x => g x^4) μ) :
    (∫ x, f x^2*g x^2 ∂μ) ≤ ((∫ x, f x^4 ∂μ)+(∫ x, g x^4 ∂μ))/2 := by
  calc
    _ ≤ ∫ x, (f x^4+g x^4)/2 ∂μ := by
      apply integral_mono hint ((hf.add hg).div_const _)
      intro x
      change f x^2*g x^2 ≤ (f x^4+g x^4)/2
      nlinarith [sq_nonneg (f x^2-g x^2)]
    _ = _ := by rw [integral_div, integral_add hf hg]

lemma centeredSquared_cyclic_zero {n : ℕ} (v : ℝ≥0) (i j k l : Fin n)
    (hik : i ≠ k) (hjl : j ≠ l) :
    ∫ g : GaussianCoordinates n, centeredSquared v g i j*centeredSquared v g j k*
      centeredSquared v g k l*centeredSquared v g l i
      ∂(Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 v)) = 0 := by
  by_cases hij : i = j
  · subst j; simp [centeredSquared_diag]
  by_cases hjk : j = k
  · subst k; simp [centeredSquared_diag]
  by_cases hkl : k = l
  · subst l; simp [centeredSquared_diag]
  by_cases hli : l = i
  · subst l; simp [centeredSquared_diag]
  simp only [centeredSquared, hij, hjk, hkl, hli, ite_false]
  let e₁ := (min i j, max i j)
  let e₂ := (min j k, max j k)
  let e₃ := (min k l, max k l)
  let e₄ := (min l i, max l i)
  have h12 : e₁ ≠ e₂ := by simpa only [e₁, e₂, ne_eq, minmax_eq_iff] using
    (show ¬ ((i=j ∧ j=k) ∨ (i=k ∧ j=j)) by tauto)
  have h13 : e₁ ≠ e₃ := by simpa only [e₁, e₃, ne_eq, minmax_eq_iff] using
    (show ¬ ((i=k ∧ j=l) ∨ (i=l ∧ j=k)) by tauto)
  have h14 : e₁ ≠ e₄ := by simpa only [e₁, e₄, ne_eq, minmax_eq_iff] using
    (show ¬ ((i=l ∧ j=i) ∨ (i=i ∧ j=l)) by tauto)
  have h23 : e₂ ≠ e₃ := by simpa only [e₂, e₃, ne_eq, minmax_eq_iff] using
    (show ¬ ((j=k ∧ k=l) ∨ (j=l ∧ k=k)) by tauto)
  have h24 : e₂ ≠ e₄ := by simpa only [e₂, e₄, ne_eq, minmax_eq_iff] using
    (show ¬ ((j=l ∧ k=i) ∨ (j=i ∧ k=l)) by tauto)
  have hm (e : Fin n × Fin n) : Measurable (centeredSquareCoordinate v e) := by
    unfold centeredSquareCoordinate; fun_prop
  have hab := (centeredSquareCoordinate_independent v).indepFun h12
  have hprod := (centeredSquareCoordinate_independent v).indepFun_mul_mul hm e₁ e₂ e₃ e₄ h13 h14 h23 h24
  have he := hprod.integral_fun_mul_eq_mul_integral
    ((hm e₁).mul (hm e₂)).aestronglyMeasurable ((hm e₃).mul (hm e₄)).aestronglyMeasurable
  simp only [Pi.mul_apply] at he
  rw [hab.integral_fun_mul_eq_mul_integral (hm e₁).aestronglyMeasurable (hm e₂).aestronglyMeasurable,
    centeredSquareCoordinate_mean, zero_mul, zero_mul] at he
  simpa only [e₁, e₂, e₃, e₄, mul_assoc] using he

lemma centeredSquared_cyclic_le {n : ℕ} (v : ℝ≥0) (i j k l : Fin n) :
    ∫ g : GaussianCoordinates n, centeredSquared v g i j*centeredSquared v g j k*
      centeredSquared v g k l*centeredSquared v g l i
      ∂(Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 v)) ≤
        (if i=k then (v:ℝ)^4*squaredGaussianFourth else 0) +
        (if j=l then (v:ℝ)^4*squaredGaussianFourth else 0) := by
  have hM : 0 ≤ (v:ℝ)^4*squaredGaussianFourth := mul_nonneg (by positivity) squaredGaussianFourth_nonneg
  have hp := centeredSquared_cyclic_integrable v i j k l
  by_cases hik : i = k
  · subst k
    have he (g : GaussianCoordinates n) : centeredSquared v g i j*centeredSquared v g j i*
        centeredSquared v g i l*centeredSquared v g l i =
          centeredSquared v g i j^2*centeredSquared v g i l^2 := by
      rw [centeredSquared_symm v g j i, centeredSquared_symm v g l i]; ring
    simp_rw [he] at hp ⊢
    have hh := integral_sq_mul_sq_le_fourth (fun g => centeredSquared v g i j)
      (fun g => centeredSquared v g i l) hp (centeredSquared_fourth_integrable v i j)
      (centeredSquared_fourth_integrable v i l)
    have hb := centeredSquared_fourth_le v i j
    have hc := centeredSquared_fourth_le v i l
    simp only [ite_true]
    have hright : 0 ≤ (if j=l then (v:ℝ)^4*squaredGaussianFourth else 0) := by
      split_ifs <;> linarith
    linarith
  · by_cases hjl : j = l
    · subst l
      have he (g : GaussianCoordinates n) : centeredSquared v g i j*centeredSquared v g j k*
          centeredSquared v g k j*centeredSquared v g j i =
            centeredSquared v g i j^2*centeredSquared v g k j^2 := by
        rw [centeredSquared_symm v g j i, centeredSquared_symm v g j k]; ring
      simp_rw [he] at hp ⊢
      have hh := integral_sq_mul_sq_le_fourth (fun g => centeredSquared v g i j)
        (fun g => centeredSquared v g k j) hp (centeredSquared_fourth_integrable v i j)
        (centeredSquared_fourth_integrable v k j)
      have hb := centeredSquared_fourth_le v i j
      have hc := centeredSquared_fourth_le v k j
      simp only [hik, ite_false, ite_true, zero_add]
      linarith
    · rw [centeredSquared_cyclic_zero v i j k l hik hjl]
      simp only [hik, hjl, ite_false, add_zero, le_refl]

noncomputable def squaredFourthTrace {n : ℕ} (v : ℝ≥0) (g : GaussianCoordinates n) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, centeredSquared v g i j*centeredSquared v g j k*
    centeredSquared v g k l*centeredSquared v g l i

lemma squaredFourthTrace_integrable {n : ℕ} (v : ℝ≥0) :
    Integrable (squaredFourthTrace (n := n) v)
      (Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 v)) := by
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
      centeredSquared_cyclic_integrable v i j k l))))

lemma squaredFourthTrace_nonneg {n : ℕ} (v : ℝ≥0) (g : GaussianCoordinates n) :
    0 ≤ squaredFourthTrace v g :=
  (pow_nonneg (norm_nonneg _) 4).trans (matrix_fourth_trace_bound _ (centeredSquared_symm v g))

lemma squaredFourthTrace_integral_le {n : ℕ} (v : ℝ≥0) :
    ∫ g : GaussianCoordinates n, squaredFourthTrace v g
      ∂(Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 v)) ≤
        2*(n:ℝ)^3*(v:ℝ)^4*squaredGaussianFourth := by
  have hl (i j k : Fin n) := integrable_finsetSum Finset.univ (fun l _ =>
    centeredSquared_cyclic_integrable v i j k l)
  have hk (i j : Fin n) := integrable_finsetSum Finset.univ (fun k _ => hl i j k)
  have hj (i : Fin n) := integrable_finsetSum Finset.univ (fun j _ => hk i j)
  unfold squaredFourthTrace
  rw [integral_finsetSum _ (fun i _ => hj i)]
  simp_rw [integral_finsetSum _ (fun j _ => hk _ j), integral_finsetSum _ (fun k _ => hl _ _ k),
    integral_finsetSum _ (fun l _ => centeredSquared_cyclic_integrable v _ _ _ l)]
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ((if i=k then (v:ℝ)^4*squaredGaussianFourth else 0) +
        (if j=l then (v:ℝ)^4*squaredGaussianFourth else 0)) := by
      exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => centeredSquared_cyclic_le v i j k l))))
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, Finset.mem_univ, ite_true,
        Finset.sum_ite_eq]
      ring

lemma centeredSquared_opNorm_tail {n : ℕ} (v : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 v))
      {g | δ < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (centeredSquared v g)‖} ≤
        ENNReal.ofReal (2*(n:ℝ)^3*(v:ℝ)^4*squaredGaussianFourth/δ^4) := by
  refine (measure_mono (show {g | δ < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (centeredSquared v g)‖} ⊆
    {g | δ^4 ≤ squaredFourthTrace v g} from ?_)).trans ?_
  · intro g hg
    exact (pow_le_pow_left₀ hδ.le hg.le 4).trans
      (matrix_fourth_trace_bound _ (centeredSquared_symm v g))
  · exact (probability_markov_real _ _ (squaredFourthTrace_integrable v)
      (squaredFourthTrace_nonneg v) (δ^4) (by positivity)).trans
        (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (squaredFourthTrace_integral_le v) (by positivity)))

lemma centeredSquared_disorder_tail (β : ℝ) {n : ℕ} (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) :
    disorderLaw β n {g | δ < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (centeredSquared (Real.toNNReal (β^2/(n:ℝ))) g)‖} ≤
        ENNReal.ofReal ((2*β^8*squaredGaussianFourth/δ^4)/(n:ℝ)) := by
  convert! centeredSquared_opNorm_tail (n := n) (Real.toNNReal (β^2/(n:ℝ))) δ hδ using 2
  rw [Real.coe_toNNReal _ (by positivity)]
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

lemma centeredSquared_disorder_tendsto (β : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => disorderLaw β n {g | δ < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (centeredSquared (Real.toNNReal (β^2/(n:ℝ))) g)‖}) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ => (2*β^8*squaredGaussianFourth/δ^4)/(n:ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  simp only [ENNReal.ofReal_zero] at hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
    (Eventually.of_forall (fun _ => bot_le))
    ((eventually_gt_atTop 0).mono (fun n hn => centeredSquared_disorder_tail β hn δ hδ))

noncomputable def sampledSquaredDeviation {n : ℕ} (β : ℝ) (g : GaussianCoordinates n) : Interaction n :=
  fun i j => (sampledInteraction g i j)^2-β^2/(n:ℝ)

lemma sampledSquaredDeviation_eq {n : ℕ} (β : ℝ) (g : GaussianCoordinates n) :
    sampledSquaredDeviation β g = centeredSquared (Real.toNNReal (β^2/(n:ℝ))) g -
      (β^2/(n:ℝ)) • (1 : Interaction n) := by
  have hv : 0 ≤ β^2/(n:ℝ) := by positivity
  ext i j
  by_cases h : i=j
  · subst j
    simp only [sampledSquaredDeviation, sampledInteraction, centeredSquared, ite_true, zero_pow (by decide : (2:ℕ) ≠ 0),
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  · simp only [sampledSquaredDeviation, sampledInteraction, centeredSquared, h, ite_false,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne h, smul_eq_mul, mul_zero,
      sub_zero, centeredSquareCoordinate, Real.coe_toNNReal _ hv]

lemma sampledSquaredDeviation_norm_le {n : ℕ} (β : ℝ) (g : GaussianCoordinates n) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledSquaredDeviation β g)‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (centeredSquared (Real.toNNReal (β^2/(n:ℝ))) g)‖ + β^2/(n:ℝ) := by
  have hv : 0 ≤ β^2/(n:ℝ) := by positivity
  rw [sampledSquaredDeviation_eq, map_sub, map_smul]
  have hone : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (1 : Interaction n)‖ ≤ 1 := by
    rw [map_one]
    change ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  calc
    _ ≤ _ + ‖(β^2/(n:ℝ)) • Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (1 : Interaction n)‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hv]
      exact add_le_add le_rfl (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hv)

lemma sampledSquaredDeviation_tendsto (β : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => disorderLaw β n {g | δ < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (sampledSquaredDeviation β g)‖}) atTop (nhds 0) := by
  have hv : Tendsto (fun n : ℕ => β^2/(n:ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have he : ∀ᶠ n : ℕ in atTop, β^2/(n:ℝ) < δ/2 := hv.eventually (gt_mem_nhds (by positivity))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (centeredSquared_disorder_tendsto β (δ/2) (by positivity))
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [he] with n hn
  apply measure_mono
  intro g hg
  have hh := sampledSquaredDeviation_norm_le β g
  change δ/2 < _
  change δ < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledSquaredDeviation β g)‖ at hg
  linarith

end SKGapCutoff.RandomMatrix

open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set

end

end OAI
