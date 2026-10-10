import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.RecordedCount
import OAI.Analysis.CoulombRadii.Localization.ShellIMS

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

def rawRMS {n : ℕ} (ψ : H1Vector n) (f : Configuration n → ℝ) : ℝ :=
  Real.sqrt (potentialForm (fun x => (f x)^2) ψ)

lemma rawRMS_nonneg {n : ℕ} (ψ : H1Vector n) (f : Configuration n → ℝ) :
    0 ≤ rawRMS ψ f := Real.sqrt_nonneg _

lemma potentialForm_nonneg {n : ℕ} (ψ : H1Vector n) (f : Configuration n → ℝ)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ potentialForm f ψ :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun x => mul_nonneg (hf x) (sq_nonneg _)))

lemma rawRMS_sq {n : ℕ} (ψ : H1Vector n) (f : Configuration n → ℝ) :
    rawRMS ψ f ^ 2 = potentialForm (fun x => (f x)^2) ψ :=
  Real.sq_sqrt (potentialForm_nonneg ψ _ (fun _ => sq_nonneg _))

lemma potentialForm_bounded_cauchy {n : ℕ} (ψ : H1Vector n)
    (f g : Configuration n → ℝ) (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C) :
    (potentialForm (fun x => f x*g x) ψ)^2 ≤
      potentialForm (fun x => (f x)^2) ψ * potentialForm (fun x => (g x)^2) ψ := by
  have hff s := boundedObservable_integrable ψ (fun x => (f x)^2) (hf.pow_const 2)
    (fun x => by rw [abs_of_nonneg (sq_nonneg _)]; simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hB x) 2) s
  have hgg s := boundedObservable_integrable ψ (fun x => (g x)^2) (hg.pow_const 2)
    (fun x => by rw [abs_of_nonneg (sq_nonneg _)]; simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hC x) 2) s
  have hfg s := boundedObservable_integrable ψ (fun x => f x*g x) (hf.mul hg)
    (fun x => by rw [abs_mul]; exact mul_le_mul (hB x) (hC x) (abs_nonneg _) ((abs_nonneg _).trans (hB x))) s
  let A := potentialForm (fun x => (f x)^2) ψ
  let Q := potentialForm (fun x => (g x)^2) ψ
  let D := potentialForm (fun x => f x*g x) ψ
  have hn (t : ℝ) : 0 ≤ A*(t*t)+(-2*D)*t+Q := by
    have hp := potentialForm_nonneg ψ (fun x => (t*f x-g x)^2) (fun _ => sq_nonneg _)
    have he s : (∫ x, (t*f x-g x)^2*‖ψ.value s x‖^2) =
        t^2*(∫ x, (f x)^2*‖ψ.value s x‖^2)-
        (2*t)*(∫ x, (f x*g x)*‖ψ.value s x‖^2)+
        (∫ x, (g x)^2*‖ψ.value s x‖^2) := by
      have hi : Integrable (fun x => t^2*((f x)^2*‖ψ.value s x‖^2)-(2*t)*((f x*g x)*‖ψ.value s x‖^2)) :=
        ((hff s).const_mul (t^2)).sub ((hfg s).const_mul (2*t))
      calc
        _ = ∫ x, (t^2*((f x)^2*‖ψ.value s x‖^2)-(2*t)*((f x*g x)*‖ψ.value s x‖^2))+
            (g x)^2*‖ψ.value s x‖^2 := integral_congr_ae (Eventually.of_forall (fun _ => by ring))
        _ = _ := by
          rw [integral_add hi (hgg s),
            integral_sub ((hff s).const_mul _) ((hfg s).const_mul _),integral_const_mul,integral_const_mul]
    simp only [potentialForm,he,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum] at hp
    change 0 ≤ t^2*A-2*t*D+Q at hp
    nlinarith
  have H := discrim_le_zero hn
  unfold discrim at H
  change D^2 ≤ A*Q
  nlinarith

lemma rawRMS_add {n : ℕ} (ψ : H1Vector n)
    (f g : Configuration n → ℝ) (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C) :
    rawRMS ψ (fun x => f x+g x) ≤ rawRMS ψ f+rawRMS ψ g := by
  have hff s := boundedObservable_integrable ψ (fun x => (f x)^2) (hf.pow_const 2)
    (fun x => by rw [abs_of_nonneg (sq_nonneg _)]; simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hB x) 2) s
  have hgg s := boundedObservable_integrable ψ (fun x => (g x)^2) (hg.pow_const 2)
    (fun x => by rw [abs_of_nonneg (sq_nonneg _)]; simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hC x) 2) s
  have hfg s := boundedObservable_integrable ψ (fun x => f x*g x) (hf.mul hg)
    (fun x => by rw [abs_mul]; exact mul_le_mul (hB x) (hC x) (abs_nonneg _) ((abs_nonneg _).trans (hB x))) s
  have he : rawRMS ψ (fun x => f x+g x)^2 =
      rawRMS ψ f^2+2*potentialForm (fun x => f x*g x) ψ+rawRMS ψ g^2 := by
    simp only [rawRMS_sq,potentialForm]
    rw [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have hi : Integrable (fun x => (f x)^2*‖ψ.value s x‖^2+2*((f x*g x)*‖ψ.value s x‖^2)) :=
      (hff s).add ((hfg s).const_mul 2)
    calc
      _ = ∫ x, ((f x)^2*‖ψ.value s x‖^2+2*((f x*g x)*‖ψ.value s x‖^2))+
          (g x)^2*‖ψ.value s x‖^2 := integral_congr_ae (Eventually.of_forall (fun _ => by ring))
      _ = _ := by rw [integral_add hi (hgg s),
        integral_add (hff s) ((hfg s).const_mul _),integral_const_mul]
  have hcs := potentialForm_bounded_cauchy ψ f g hf hg hB hC
  rw [←rawRMS_sq,←rawRMS_sq] at hcs
  have H : potentialForm (fun x => f x*g x) ψ ≤ rawRMS ψ f*rawRMS ψ g := by
    have hh : |potentialForm (fun x => f x*g x) ψ| ≤ rawRMS ψ f*rawRMS ψ g :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (rawRMS_nonneg ψ f) (rawRMS_nonneg ψ g))).mp
        (by simpa only [sq_abs,mul_pow] using hcs)
    exact (le_abs_self _).trans hh
  nlinarith [rawRMS_nonneg ψ f,rawRMS_nonneg ψ g,rawRMS_nonneg ψ (fun x => f x+g x)]

lemma rawRMS_const_mul {n : ℕ} (ψ : H1Vector n) (f : Configuration n → ℝ)
    {c : ℝ} (hc : 0 ≤ c) : rawRMS ψ (fun x => c*f x)=c*rawRMS ψ f := by
  unfold rawRMS potentialForm
  have he : (∑ s : Spins n, ∫ x, (c*f x)^2*‖ψ.value s x‖^2)=
      c^2*(∑ s : Spins n, ∫ x, (f x)^2*‖ψ.value s x‖^2) := by
    simp only [mul_pow,mul_assoc,integral_const_mul,←Finset.mul_sum]
  rw [he,Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc]

lemma rawRMS_const {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1) {c : ℝ} (hc : 0≤c) :
    rawRMS ψ (fun _ => c)=c := by
  unfold rawRMS
  rw [potentialForm_const,hm,mul_one,Real.sqrt_sq hc]

lemma rawRMS_mono {n : ℕ} (ψ : H1Vector n)
    (f g : Configuration n → ℝ) (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C)
    (hf0 : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x) : rawRMS ψ f ≤ rawRMS ψ g := by
  apply Real.sqrt_le_sqrt
  apply potentialForm_mono_bounded ψ _ _ (hf.pow_const 2) (hg.pow_const 2)
    (fun x => by rw [abs_of_nonneg (sq_nonneg _)]; simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hB x) 2)
    (fun x => by rw [abs_of_nonneg (sq_nonneg _)]; simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hC x) 2)
  exact fun x => pow_le_pow_left₀ (hf0 x) (hfg x) 2

end Coulomb
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology
noncomputable section
namespace Coulomb

def ShellLabels (n : ℕ) : ℕ → Type
  | 0 => Unit
  | k+1 => ShellLabels n k × (Fin n → Fin 2)

instance shellLabelsFintype (n k : ℕ) : Fintype (ShellLabels n k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ k ih => exact inferInstanceAs (Fintype (ShellLabels n k × (Fin n → Fin 2)))

def shellVector {n : ℕ} (ψ : H1Vector n) (y : Space)
    (r : ℕ → {r : ℝ // 0<r}) : (k : ℕ) → ShellLabels n k → H1Vector n
  | 0, _ => ψ
  | k+1, p => (shellVector ψ y r k p.1).labelCut (radialCut y (r k).val)
      (radialCut_smooth y _) (radialCut_partition y _)
      (radialCutCoefficient/(r k).val)
      (div_nonneg radialCutCoefficient_pos.le (r k).property.le)
      (radialCut_derivative_bound y (r k).property) p.2

theorem shellVector_conserves {n : ℕ} (ψ : H1Vector n) (y : Space)
    (r : ℕ → {r : ℝ // 0<r}) (k : ℕ) (V : Configuration n → ℝ)
    (hV : Measurable V) {B : ℝ} (hB : ∀ x, |V x|≤B) :
    (∑ p : ShellLabels n k, potentialForm V (shellVector ψ y r k p)) = potentialForm V ψ := by
  induction k with
  | zero =>
    have : Unique (ShellLabels n 0) := inferInstanceAs (Unique Unit)
    simp only [Fintype.sum_unique, shellVector]
  | succ k ih =>
    change (∑ p : ShellLabels n k × (Fin n → Fin 2), _) = _
    rw [Fintype.sum_prod_type]
    simp_rw [shellVector,potentialForm_labelCut _ _ _ _ _ _ _ V hV hB]
    exact ih

lemma shellVector_population {n : ℕ} (ψ : H1Vector n) (y : Space)
    (r : ℕ → {r : ℝ // 0<r}) (k : ℕ) {A : Set Space} (hA : MeasurableSet A) :
    (∑ p : ShellLabels n k, expectedPopulation (shellVector ψ y r k p) A) =
      expectedPopulation ψ A := by
  simp only [expectedPopulation_eq _ hA]
  exact shellVector_conserves ψ y r k (localCount A) (localCount_measurable hA)
    (fun x => by rw [abs_of_nonneg (localCount_nonneg A x)]; exact localCount_le A x)

theorem shellVector_form_le {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n)
    (y : Space) (r : ℕ → {r : ℝ // 0<r}) (k : ℕ) :
    (∑ p : ShellLabels n k, form S (shellVector ψ y r k p)) ≤
      form S ψ + ∑ j ∈ Finset.range k,
        3*(radialCutCoefficient/(r j).val)^2*expectedPopulation ψ (imsShell y (r j).val) := by
  induction k with
  | zero =>
    have : Unique (ShellLabels n 0) := inferInstanceAs (Unique Unit)
    simp only [Fintype.sum_unique, shellVector, Finset.range_zero, Finset.sum_empty, add_zero, le_refl]
  | succ k ih =>
    change (∑ p : ShellLabels n k × (Fin n → Fin 2), _) ≤ _
    rw [Fintype.sum_prod_type]
    calc
      _ ≤ ∑ p : ShellLabels n k, (form S (shellVector ψ y r k p) +
          3*(radialCutCoefficient/(r k).val)^2*
            expectedPopulation (shellVector ψ y r k p) (imsShell y (r k).val)) := by
        apply Finset.sum_le_sum
        intro p hp
        exact form_radial_labelCut_shell S (shellVector ψ y r k p) y (r k).property
      _ = (∑ p : ShellLabels n k, form S (shellVector ψ y r k p)) +
          3*(radialCutCoefficient/(r k).val)^2*expectedPopulation ψ (imsShell y (r k).val) := by
        rw [Finset.sum_add_distrib,←Finset.mul_sum,
          shellVector_population ψ y r k (measurableSet_imsShell _ _)]
      _ ≤ _ := by rw [Finset.sum_range_succ]; linarith

end Coulomb
end

end

end OAI
