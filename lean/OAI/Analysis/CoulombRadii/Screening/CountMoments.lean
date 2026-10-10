import Mathlib
import OAI.Analysis.CoulombRadii.Localization.ConfigSupported
import OAI.Analysis.CoulombRadii.Localization.RadialCut

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def localCount {n : ℕ} (A : Set Space) (x : Configuration n) : ℝ :=
  ∑ i : Fin n, A.indicator (fun _ => (1:ℝ)) (position x i)

lemma localCount_nonneg {n : ℕ} (A : Set Space) (x : Configuration n) : 0 ≤ localCount A x := by
  exact Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
lemma localCount_le {n : ℕ} (A : Set Space) (x : Configuration n) : localCount A x ≤ n := by
  calc
    _ ≤ ∑ _i : Fin n, (1:ℝ) := Finset.sum_le_sum (fun i _ => by
      by_cases h : position x i ∈ A <;> simp [h])
    _ = _ := by simp
lemma localCount_measurable {n : ℕ} {A : Set Space} (hA : MeasurableSet A) :
    Measurable (localCount (n:=n) A) := by
  exact Finset.measurable_fun_sum _ (fun i _ => (measurable_const.indicator hA).comp (continuous_position i).measurable)

lemma localCount_weight_integrable {n : ℕ} (ψ : H1Vector n) {A : Set Space}
    (hA : MeasurableSet A) (s : Spins n) (q : ℕ) :
    Integrable (fun x => (localCount A x)^q*‖ψ.value s x‖^2) := by
  have hw := (ψ.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)
  apply (hw.const_mul ((n:ℝ)^q)).mono'
    (((localCount_measurable hA).pow_const q).aestronglyMeasurable.mul hw.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(localCount A x)^q*‖ψ.value s x‖^2‖ ≤ (n:ℝ)^q*‖ψ.value s x‖^2
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (localCount_nonneg A x) _) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (localCount_nonneg A x) (localCount_le A x) q) (sq_nonneg _)

def localCountSecondMoment {n : ℕ} (ψ : H1Vector n) (A : Set Space) : ℝ :=
  ∑ s : Spins n, ∫ x, (localCount A x)^2*‖ψ.value s x‖^2

lemma localCountSecondMoment_nonneg {n : ℕ} (ψ : H1Vector n) (A : Set Space) :
    0 ≤ localCountSecondMoment ψ A :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))

lemma localCountSecondMoment_le {n : ℕ} (ψ : H1Vector n) (A : Set Space) :
    localCountSecondMoment ψ A ≤ (n:ℝ)^2*mass ψ := by
  unfold localCountSecondMoment mass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · filter_upwards [] with x
    positivity
  · exact ((ψ.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)).const_mul _
  · filter_upwards [] with x
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (localCount_nonneg A x) (localCount_le A x) 2) (sq_nonneg _)

lemma expectedPopulation_eq {n : ℕ} (ψ : H1Vector n) {A : Set Space} (hA : MeasurableSet A) :
    expectedPopulation ψ A = ∑ s : Spins n, ∫ x, localCount A x*‖ψ.value s x‖^2 := by
  apply Finset.sum_congr rfl
  intro s hs
  simp only [localCount,Finset.sum_mul]
  exact (integral_finsetSum _ (fun i _ => population_integrable ψ A hA s i)).symm

lemma expectedPopulation_sq_le {n : ℕ} (ψ : H1Vector n) {A : Set Space}
    (hA : MeasurableSet A) (hmass : mass ψ=1) :
    (expectedPopulation ψ A)^2 ≤ localCountSecondMoment ψ A := by
  let c := expectedPopulation ψ A
  have hn : 0 ≤ ∑ s : Spins n, ∫ x, (localCount A x-c)^2*‖ψ.value s x‖^2 :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hi (s : Spins n) :
      (∫ x, (localCount A x-c)^2*‖ψ.value s x‖^2) =
      (∫ x, (localCount A x)^2*‖ψ.value s x‖^2)-2*c*(∫ x, localCount A x*‖ψ.value s x‖^2)+
      c^2*(∫ x, ‖ψ.value s x‖^2) := by
    have h1 : Integrable (fun x => localCount A x*‖ψ.value s x‖^2) := by
      simpa using localCount_weight_integrable ψ hA s 1
    have h2 := localCount_weight_integrable ψ hA s 2
    have h0 := (ψ.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)
    have hsub : Integrable (fun x => (localCount A x)^2*‖ψ.value s x‖^2-(2*c)*(localCount A x*‖ψ.value s x‖^2)) := by
      exact h2.sub (h1.const_mul (2*c))
    calc
      _ = ∫ x, ((localCount A x)^2*‖ψ.value s x‖^2-(2*c)*(localCount A x*‖ψ.value s x‖^2))+c^2*‖ψ.value s x‖^2 :=
        integral_congr_ae (Eventually.of_forall (fun x => by ring))
      _ = _ := by
        rw [integral_add hsub (h0.const_mul _),integral_sub h2 (h1.const_mul _),
          integral_const_mul,integral_const_mul]
  simp only [hi,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] at hn
  rw [← expectedPopulation_eq ψ hA] at hn
  change 0 ≤ localCountSecondMoment ψ A-2*c*expectedPopulation ψ A+c^2*mass ψ at hn
  rw [hmass] at hn
  dsimp [c] at hn
  nlinarith

def outLabelCount {n : ℕ} (p : Fin n → Fin 2) : ℝ :=
  ∑ i : Fin n, if p i=0 then 1 else 0

lemma outLabelCount_nonneg {n : ℕ} (p : Fin n → Fin 2) : 0 ≤ outLabelCount p :=
  Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

lemma tensorCut_zero_of_outCount_lt {n : ℕ} (χ : Fin 2 → Space → ℝ)
    (p : Fin n → Fin 2) (A : Set Space) (hA : ∀ z ∉ A, χ 0 z=0)
    (x : Configuration n) (hx : localCount A x < outLabelCount p) : tensorCut χ p x=0 := by
  by_contra h
  have H (i : Fin n) : (if p i=0 then (1:ℝ) else 0) ≤ A.indicator (fun _ => (1:ℝ)) (position x i) := by
    by_cases hp : p i=0
    · have hmem : position x i ∈ A := by
        by_contra hi
        have hc : χ (p i) (position x i)=0 := by rw [hp,hA _ hi]
        exact h (Finset.prod_eq_zero (Finset.mem_univ i) hc)
      simp [hp,hmem]
    · simpa [hp] using Set.indicator_nonneg (fun _ _ => zero_le_one) (position x i)
  exact (not_lt_of_ge (Finset.sum_le_sum (fun i _ => H i))) hx

lemma tensorCut_outCount_square_le {n : ℕ} (χ : Fin 2 → Space → ℝ)
    (hp : ∀ z, ∑ l, χ l z^2=1) (A : Set Space) (hA : ∀ z ∉ A, χ 0 z=0) (x : Configuration n) :
    (∑ p : Fin n → Fin 2, (outLabelCount p)^2*(tensorCut χ p x)^2) ≤ (localCount A x)^2 := by
  calc
    _ ≤ ∑ p : Fin n → Fin 2, (localCount A x)^2*(tensorCut χ p x)^2 := by
      apply Finset.sum_le_sum
      intro p hp'
      by_cases h : outLabelCount p ≤ localCount A x
      · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (outLabelCount_nonneg p) h 2) (sq_nonneg _)
      · rw [tensorCut_zero_of_outCount_lt χ p A hA x (lt_of_not_ge h)]
        simp
    _ = _ := by rw [← Finset.mul_sum,tensorCut_partition χ hp,mul_one]

theorem labelCut_outCount_secondMoment_le {n : ℕ} (ψ : H1Vector n)
    (χ : Fin 2 → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (A : Set Space) (hA : MeasurableSet A) (hsupp : ∀ z ∉ A, χ 0 z=0) :
    (∑ p : Fin n → Fin 2, (outLabelCount p)^2*mass (ψ.labelCut χ hχ hp D hD hd p)) ≤
      localCountSecondMoment ψ A := by
  have hint (s : Spins n) (p : Fin n → Fin 2) :
      Integrable (fun x => (outLabelCount p)^2*((tensorCut χ p x)^2*‖ψ.value s x‖^2)) := by
    have hcut := ((ψ.labelCut χ hχ hp D hD hd p).value_L2 s).integrable_norm_pow (p:=2) (by norm_num)
    apply (hcut.const_mul ((outLabelCount p)^2)).congr
    filter_upwards [] with x
    simp only [H1Vector.labelCut,H1Vector.smoothMul,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  unfold mass localCountSecondMoment
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro s hs
  simp only [← integral_const_mul]
  have he (p : Fin n → Fin 2) :
      (fun x => (outLabelCount p)^2*‖(ψ.labelCut χ hχ hp D hD hd p).value s x‖^2) =
      (fun x => (outLabelCount p)^2*((tensorCut χ p x)^2*‖ψ.value s x‖^2)) := by
    funext x
    simp only [H1Vector.labelCut,H1Vector.smoothMul,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  simp_rw [he]
  rw [← integral_finsetSum _ (fun p _ => hint s p)]
  apply integral_mono (integrable_finsetSum _ (fun p _ => hint s p)) (localCount_weight_integrable ψ hA s 2)
  intro x
  simp only [← mul_assoc,← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (tensorCut_outCount_square_le χ hp A hsupp x) (sq_nonneg _)

end Coulomb
end

end
end

end OAI
