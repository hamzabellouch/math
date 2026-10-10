import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section

open scoped BigOperators

namespace SKGapCutoff

abbrev Spin (n : ℕ) := Fin n → Bool
abbrev Interaction (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def spin {n : ℕ} (x : Spin n) (i : Fin n) : ℝ := if x i then 1 else -1

def replace {n : ℕ} (x : Spin n) (i : Fin n) (b : Bool) : Spin n :=
  Function.update x i b

noncomputable def halfDiff {n : ℕ} (i : Fin n) (f : Spin n → ℝ)
    (x : Spin n) : ℝ := (f (replace x i true) - f (replace x i false)) / 2

noncomputable def field {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) : ℝ :=
  ∑ j, J i j * spin x j

noncomputable def mean {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) : ℝ :=
  Real.tanh (field J x i)

noncomputable def generator {n : ℕ} (J : Interaction n) (f : Spin n → ℝ)
    (x : Spin n) : ℝ := ∑ j, (mean J x j - spin x j) * halfDiff j f x

noncomputable def gradientGenerator {n : ℕ} (J : Interaction n)
    (p : Spin n → Fin n → ℝ) (x : Spin n) (i : Fin n) : ℝ :=
  generator J (fun y => p y i) x - p x i -
    2 * spin x i * ∑ j, halfDiff i (fun y => mean J y j) x *
      halfDiff j (fun y => p y i) x +
    ∑ j, halfDiff i (fun y => mean J y j) x * p x j

@[simp] theorem replace_same {n : ℕ} (x : Spin n) (i : Fin n) (b : Bool) :
    replace x i b i = b := by
  simp [replace]

@[simp] theorem replace_replace {n : ℕ} (x : Spin n) (i : Fin n) (a b : Bool) :
    replace (replace x i a) i b = replace x i b := by
  simp [replace, Function.update_idem]

@[simp] theorem replace_self {n : ℕ} (x : Spin n) (i : Fin n) :
    replace x i (x i) = x := by
  simp [replace]

theorem replace_comm {n : ℕ} (x : Spin n) {i j : Fin n} (h : i ≠ j)
    (a b : Bool) : replace (replace x i a) j b = replace (replace x j b) i a := by
  exact Function.update_comm h a b x

@[simp] theorem halfDiff_replace {n : ℕ} (i : Fin n) (f : Spin n → ℝ)
    (x : Spin n) (b : Bool) : halfDiff i f (replace x i b) = halfDiff i f x := by
  simp [halfDiff]

@[simp] theorem halfDiff_self {n : ℕ} (i : Fin n) (f : Spin n → ℝ)
    (x : Spin n) : halfDiff i (halfDiff i f) x = 0 := by
  simp [halfDiff]

theorem halfDiff_mul {n : ℕ} (i : Fin n) (f g : Spin n → ℝ) (x : Spin n) :
    halfDiff i (fun y => f y * g y) x =
      f x * halfDiff i g x + g x * halfDiff i f x -
        2 * spin x i * halfDiff i f x * halfDiff i g x := by
  have hx : replace x i (x i) = x := replace_self x i
  cases h : x i <;> simp only [h] at hx
  · simp only [halfDiff, spin, h, Bool.false_eq_true, ↓reduceIte]
    rw [hx]
    ring
  · simp only [halfDiff, spin, h, ↓reduceIte]
    rw [hx]
    ring

theorem halfDiff_comm {n : ℕ} (i j : Fin n) (f : Spin n → ℝ) (x : Spin n) :
    halfDiff i (halfDiff j f) x = halfDiff j (halfDiff i f) x := by
  by_cases h : i = j
  · subst j
    rfl
  · simp only [halfDiff]
    rw [replace_comm x h true true, replace_comm x h true false,
      replace_comm x h false true, replace_comm x h false false]
    ring

@[simp] theorem halfDiff_const {n : ℕ} (i : Fin n) (c : ℝ) (x : Spin n) :
    halfDiff i (fun _ => c) x = 0 := by
  simp [halfDiff]

theorem halfDiff_sub {n : ℕ} (i : Fin n) (f g : Spin n → ℝ) (x : Spin n) :
    halfDiff i (fun y => f y - g y) x = halfDiff i f x - halfDiff i g x := by
  simp only [halfDiff]
  ring

theorem halfDiff_sum {n : ℕ} {α : Type*} [Fintype α] (i : Fin n)
    (f : α → Spin n → ℝ) (x : Spin n) :
    halfDiff i (fun y => ∑ a, f a y) x = ∑ a, halfDiff i (f a) x := by
  simp only [halfDiff, sub_div, Finset.sum_sub_distrib, Finset.sum_div]

@[simp] theorem halfDiff_spin {n : ℕ} (i j : Fin n) (x : Spin n) :
    halfDiff i (fun y => spin y j) x = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    norm_num [halfDiff, spin]
  · simp [halfDiff, spin, replace, Function.update_of_ne (Ne.symm h), h]

theorem halfDiff_generator {n : ℕ} (J : Interaction n) (f : Spin n → ℝ)
    (x : Spin n) (i : Fin n) :
    halfDiff i (generator J f) x =
      gradientGenerator J (fun y j => halfDiff j f y) x i := by
  change halfDiff i (fun y => generator J f y) x = _
  unfold gradientGenerator
  simp only [generator, halfDiff_sum, halfDiff_mul, halfDiff_sub, halfDiff_spin]
  simp_rw [halfDiff_comm i]
  simp only [mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Fintype.sum_ite_eq, halfDiff_self, sub_zero]
  rw [Finset.mul_sum]
  simp only [mul_assoc]
  simp_rw [mul_comm (halfDiff _ f x)]
  ring

abbrev Observables (n : ℕ) := Spin n → ℝ
abbrev VectorFields (n : ℕ) := Spin n → Fin n → ℝ

noncomputable def gradientLM (n : ℕ) : Observables n →ₗ[ℝ] VectorFields n where
  toFun f x i := halfDiff i f x
  map_add' f g := by
    funext x i
    simp only [halfDiff, Pi.add_apply]
    ring
  map_smul' a f := by
    funext x i
    simp only [halfDiff, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

noncomputable def generatorLM {n : ℕ} (J : Interaction n) :
    Observables n →ₗ[ℝ] Observables n where
  toFun := generator J
  map_add' f g := by
    funext x
    simp only [generator]
    change (∑ j, (mean J x j - spin x j) *
      (gradientLM n (f + g) x j)) = _
    simp [map_add, gradientLM, generator, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext x
    simp only [generator]
    change (∑ j, (mean J x j - spin x j) *
      (gradientLM n (a • f) x j)) = _
    simp [map_smul, gradientLM, generator, mul_left_comm, Finset.mul_sum]

noncomputable def gradientGeneratorLM {n : ℕ} (J : Interaction n) :
    VectorFields n →ₗ[ℝ] VectorFields n where
  toFun := gradientGenerator J
  map_add' p q := by
    funext x i
    simp only [gradientGenerator, Pi.add_apply]
    have h1 : (fun y => p y i + q y i) =
        (fun y => p y i) + (fun y => q y i) := rfl
    rw [h1]
    change (generatorLM J ((fun y => p y i) + (fun y => q y i))) x - _ -
      2 * spin x i * (∑ j, halfDiff i (fun y => mean J y j) x *
        gradientLM n ((fun y => p y i) + (fun y => q y i)) x j) + _ = _
    simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    change generator J (fun y => p y i) x + generator J (fun y => q y i) x - _ - _ + _ = _
    simp only [gradientLM, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  map_smul' a p := by
    funext x i
    simp only [gradientGenerator, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have h1 : (fun y => a * p y i) = a • (fun y => p y i) := rfl
    rw [h1]
    change (generatorLM J (a • (fun y => p y i))) x - _ -
      2 * spin x i * (∑ j, halfDiff i (fun y => mean J y j) x *
        gradientLM n (a • (fun y => p y i)) x j) + _ = _
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    simp only [gradientLM, generatorLM, LinearMap.coe_mk, AddHom.coe_mk]
    simp_rw [mul_left_comm _ a, ← Finset.mul_sum]
    ring

noncomputable def gradientCLM (n : ℕ) : Observables n →L[ℝ] VectorFields n :=
  (gradientLM n).toContinuousLinearMap

noncomputable def generatorCLM {n : ℕ} (J : Interaction n) :
    Observables n →L[ℝ] Observables n := (generatorLM J).toContinuousLinearMap

noncomputable def gradientGeneratorCLM {n : ℕ} (J : Interaction n) :
    VectorFields n →L[ℝ] VectorFields n :=
  (gradientGeneratorLM J).toContinuousLinearMap

noncomputable def semigroup {n : ℕ} (J : Interaction n) (t : ℝ) :
    Observables n →L[ℝ] Observables n := NormedSpace.exp (t • generatorCLM J)

noncomputable def gradientSemigroup {n : ℕ} (J : Interaction n) (t : ℝ) :
    VectorFields n →L[ℝ] VectorFields n :=
  NormedSpace.exp (t • gradientGeneratorCLM J)

theorem exp_intertwine {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] E) (B : F →L[ℝ] F) (T : E →L[ℝ] F)
    (h : ∀ x, T (A x) = B (T x)) (x : E) :
    T (NormedSpace.exp A x) = NormedSpace.exp B (T x) := by
  have hp (k : ℕ) (y : E) : T ((A ^ k) y) = (B ^ k) (T y) := by
    induction k generalizing y with
    | zero => simp
    | succ k ih =>
      simp only [pow_succ', mul_apply_eq_comp, h, ih]
  have hA : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • ((A ^ k) x))
      (NormedSpace.exp A x) := by
    simpa only [NormedSpace.expSeries_apply_eq, ContinuousLinearMap.apply_apply,
      smul_apply] using
      (ContinuousLinearMap.apply ℝ E x).hasSum
        (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) A)
  have hB : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • ((B ^ k) (T x)))
      (NormedSpace.exp B (T x)) := by
    simpa only [NormedSpace.expSeries_apply_eq, ContinuousLinearMap.apply_apply,
      smul_apply] using
      (ContinuousLinearMap.apply ℝ F (T x)).hasSum
        (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) B)
  apply HasSum.unique _ hB
  simpa only [map_smul, hp] using T.hasSum hA

theorem halfDiff_semigroup {n : ℕ} (J : Interaction n) (t : ℝ)
    (f : Observables n) (x : Spin n) (i : Fin n) :
    halfDiff i (semigroup J t f) x =
      gradientSemigroup J t (fun y j => halfDiff j f y) x i := by
  have h (g : Observables n) :
      gradientCLM n ((t • generatorCLM J) g) =
        (t • gradientGeneratorCLM J) (gradientCLM n g) := by
    rw [smul_apply, map_smul, smul_apply]
    congr 1
    funext y j
    exact halfDiff_generator J g y j
  exact congrFun (congrFun
    (exp_intertwine (t • generatorCLM J) (t • gradientGeneratorCLM J)
      (gradientCLM n) h f) x) i

noncomputable def energy {n : ℕ} (J : Interaction n) (x : Spin n) : ℝ :=
  (∑ i, ∑ j, spin x i * J i j * spin x j) / 2

noncomputable def partition {n : ℕ} (J : Interaction n) : ℝ :=
  ∑ x : Spin n, Real.exp (energy J x)

noncomputable def gibbs {n : ℕ} (J : Interaction n) (x : Spin n) : ℝ :=
  Real.exp (energy J x) / partition J

noncomputable def attemptLM {n : ℕ} (J : Interaction n) :
    Observables n →L[ℝ] Observables n :=
  1 + (n : ℝ)⁻¹ • generatorCLM J

noncomputable def continuousKernel {n : ℕ} (J : Interaction n) (t : ℝ)
    (x y : Spin n) : ℝ := semigroup J t (fun z => if z = y then 1 else 0) x

noncomputable def discreteKernel {n : ℕ} (J : Interaction n) (k : ℕ)
    (x y : Spin n) : ℝ := (attemptLM J ^ k) (fun z => if z = y then 1 else 0) x

noncomputable def totalVariation {n : ℕ} (p q : Spin n → ℝ) : ℝ :=
  (∑ y, |p y - q y|) / 2

noncomputable def worstContinuous {n : ℕ} (J : Interaction n) (t : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun x => totalVariation (continuousKernel J t x) (gibbs J))

noncomputable def worstDiscrete {n : ℕ} (J : Interaction n) (k : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun x => totalVariation (discreteKernel J k x) (gibbs J))

abbrev GaussianCoordinates (n : ℕ) := (Fin n × Fin n) → ℝ

noncomputable def disorderLaw (β : ℝ) (n : ℕ) :
    MeasureTheory.Measure (GaussianCoordinates n) :=
  MeasureTheory.Measure.pi (fun _ =>
    ProbabilityTheory.gaussianReal 0 (Real.toNNReal (β ^ 2 / (n : ℝ))))

def sampledInteraction {n : ℕ} (g : GaussianCoordinates n) : Interaction n :=
  fun i j => if i = j then 0 else g (min i j, max i j)

noncomputable def cutoffTime (rate : ℝ) (n : ℕ) : ℝ := Real.log (n : ℝ) / (2 * rate)

def DisorderLimit (β : ℝ) (F : (n : ℕ) → Interaction n → ℝ) (a : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    Filter.Tendsto (fun n => (disorderLaw β n)
      {g | δ < |F n (sampledInteraction g) - a|})
      Filter.atTop (nhds 0)

def CutoffAtRate (β rate : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 →
    DisorderLimit β (fun n J => worstContinuous J ((1 - ε) * cutoffTime rate n)) 1 ∧
    DisorderLimit β (fun n J => worstContinuous J ((1 + ε) * cutoffTime rate n)) 0 ∧
    DisorderLimit β (fun n J => worstDiscrete J
      ⌊(1 - ε) * (n : ℝ) * cutoffTime rate n⌋₊) 1 ∧
    DisorderLimit β (fun n J => worstDiscrete J
      ⌈(1 + ε) * (n : ℝ) * cutoffTime rate n⌉₊) 0

@[simp] theorem sampledInteraction_diag {n : ℕ} (g : GaussianCoordinates n) (i : Fin n) :
    sampledInteraction g i i = 0 := by simp [sampledInteraction]

theorem sampledInteraction_symm {n : ℕ} (g : GaussianCoordinates n) (i j : Fin n) :
    sampledInteraction g i j = sampledInteraction g j i := by
  by_cases h : i = j
  · subst j; rfl
  · simp [sampledInteraction, h, Ne.symm h, min_comm, max_comm]

theorem partition_pos {n : ℕ} (J : Interaction n) : 0 < partition J := by
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem gibbs_pos {n : ℕ} (J : Interaction n) (x : Spin n) : 0 < gibbs J x :=
  div_pos (Real.exp_pos _) (partition_pos J)

theorem gibbs_sum {n : ℕ} (J : Interaction n) : ∑ x : Spin n, gibbs J x = 1 := by
  simp only [gibbs, ← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos J))

noncomputable def siteRefresh {n : ℕ} (J : Interaction n) (i : Fin n)
    (f : Observables n) (x : Spin n) : ℝ :=
  ((1 + mean J x i) / 2) * f (replace x i true) +
  ((1 - mean J x i) / 2) * f (replace x i false)

theorem generator_siteRefresh {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) : generator J f x = ∑ i, (siteRefresh J i f x - f x) := by
  apply Finset.sum_congr rfl
  intro i _
  have hx : replace x i (x i) = x := replace_self x i
  cases hi : x i <;> simp only [hi] at hx
  · simp only [halfDiff, spin, hi, Bool.false_eq_true, ↓reduceIte, siteRefresh]
    rw [hx]
    ring
  · simp only [halfDiff, spin, hi, ↓reduceIte, siteRefresh]
    rw [hx]
    ring

theorem attempt_apply_of_pos {n : ℕ} (hn : 0 < n) (J : Interaction n)
    (f : Observables n) (x : Spin n) :
    attemptLM J f x = (∑ i, siteRefresh J i f x) / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  change f x + (n : ℝ)⁻¹ * generator J f x = _
  rw [generator_siteRefresh, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

@[simp] theorem generator_const {n : ℕ} (J : Interaction n) (a : ℝ) (x : Spin n) :
    generator J (fun _ => a) x = 0 := by
  simp [generator]

@[simp] theorem siteRefresh_const {n : ℕ} (J : Interaction n) (i : Fin n)
    (a : ℝ) (x : Spin n) : siteRefresh J i (fun _ => a) x = a := by
  unfold siteRefresh
  ring

@[simp] theorem attempt_const {n : ℕ} (J : Interaction n) (a : ℝ) :
    attemptLM J (fun _ => a) = fun _ => a := by
  funext x
  change a + (n : ℝ)⁻¹ * generator J (fun _ => a) x = a
  simp

@[simp] theorem attempt_pow_const {n : ℕ} (J : Interaction n) (k : ℕ) (a : ℝ) :
    (attemptLM J ^ k) (fun _ => a) = fun _ => a := by
  induction k with
  | zero => simp
  | succ k ih => simp only [pow_succ', mul_apply_eq_comp, ih, attempt_const]

theorem siteRefresh_nonneg {n : ℕ} (J : Interaction n) (i : Fin n)
    (f : Observables n) (hf : ∀ x, 0 ≤ f x) (x : Spin n) :
    0 ≤ siteRefresh J i f x := by
  have hm1 : -1 ≤ mean J x i := le_of_lt (Real.neg_one_lt_tanh _)
  have hm2 : mean J x i ≤ 1 := le_of_lt (Real.tanh_lt_one _)
  exact add_nonneg (mul_nonneg (by linarith) (hf _))
    (mul_nonneg (by linarith) (hf _))

theorem attempt_nonneg {n : ℕ} (J : Interaction n) (f : Observables n)
    (hf : ∀ x, 0 ≤ f x) (x : Spin n) : 0 ≤ attemptLM J f x := by
  by_cases hn : n = 0
  · subst n
    simpa [attemptLM] using hf x
  · rw [attempt_apply_of_pos (Nat.pos_of_ne_zero hn)]
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => siteRefresh_nonneg J _ f hf x))
      (Nat.cast_nonneg n)

theorem attempt_pow_nonneg {n : ℕ} (J : Interaction n) (k : ℕ) (f : Observables n)
    (hf : ∀ x, 0 ≤ f x) (x : Spin n) : 0 ≤ (attemptLM J ^ k) f x := by
  induction k generalizing x with
  | zero => simpa using hf x
  | succ k ih =>
    simp only [pow_succ', mul_apply_eq_comp]
    exact attempt_nonneg J _ ih x

theorem discreteKernel_nonneg {n : ℕ} (J : Interaction n) (k : ℕ)
    (x y : Spin n) : 0 ≤ discreteKernel J k x y := by
  exact attempt_pow_nonneg J k _ (fun _ => by split_ifs <;> norm_num) x

theorem discreteKernel_sum {n : ℕ} (J : Interaction n) (k : ℕ) (x : Spin n) :
    ∑ y, discreteKernel J k x y = 1 := by
  have eq_one : (∑ y : Spin n, fun z => if z = y then (1 : ℝ) else 0) =
      fun _ : Spin n => (1 : ℝ) := by
    funext z
    simp
  unfold discreteKernel
  rw [← Finset.sum_apply, ← map_sum, eq_one, attempt_pow_const]

end SKGapCutoff
end

end OAI
