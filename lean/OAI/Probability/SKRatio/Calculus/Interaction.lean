import Mathlib
import OAI.Probability.SKRatio.FiniteChain.Spin

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus
abbrev Interaction (n : ℕ) := Fin n → Fin n → ℝ

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

noncomputable def generatorCLM {n : ℕ} (J : Interaction n) :
    Observables n →L[ℝ] Observables n := (generatorLM J).toContinuousLinearMap

noncomputable def semigroup {n : ℕ} (J : Interaction n) (t : ℝ) :
    Observables n →L[ℝ] Observables n := NormedSpace.exp (t • generatorCLM J)

@[simp] lemma spin_sq {n : ℕ} (x : Spin n) (i : Fin n) : spin x i ^ 2 = 1 := by
  cases h : x i <;> simp [spin, h]

lemma generator_mul {n : ℕ} (J : Interaction n) (f g : Observables n) (x : Spin n) :
    generator J (fun y => f y * g y) x =
      f x * generator J g x + g x * generator J f x +
        2 * ∑ i, (1 - mean J x i * spin x i) * halfDiff i f x * halfDiff i g x := by
  simp only [generator, halfDiff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hx := spin_sq x i
  linear_combination 2 * halfDiff i f x * halfDiff i g x * hx

lemma semigroup_hasDerivAt {n : ℕ} (J : Interaction n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => semigroup J s)
      (semigroup J t * generatorCLM J) t :=
  hasDerivAt_exp_smul_const (generatorCLM J) t

lemma semigroup_hasDerivAt' {n : ℕ} (J : Interaction n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => semigroup J s)
      (generatorCLM J * semigroup J t) t :=
  hasDerivAt_exp_smul_const' (generatorCLM J) t

lemma semigroup_apply_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => semigroup J s f) (semigroup J t (generator J f)) t := by
  simpa only [mul_apply_eq_comp, map_zero, add_zero, generatorCLM, generatorLM,
    LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk] using
    (semigroup_hasDerivAt J t).clm_apply (hasDerivAt_const t f)

lemma semigroup_apply_hasDerivAt' {n : ℕ} (J : Interaction n) (f : Observables n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => semigroup J s f) (generator J (semigroup J t f)) t := by
  simpa only [mul_apply_eq_comp, map_zero, add_zero, generatorCLM, generatorLM,
    LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk] using
    (semigroup_hasDerivAt' J t).clm_apply (hasDerivAt_const t f)

lemma semigroup_continuous {n : ℕ} (J : Interaction n) :
    Continuous (fun s : ℝ => semigroup J s) := by
  have hd : Differentiable ℝ (fun s : ℝ => semigroup J s) :=
    fun t => (semigroup_hasDerivAt J t).differentiableAt
  exact hd.continuous

@[simp] lemma semigroup_zero {n : ℕ} (J : Interaction n) : semigroup J 0 = 1 := by
  simp [semigroup]

noncomputable def jumpEnergy {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) : ℝ :=
  2 * ∑ i, (1 - mean J x i * spin x i) * (halfDiff i f x) ^ 2

lemma generator_square {n : ℕ} (J : Interaction n) (f : Observables n) :
    generator J (fun x => f x ^ 2) =
      fun x => 2 * f x * generator J f x + jumpEnergy J f x := by
  funext x
  simpa only [pow_two, mul_assoc, ← two_mul, jumpEnergy] using generator_mul J f f x

lemma spin_flip_self {n : ℕ} (x : Spin n) (i : Fin n) :
    spin (flip i x) i = -spin x i := by
  cases h : x i <;> simp [SKRatio.flip, spin, h]

lemma spin_flip {n : ℕ} (x : Spin n) (i j : Fin n) :
    spin (flip i x) j = spin x j - if j = i then 2 * spin x i else 0 := by
  by_cases h : j = i
  · subst j; rw [spin_flip_self]; simp; ring
  · simp [flip, spin, h]

lemma field_flip {n : ℕ} (J : Interaction n) (hdiag : ∀ i, J i i = 0)
    (x : Spin n) (i : Fin n) : field J (flip i x) i = field J x i := by
  simp only [field, spin_flip, mul_sub, Finset.sum_sub_distrib]
  simp [mul_ite, hdiag]

lemma hamiltonian_flip {n : ℕ} (g : Disorder n) (x : Spin n) (i : Fin n) :
    hamiltonian g 0 (flip i x) = hamiltonian g 0 x -
      2 * spin x i * field (coupling g) x i := by
  have hr : ∑ j, spin x j * coupling g j i = field (coupling g) x i := by
    simp only [field, coupling_symm, mul_comm]
  have he (y : Spin n) : hamiltonian g 0 y =
      (∑ j, ∑ k, spin y j * coupling g j k * spin y k) / 2 := by
    simp only [hamiltonian, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    simp only [spinValue, spin]
    ring
  rw [he, he]
  simp only [spin_flip, sub_mul, mul_sub, Finset.sum_sub_distrib]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, coupling_diag]
  simp only [← Finset.sum_mul, hr]
  simp only [mul_assoc, ← Finset.mul_sum, field]
  ring

lemma mass_flip {n : ℕ} (g : Disorder n) (x : Spin n) (i : Fin n) :
    mass g 0 (flip i x) = mass g 0 x * Real.exp (-2 * spin x i * field (coupling g) x i) := by
  unfold mass weight
  rw [hamiltonian_flip, Real.exp_sub, neg_mul, neg_mul, Real.exp_neg]
  ring

lemma exp_two_mul_one_sub_tanh (a : ℝ) :
    Real.exp (2 * a) * (1 - Real.tanh a) = 1 + Real.tanh a := by
  rw [Real.tanh_eq, show 2 * a = a + a by ring, Real.exp_add, Real.exp_neg]
  have he := Real.exp_pos a
  field_simp
  nlinarith

lemma exp_neg_two_mul_one_add_tanh (a : ℝ) :
    Real.exp (-2 * a) * (1 + Real.tanh a) = 1 - Real.tanh a := by
  simpa only [mul_neg, neg_mul, Real.tanh_neg, sub_neg_eq_add, sub_eq_add_neg, neg_neg] using
    exp_two_mul_one_sub_tanh (-a)

def flipRate {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) : ℝ :=
  (1 - spin x i * mean J x i) / 2

lemma mass_flip_ratio {n : ℕ} (g : Disorder n) (x : Spin n) (i : Fin n) :
    mass g 0 (flip i x) / (mass g 0 x + mass g 0 (flip i x)) =
      flipRate (coupling g) x i := by
  have hx := mass_pos g 0 x
  rw [mass_flip]
  have he := Real.exp_pos (-2 * spin x i * field (coupling g) x i)
  have hden : mass g 0 x + mass g 0 x * Real.exp (-2 * spin x i * field (coupling g) x i) ≠ 0 := by
    positivity
  apply (div_eq_iff hden).mpr
  cases hi : x i
  · have h := exp_two_mul_one_sub_tanh (field (coupling g) x i)
    simp only [flipRate, mean, spin, hi, Bool.false_eq_true, ↓reduceIte, mul_neg,
      mul_one, sub_neg_eq_add, neg_mul, neg_neg]
    linear_combination (mass g 0 x / 2) * h
  · have h := exp_neg_two_mul_one_add_tanh (field (coupling g) x i)
    simp only [flipRate, mean, spin, hi, ↓reduceIte, mul_one, one_mul]
    linear_combination (mass g 0 x / 2) * h

lemma siteKernel_apply {n : ℕ} (g : Disorder n) (i : Fin n) (f : Observables n) (x : Spin n) :
    ∑ y, siteKernel g i x y * f y =
      f x + flipRate (coupling g) x i * (f (flip i x) - f x) := by
  have hd : mass g 0 x + mass g 0 (flip i x) ≠ 0 :=
    (add_pos (mass_pos g 0 x) (mass_pos g 0 (flip i x))).ne'
  have hs : mass g 0 x / (mass g 0 x + mass g 0 (flip i x)) +
      mass g 0 (flip i x) / (mass g 0 x + mass g 0 (flip i x)) = 1 := by
    rw [← add_div, div_self hd]
  simp only [siteKernel, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← mass_flip_ratio]
  linear_combination f x * hs

lemma generator_flip {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) :
    generator J f x = ∑ i, flipRate J x i * (f (flip i x) - f x) := by
  apply Finset.sum_congr rfl
  intro i _
  have hx := replace_self x i
  cases hi : x i <;> simp only [hi] at hx
  · simp only [spin, hi, Bool.false_eq_true, ↓reduceIte, flipRate, flip, Bool.not_false,
      halfDiff]
    rw [hx]
    simp only [replace]
    ring
  · simp only [spin, hi, ↓reduceIte, flipRate, flip, Bool.not_true, halfDiff]
    rw [hx]
    simp only [replace]
    ring

theorem generator_eq_transition {n : ℕ} (g : Disorder n) (f : Observables n) (x : Spin n) :
    generator (coupling g) f x = (n : ℝ) * ((∑ y, transition g x y * f y) - f x) := by
  by_cases hn : n = 0
  · subst n; simp [generator]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hP : transition g = fun x y => (∑ i, siteKernel g i x y) / (n : ℝ) := by
    simp only [transition, hn, ↓reduceIte]
    rfl
  rw [hP]
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [mul_sub, mul_div_cancel₀ _ hn']
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [siteKernel_apply]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [generator_flip]
  ring

def unweightedGradient {n : ℕ} (f : Observables n) (x : Spin n) : ℝ :=
  ∑ i, (halfDiff i f x) ^ 2

def gradientWeight {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) : ℝ :=
  1 - spin x i * mean J x i

def weightedGradient {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) : ℝ :=
  ∑ i, gradientWeight J x i * (halfDiff i f x)^2

lemma variance_density {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) :
    generator J (fun y => f y ^ 2) x - 2 * f x * generator J f x =
      2 * weightedGradient J f x := by
  rw [generator_square]
  simp only [jumpEnergy, weightedGradient, gradientWeight, mul_comm (mean J x _)]
  ring

lemma halfDiff_flow_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n)
    (i : Fin n) (x : Spin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => halfDiff i (semigroup J s f) x)
      (halfDiff i (generator J (semigroup J t f)) x) t := by
  have h := semigroup_apply_hasDerivAt' J f t
  exact ((hasDerivAt_pi.mp h (replace x i true)).sub
    (hasDerivAt_pi.mp h (replace x i false))).div_const 2

lemma unweightedGradient_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => unweightedGradient (semigroup J s f) x)
      (∑ i, 2 * halfDiff i (semigroup J t f) x *
        halfDiff i (generator J (semigroup J t f)) x) t := by
  have hs := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (halfDiff_flow_hasDerivAt J f i x t).pow 2)
  simpa only [unweightedGradient, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply] using hs

lemma generator_unweightedGradient {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) :
    generator J (unweightedGradient f) x =
      ∑ i, generator J (fun y => halfDiff i f y ^ 2) x := by
  have hu : unweightedGradient f = ∑ i, (fun y => halfDiff i f y ^ 2) := by
    funext y; simp only [unweightedGradient, Finset.sum_apply]
  rw [hu]
  change generatorLM J (∑ i, (fun y => halfDiff i f y ^ 2)) x = _
  simp only [map_sum, Finset.sum_apply]
  rfl

lemma unweightedGradient_commutator {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) :
    (1 / 2 : ℝ) * ((∑ i, 2 * halfDiff i f x * halfDiff i (generator J f) x) -
      generator J (unweightedGradient f) x) =
    -unweightedGradient f x +
      (∑ i, ∑ j, halfDiff i f x * halfDiff i (fun y => mean J y j) x *
        (halfDiff j f x - 2 * spin x i * halfDiff i (halfDiff j f) x)) -
      (∑ i, ∑ j, gradientWeight J x j * (halfDiff i (halfDiff j f) x)^2) := by
  rw [generator_unweightedGradient, ← Finset.sum_sub_distrib, Finset.mul_sum]
  have hloc (i : Fin n) :
      (1 / 2 : ℝ) * (2 * halfDiff i f x * halfDiff i (generator J f) x -
        generator J (fun y => halfDiff i f y ^ 2) x) =
      -(halfDiff i f x)^2 +
        (∑ j, halfDiff i f x * halfDiff i (fun y => mean J y j) x *
          (halfDiff j f x - 2 * spin x i * halfDiff i (halfDiff j f) x)) -
        ∑ j, gradientWeight J x j * (halfDiff i (halfDiff j f) x)^2 := by
    have hsum : (∑ j, halfDiff i f x * halfDiff i (fun y => mean J y j) x *
        (halfDiff j f x - 2 * spin x i * halfDiff i (halfDiff j f) x)) =
        halfDiff i f x * (∑ j, halfDiff i (fun y => mean J y j) x * halfDiff j f x) -
          2 * halfDiff i f x * spin x i *
            (∑ j, halfDiff i (fun y => mean J y j) x * halfDiff i (halfDiff j f) x) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum, halfDiff_generator, generator_square]
    simp only [gradientGenerator, jumpEnergy, gradientWeight]
    simp_rw [halfDiff_comm _ i, mul_comm (mean J x _)]
    ring
  simp_rw [hloc]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    unweightedGradient]

end SKRatio.Calculus
end
end

end OAI
