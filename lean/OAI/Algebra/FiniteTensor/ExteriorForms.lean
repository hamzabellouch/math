import Mathlib

namespace OAI

/-! Exterior forms, differentials, Koszul operators and residue pairings. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Forms
noncomputable section
open scoped TensorProduct BigOperators

variable (K A σ : Type*) [Field K] [CommRing A] [Algebra K A]
  [Fintype σ] [DecidableEq σ]

abbrev E := ExteriorAlgebra K (σ → K)
abbrev Ω := A ⊗[K] E K σ

def dx (i : σ) : E K σ := ExteriorAlgebra.ι K (Pi.single i 1)
def scalar (a : A) : Ω K A σ := a ⊗ₜ[K] (1 : E K σ)
def parity : Ω K A σ →ₐ[K] Ω K A σ :=
  Algebra.TensorProduct.map (AlgHom.id K A) CliffordAlgebra.involute

def oneForm (v : σ → A) : Ω K A σ := ∑ i, v i ⊗ₜ[K] dx K σ i

variable {K A σ}

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem parity_tmul (a : A) (e : E K σ) :
    parity K A σ (a ⊗ₜ[K] e) = a ⊗ₜ[K] CliffordAlgebra.involute e := rfl

omit [Fintype σ] in
@[simp] theorem parity_dx (i : σ) :
    CliffordAlgebra.involute (dx K σ i) = -dx K σ i := by
  exact CliffordAlgebra.involute_ι _

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem parity_parity (ω : Ω K A σ) :
    parity K A σ (parity K A σ ω) = ω := by
  induction ω using TensorProduct.inductionOn with
  | tmul a e => simp
  | add a b ha hb => simp [ha, hb]

omit [Fintype σ] [DecidableEq σ] in
theorem exterior_anticommute (v : σ → K) (e : E K σ) :
    ExteriorAlgebra.ι K v * e = CliffordAlgebra.involute e * ExteriorAlgebra.ι K v := by
  induction e using ExteriorAlgebra.induction with
  | algebraMap r => simp [Algebra.commutes]
  | ι w =>
    rw [CliffordAlgebra.involute_ι, neg_mul]
    exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap v w)
  | mul a b ha hb =>
    rw [map_mul, ← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]
  | add a b ha hb => simp [mul_add, add_mul, ha, hb]

theorem oneForm_anticommute (v : σ → A) (ω : Ω K A σ) :
    oneForm K A σ v * ω = parity K A σ ω * oneForm K A σ v := by
  induction ω using TensorProduct.inductionOn with
  | tmul a e =>
    simp only [oneForm, Finset.sum_mul, Finset.mul_sum, parity_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm (v i) a, dx, exterior_anticommute]
  | add a b ha hb => simp [mul_add, add_mul, ha, hb]

@[simp] theorem parity_oneForm (v : σ → A) :
    parity K A σ (oneForm K A σ v) = -oneForm K A σ v := by
  simp only [oneForm, map_sum, parity_tmul, parity_dx, TensorProduct.tmul_neg,
    Finset.sum_neg_distrib]

theorem oneForm_sq_zero [Invertible (2 : K)] (v : σ → A) :
    oneForm K A σ v * oneForm K A σ v = 0 := by
  have h := oneForm_anticommute v (oneForm K A σ v)
  rw [parity_oneForm, neg_mul] at h
  have h2 : (2 : K) • (oneForm K A σ v * oneForm K A σ v) = 0 := by
    rw [two_smul K]
    exact eq_neg_iff_add_eq_zero.mp h
  exact (isUnit_of_invertible (2 : K)).smul_eq_zero.mp h2

variable (K A σ)
 
def differential (der : σ → A →ₗ[K] A) : Ω K A σ →ₗ[K] Ω K A σ :=
  ∑ i, TensorProduct.map (der i) (LinearMap.mulLeft K (dx K σ i))

variable {K A σ}
@[simp] theorem differential_tmul (der : σ → A →ₗ[K] A) (a : A) (e : E K σ) :
    differential K A σ der (a ⊗ₜ[K] e) = ∑ i, der i a ⊗ₜ[K] (dx K σ i * e) := by
  simp [differential]

@[simp] theorem differential_scalar (der : σ → A →ₗ[K] A) (a : A) :
    differential K A σ der (scalar K A σ a) = oneForm K A σ (fun i => der i a) := by
  simp [scalar, oneForm]

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem parity_scalar (a : A) : parity K A σ (scalar K A σ a) = scalar K A σ a := by
  simp [scalar]

theorem differential_mul (der : σ → A →ₗ[K] A)
    (hder : ∀ i a b, der i (a*b) = der i a * b + a * der i b)
    (ω η : Ω K A σ) :
    differential K A σ der (ω*η) = differential K A σ der ω * η +
      parity K A σ ω * differential K A σ der η := by
  induction ω using TensorProduct.inductionOn with
  | add a b ha hb => simp only [add_mul, map_add, ha, hb]; abel
  | tmul a e =>
    induction η using TensorProduct.inductionOn with
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]; abel
    | tmul b f =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, differential_tmul,
        Finset.sum_mul, Finset.mul_sum, parity_tmul, hder, TensorProduct.add_tmul]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [dx, ← mul_assoc, exterior_anticommute (Pi.single i 1) e]

theorem differential_parity (der : σ → A →ₗ[K] A) (ω : Ω K A σ) :
    differential K A σ der (parity K A σ ω) = -parity K A σ (differential K A σ der ω) := by
  induction ω using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]; abel
  | tmul a e =>
    simp only [parity_tmul, differential_tmul, map_sum, map_mul, parity_dx,
      neg_mul, TensorProduct.tmul_neg, Finset.sum_neg_distrib, neg_neg]

theorem differential_sq_zero [Invertible (2 : K)] (der : σ → A →ₗ[K] A)
    (hder : ∀ i j a, der i (der j a) = der j (der i a)) (ω : Ω K A σ) :
    differential K A σ der (differential K A σ der ω) = 0 := by
  induction ω using TensorProduct.inductionOn with
  | add a b ha hb => simp [ha, hb]
  | tmul a e =>
    have hanti : ∀ i j, dx K σ i * dx K σ j = -(dx K σ j * dx K σ i) := by
      intro i j
      exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
    have heq : differential K A σ der (differential K A σ der (a ⊗ₜ[K] e)) =
        -differential K A σ der (differential K A σ der (a ⊗ₜ[K] e)) := by
      simp only [differential_tmul, map_sum]
      conv_rhs => rw [Finset.sum_comm]
      simp only [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hder j i a, ← mul_assoc, hanti j i, neg_mul, TensorProduct.tmul_neg, mul_assoc]
    exact (isUnit_of_invertible (2 : K)).smul_eq_zero.mp (by
      rw [two_smul K]
      exact eq_neg_iff_add_eq_zero.mp heq)

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem scalar_mul (a b : A) : scalar K A σ (a*b) = scalar K A σ a * scalar K A σ b := by
  simp [scalar, Algebra.TensorProduct.tmul_mul_tmul]

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem scalar_add (a b : A) : scalar K A σ (a+b) = scalar K A σ a + scalar K A σ b := by
  simp [scalar, TensorProduct.add_tmul]

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem scalar_zero : scalar K A σ 0 = 0 := by simp [scalar]
omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem scalar_one : scalar K A σ 1 = 1 := by
  exact Algebra.TensorProduct.one_def.symm

omit [Fintype σ] [DecidableEq σ] in
theorem scalar_commute (a : A) (ω : Ω K A σ) : scalar K A σ a * ω = ω * scalar K A σ a := by
  induction ω using TensorProduct.inductionOn with
  | add b c hb hc => simp [mul_add, add_mul, hb, hc]
  | tmul b e => simp [scalar, Algebra.TensorProduct.tmul_mul_tmul, mul_comm a b]

variable (K A σ)
 
def contraction (i : σ) : Ω K A σ →ₗ[K] Ω K A σ :=
  TensorProduct.map LinearMap.id (CliffordAlgebra.contractLeft (LinearMap.proj i))

variable {K A σ}
omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem contraction_tmul (i : σ) (a : A) (e : E K σ) :
    contraction K A σ i (a ⊗ₜ[K] e) =
      a ⊗ₜ[K] CliffordAlgebra.contractLeft (LinearMap.proj i) e := rfl

theorem contraction_oneForm_mul (i : σ) (v : σ → A) (ω : Ω K A σ) :
    contraction K A σ i (oneForm K A σ v * ω) =
      scalar K A σ (v i) * ω - oneForm K A σ v * contraction K A σ i ω := by
  induction ω using TensorProduct.inductionOn with
  | add a b ha hb => simp only [mul_add, map_add, ha, hb]; abel
  | tmul a e =>
    simp only [oneForm, Finset.sum_mul, map_sum, Algebra.TensorProduct.tmul_mul_tmul,
      contraction_tmul, dx, CliffordAlgebra.contractLeft_ι_mul, LinearMap.proj_apply,
      TensorProduct.tmul_sub, TensorProduct.tmul_smul, Finset.sum_sub_distrib]
    congr 1
    simp [Pi.single_apply, scalar, Algebra.TensorProduct.tmul_mul_tmul]

theorem gradient_multiple_boundary (v : σ → A) (ω : Ω K A σ)
    (hω : oneForm K A σ v * ω = 0) (a : σ → A) :
    scalar K A σ (∑ i, a i * v i) * ω ∈ LinearMap.range (LinearMap.mulLeft K (oneForm K A σ v)) := by
  refine ⟨∑ i, scalar K A σ (a i) * contraction K A σ i ω, ?_⟩
  simp only [LinearMap.mulLeft_apply, Finset.mul_sum]
  have hi : ∀ i, oneForm K A σ v * contraction K A σ i ω = scalar K A σ (v i) * ω := by
    intro i
    have h := contraction_oneForm_mul i v ω
    rw [hω, map_zero] at h
    exact (sub_eq_zero.mp h.symm).symm
  have hsc : scalar K A σ (∑ i, a i*v i) = ∑ i, scalar K A σ (a i*v i) := by
    simp [scalar, TensorProduct.sum_tmul]
  rw [hsc, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc, ← scalar_commute, mul_assoc, hi, ← mul_assoc, ← scalar_mul]

variable (K A σ)
 
def normalFactor (der : σ → A →ₗ[K] A) (p : ℕ) (c : A) : Ω K A σ :=
  scalar K A σ (c^(p-1)) * differential K A σ der (scalar K A σ c)

def normalCycle (der : σ → A →ₗ[K] A) (p : ℕ) (cs : List A) : Ω K A σ :=
  (cs.map (normalFactor K A σ der p)).prod

variable {K A σ}
variable [Invertible (2 : K)]
variable (der : σ → A →ₗ[K] A)
  (hleib : ∀ i a b, der i (a*b) = der i a*b + a*der i b)
  (hcomm : ∀ i j a, der i (der j a) = der j (der i a))

omit [Fintype σ] [DecidableEq σ] [Invertible (2 : K)] in
include hleib in
private theorem deriv_one_eq_zero (i : σ) : der i 1 = 0 := by
  have h := hleib i 1 1
  simp only [mul_one, one_mul] at h
  exact add_left_cancel (show der i 1 + der i 1 = der i 1 + 0 by simpa using h.symm)

omit [Invertible (2 : K)] in
include hleib in
@[simp] theorem differential_one : differential K A σ der 1 = 0 := by
  rw [← scalar_one, differential_scalar]
  simp [oneForm, deriv_one_eq_zero der hleib]

include hleib in
theorem differential_power_mul_self (c : A) (r : ℕ) :
    differential K A σ der (scalar K A σ (c^r)) *
      differential K A σ der (scalar K A σ c) = 0 := by
  have hs : differential K A σ der (scalar K A σ c) *
      differential K A σ der (scalar K A σ c) = 0 := by
    rw [differential_scalar]
    exact oneForm_sq_zero _
  induction r with
  | zero => simp [differential_one der hleib]
  | succ r ih =>
    rw [pow_succ, scalar_mul, differential_mul der hleib, parity_scalar, add_mul,
      ← scalar_commute c, mul_assoc, ih, mul_zero, zero_add,
      mul_assoc, hs, mul_zero]

include hleib hcomm in
theorem normalFactor_closed (p : ℕ) (c : A) :
    differential K A σ der (normalFactor K A σ der p c) = 0 := by
  rw [normalFactor, differential_mul der hleib, differential_sq_zero der hcomm,
    mul_zero, add_zero]
  exact differential_power_mul_self der hleib c _

include hleib hcomm in
theorem normalCycle_closed (p : ℕ) (cs : List A) :
    differential K A σ der (normalCycle K A σ der p cs) = 0 := by
  induction cs with
  | nil => simp [normalCycle, differential_one der hleib]
  | cons c cs ih =>
    change differential K A σ der (normalFactor K A σ der p c * normalCycle K A σ der p cs) = 0
    rw [differential_mul der hleib, normalFactor_closed der hleib hcomm, ih]
    simp

 
omit [Invertible (2 : K)] in
theorem normalFactor_scalar_ann (p : ℕ) (hp : 0<p) (c : A) (hc : c^p=0) :
    scalar K A σ c * normalFactor K A σ der p c = 0 := by
  rw [normalFactor, ← mul_assoc, ← scalar_mul, ← pow_succ', Nat.sub_add_cancel hp,
    hc, scalar_zero, zero_mul]

theorem normalFactor_dscalar_ann (p : ℕ) (c : A) :
    differential K A σ der (scalar K A σ c) * normalFactor K A σ der p c = 0 := by
  rw [normalFactor, ← mul_assoc, ← scalar_commute, mul_assoc, differential_scalar,
    oneForm_sq_zero, mul_zero]

omit [Invertible (2 : K)] in
theorem normalCycle_scalar_ann (p : ℕ) (hp : 0<p) (cs : List A)
    (hnil : ∀ c∈cs, c^p=0) (c : A) (hc : c∈cs) :
    scalar K A σ c * normalCycle K A σ der p cs = 0 := by
  induction cs with
  | nil => simp at hc
  | cons a cs ih =>
    change scalar K A σ c * (normalFactor K A σ der p a * normalCycle K A σ der p cs) = 0
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [← mul_assoc, normalFactor_scalar_ann der p hp c (hnil c (by simp)), zero_mul]
    · rw [← mul_assoc, scalar_commute, mul_assoc, ih (fun b hb => hnil b (by simp [hb])) hc,
        mul_zero]

theorem normalCycle_dscalar_ann (p : ℕ) (cs : List A) (c : A) (hc : c∈cs) :
    differential K A σ der (scalar K A σ c) * normalCycle K A σ der p cs = 0 := by
  induction cs with
  | nil => simp at hc
  | cons a cs ih =>
    change differential K A σ der (scalar K A σ c) *
      (normalFactor K A σ der p a * normalCycle K A σ der p cs) = 0
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [← mul_assoc, normalFactor_dscalar_ann, zero_mul]
    · rw [← mul_assoc, differential_scalar, oneForm_anticommute, mul_assoc,
        ← differential_scalar, ih hc, mul_zero]

include hleib in
 

theorem normalCycle_ideal_ann (p : ℕ) (hp : 0<p) (cs : List A)
    (hnil : ∀ c∈cs, c^p=0) (S : A) (hS : S ∈ Ideal.span {c | c∈cs}) :
    scalar K A σ S * normalCycle K A σ der p cs = 0 ∧
      differential K A σ der (scalar K A σ S) * normalCycle K A σ der p cs = 0 := by
  induction hS using Submodule.span_induction with
  | mem c hc => exact ⟨normalCycle_scalar_ann der p hp cs hnil c hc,
      normalCycle_dscalar_ann der p cs c hc⟩
  | zero => simp
  | add a b ha hb iha ihb =>
    simp only [scalar_add, map_add, add_mul, iha.1, ihb.1, iha.2, ihb.2, zero_add]
    trivial
  | smul a b hb ih =>
    change scalar K A σ (a*b) * _ = 0 ∧ differential K A σ der (scalar K A σ (a*b)) * _ = 0
    rw [scalar_mul, mul_assoc, ih.1, mul_zero]
    constructor
    · rfl
    · rw [differential_mul der hleib, add_mul, mul_assoc, ih.1, mul_zero,
        mul_assoc, ih.2, mul_zero, zero_add]

 
omit [Invertible (2 : K)] in
theorem gradient_ideal_boundary (v : σ → A) (ω : Ω K A σ)
    (hω : oneForm K A σ v * ω = 0) (a : A) (ha : a ∈ Ideal.span (Set.range v)) :
    scalar K A σ a * ω ∈ LinearMap.range (LinearMap.mulLeft K (oneForm K A σ v)) := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp ha
  rw [← hb]
  exact gradient_multiple_boundary v ω hω b

 
omit [Invertible (2 : K)] in
theorem oneForm_mul_zero_iff (v : σ → A) (ω : Ω K A σ) :
    oneForm K A σ v * ω = 0 ↔ ω * oneForm K A σ v = 0 := by
  constructor
  · intro h
    have he := congrArg (parity K A σ) h
    simp only [map_mul, parity_oneForm, map_zero, neg_mul, neg_eq_zero] at he
    rw [oneForm_anticommute, parity_parity] at he
    exact he
  · intro h
    rw [oneForm_anticommute]
    have he := congrArg (parity K A σ) h
    simpa only [map_mul, parity_oneForm, map_zero, mul_neg, neg_eq_zero] using he

 
omit [Invertible (2 : K)] in
theorem boundary_mul_cycle_zero (v : σ → A) (ω η : Ω K A σ)
    (hω : ω ∈ LinearMap.range (LinearMap.mulLeft K (oneForm K A σ v)))
    (hη : oneForm K A σ v * η = 0) : ω * η = 0 := by
  obtain ⟨β, rfl⟩ := hω
  change (oneForm K A σ v * β) * η = 0
  rw [oneForm_anticommute, mul_assoc, hη, mul_zero]

end
end PD4Tensor.Forms
end

end OAI
