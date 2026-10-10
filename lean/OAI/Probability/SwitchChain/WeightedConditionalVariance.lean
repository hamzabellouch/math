import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.WeightedConditional

variable {Ω ι β : Type*} [Fintype Ω] [sectionFintypeι : Fintype ι] [sectionFintypeβ : Fintype β]
  [sectionDecidableEqβ : DecidableEq β]

def conditionalSum (w : Ω → ℝ) (key : ι → Ω → β)
    (i : ι) (t : β) (f : Ω → ℝ) : ℝ :=
  ∑ x, if key i x = t then w x * f x else 0

include sectionFintypeι in
theorem sum_mul_conditionalSum (w : Ω → ℝ) (key : ι → Ω → β)
    (i : ι) (g : β → ℝ) (f : Ω → ℝ) :
    (∑ t, g t * conditionalSum w key i t f) =
      ∑ x, w x * g (key i x) * f x := by
  have retainedsectionFintypeι := sectionFintypeι
  classical
  unfold conditionalSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  ring

theorem sum_conditionalSum (w : Ω → ℝ) (key : ι → Ω → β)
    (i : ι) (f : Ω → ℝ) :
    (∑ t, conditionalSum w key i t f) = ∑ x, w x * f x := by
  simpa using sum_mul_conditionalSum w key i (fun _ => 1) f

include sectionFintypeι sectionFintypeβ in
theorem conditionalSum_add (w : Ω → ℝ) (key : ι → Ω → β)
    (i : ι) (t : β) (f g : Ω → ℝ) :
    conditionalSum w key i t (fun x => f x + g x) =
      conditionalSum w key i t f + conditionalSum w key i t g := by
  have retainedsectionFintypeι := sectionFintypeι
  have retainedsectionFintypeβ := sectionFintypeβ
  unfold conditionalSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  split <;> simp_all [mul_add]

include sectionFintypeι sectionFintypeβ in
theorem conditionalSum_smul (w : Ω → ℝ) (key : ι → Ω → β)
    (i : ι) (t : β) (c : ℝ) (f : Ω → ℝ) :
    conditionalSum w key i t (fun x => c * f x) =
      c * conditionalSum w key i t f := by
  have retainedsectionFintypeι := sectionFintypeι
  have retainedsectionFintypeβ := sectionFintypeβ
  unfold conditionalSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  split <;> simp_all [mul_left_comm]

abbrev Space (ι β : Type*) [Fintype ι] [Fintype β] :=
  EuclideanSpace ℝ (ι × β)

def decode (p : ι → β → ℝ) (z : Space ι β) (i : ι) (t : β) : ℝ :=
  z (i, t) / Real.sqrt (p i t)

def rowSum (p : ι → β → ℝ) (key : ι → Ω → β) (z : Space ι β) (x : Ω) : ℝ :=
  ∑ i, decode p z i (key i x)

def gram (w : Ω → ℝ) (p : ι → β → ℝ) (key : ι → Ω → β) :
    Space ι β →ₗ[ℝ] Space ι β where
  toFun z := WithLp.toLp 2 (fun it =>
    conditionalSum w key it.1 it.2 (rowSum p key z) / Real.sqrt (p it.1 it.2))
  map_add' z z' := by
    ext it
    change conditionalSum w key it.1 it.2 (rowSum p key (z + z')) /
      Real.sqrt (p it.1 it.2) = _
    have hs : rowSum p key (z + z') = fun x => rowSum p key z x + rowSum p key z' x := by
      funext x
      simp [rowSum, decode, add_div, Finset.sum_add_distrib]
    rw [hs, conditionalSum_add, add_div]
    rfl
  map_smul' c z := by
    ext it
    change conditionalSum w key it.1 it.2 (rowSum p key (c • z)) /
      Real.sqrt (p it.1 it.2) = c * _
    have hs : rowSum p key (c • z) = fun x => c * rowSum p key z x := by
      funext x
      simp [rowSum, decode, mul_div_assoc, Finset.mul_sum]
    rw [hs, conditionalSum_smul]
    change (c * _) / _ = c * (_ / _)
    ring

@[simp] theorem gram_apply (w : Ω → ℝ) (p : ι → β → ℝ)
    (key : ι → Ω → β) (z : Space ι β) (i : ι) (t : β) :
    gram w p key z (i,t) =
      conditionalSum w key i t (rowSum p key z) / Real.sqrt (p i t) := rfl

theorem inner_gram (w : Ω → ℝ) (p : ι → β → ℝ)
    (key : ι → Ω → β) (z z' : Space ι β) :
    inner ℝ z (gram w p key z') =
      ∑ x, w x * rowSum p key z x * rowSum p key z' x := by
  classical
  rw [real_inner_comm]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fintype.sum_prod_type,
    gram_apply]
  have hrew (i : ι) :
      (∑ t, z (i,t) * (conditionalSum w key i t (rowSum p key z') /
        Real.sqrt (p i t))) =
      ∑ x, w x * decode p z i (key i x) * rowSum p key z' x := by
    rw [← sum_mul_conditionalSum w key i (decode p z i) (rowSum p key z')]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [decode]
    ring
  simp_rw [hrew]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  unfold rowSum
  rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem gram_symmetric (w : Ω → ℝ) (p : ι → β → ℝ)
    (key : ι → Ω → β) : (gram w p key).IsSymmetric := by
  intro z z'
  rw [real_inner_comm, inner_gram, inner_gram]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem gram_nonneg (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (p : ι → β → ℝ) (key : ι → Ω → β) (z : Space ι β) :
    0 ≤ inner ℝ z (gram w p key z) := by
  rw [inner_gram]
  apply Finset.sum_nonneg
  intro x hx
  nlinarith [hw x, sq_nonneg (rowSum p key z x)]

def centered (p : ι → β → ℝ) : Submodule ℝ (Space ι β) where
  carrier := {z | ∀ i, ∑ t, Real.sqrt (p i t) * z (i,t) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro z z' hz hz' i
    simp only [Set.mem_ofPred_eq] at hz hz'
    simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib, hz i, hz' i, add_zero]
  smul_mem' := by
    intro c z hz i
    simp only [Set.mem_ofPred_eq] at hz
    simp only [PiLp.smul_apply, smul_eq_mul]
    simp_rw [mul_left_comm (Real.sqrt _) c]
    rw [← Finset.mul_sum, hz i, mul_zero]

include sectionDecidableEqβ in
@[simp] theorem mem_centered (p : ι → β → ℝ) (z : Space ι β) :
    z ∈ centered p ↔ ∀ i, ∑ t, Real.sqrt (p i t) * z (i,t) = 0 := by
  have retainedsectionDecidableEqβ := sectionDecidableEqβ
  exact Iff.rfl

include sectionDecidableEqβ in
theorem marginal_mul_decode (p : ι → β → ℝ) (hp : ∀ i t, 0 < p i t)
    (z : Space ι β) (i : ι) (t : β) :
    p i t * decode p z i t = Real.sqrt (p i t) * z (i,t) := by
  have retainedsectionDecidableEqβ := sectionDecidableEqβ
  have hs : Real.sqrt (p i t) ≠ 0 := (Real.sqrt_pos.2 (hp i t)).ne'
  unfold decode
  calc
    p i t * (z (i,t) / Real.sqrt (p i t)) =
        (Real.sqrt (p i t) * Real.sqrt (p i t)) *
          (z (i,t) / Real.sqrt (p i t)) := by
      rw [Real.mul_self_sqrt (hp i t).le]
    _ = Real.sqrt (p i t) * z (i,t) := by field_simp

theorem weighted_rowSum (w : Ω → ℝ) (p : ι → β → ℝ)
    (hp : ∀ i t, 0 < p i t) (key : ι → Ω → β)
    (hmarginal : ∀ i t, conditionalSum w key i t (fun _ => 1) = p i t)
    (z : Space ι β) :
    (∑ x, w x * rowSum p key z x) =
      ∑ i, ∑ t, Real.sqrt (p i t) * z (i,t) := by
  classical
  unfold rowSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have h := sum_mul_conditionalSum w key i (decode p z i) (fun _ => 1)
  simp only [hmarginal, mul_one] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro t ht
  rw [mul_comm, marginal_mul_decode p hp]

theorem gram_preserves_centered (w : Ω → ℝ) (p : ι → β → ℝ)
    (hp : ∀ i t, 0 < p i t) (key : ι → Ω → β)
    (hmarginal : ∀ i t, conditionalSum w key i t (fun _ => 1) = p i t)
    (z : Space ι β) (hz : z ∈ centered p) : gram w p key z ∈ centered p := by
  classical
  intro i
  calc
    (∑ t, Real.sqrt (p i t) * gram w p key z (i,t)) =
        ∑ t, conditionalSum w key i t (rowSum p key z) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [gram_apply]
      have hs : Real.sqrt (p i t) ≠ 0 := (Real.sqrt_pos.2 (hp i t)).ne'
      field_simp
    _ = ∑ x, w x * rowSum p key z x := sum_conditionalSum w key i _
    _ = ∑ j, ∑ t, Real.sqrt (p j t) * z (j,t) :=
      weighted_rowSum w p hp key hmarginal z
    _ = 0 := by
      have hz' := (mem_centered p z).mp hz
      simp only [hz', Finset.sum_const_zero]

theorem conditional_eigen_equation (w : Ω → ℝ) (p : ι → β → ℝ)
    (hp : ∀ i t, 0 < p i t) (key : ι → Ω → β)
    (z : Space ι β) (lam : ℝ) (heig : gram w p key z = lam • z)
    (i : ι) (t : β) :
    lam * decode p z i t =
      conditionalSum w key i t (rowSum p key z) / p i t := by
  have hs : Real.sqrt (p i t) ≠ 0 := (Real.sqrt_pos.2 (hp i t)).ne'
  have he := congrArg (fun q : Space ι β => q (i,t)) heig
  change conditionalSum w key i t (rowSum p key z) / Real.sqrt (p i t) =
    lam * z (i,t) at he
  calc
    lam * decode p z i t = (lam * z (i,t)) / Real.sqrt (p i t) := by
      unfold decode
      ring
    _ = (conditionalSum w key i t (rowSum p key z) / Real.sqrt (p i t)) /
        Real.sqrt (p i t) := by rw [he]
    _ = conditionalSum w key i t (rowSum p key z) / p i t := by
      rw [div_div, Real.mul_self_sqrt (hp i t).le]

def encode (p : ι → β → ℝ) (b : ι → β → ℝ) : Space ι β :=
  WithLp.toLp 2 (fun it => Real.sqrt (p it.1 it.2) * b it.1 it.2)

include sectionDecidableEqβ in
@[simp] theorem decode_encode (p : ι → β → ℝ) (hp : ∀ i t, 0 < p i t)
    (b : ι → β → ℝ) (i : ι) (t : β) : decode p (encode p b) i t = b i t := by
  have retainedsectionDecidableEqβ := sectionDecidableEqβ
  unfold decode encode
  change Real.sqrt (p i t) * b i t / Real.sqrt (p i t) = b i t
  exact mul_div_cancel_left₀ _ (Real.sqrt_pos.2 (hp i t)).ne'

include sectionDecidableEqβ in
theorem encode_mem_centered (p : ι → β → ℝ) (hp : ∀ i t, 0 < p i t)
    (b : ι → β → ℝ) (hb : ∀ i, ∑ t, p i t * b i t = 0) :
    encode p b ∈ centered p := by
  have retainedsectionDecidableEqβ := sectionDecidableEqβ
  intro i
  convert hb i using 1
  apply Finset.sum_congr rfl
  intro t ht
  change Real.sqrt (p i t) * (Real.sqrt (p i t) * b i t) = p i t * b i t
  rw [← mul_assoc, Real.mul_self_sqrt (hp i t).le]

include sectionDecidableEqβ in
theorem norm_encode_sq (p : ι → β → ℝ) (hp : ∀ i t, 0 < p i t)
    (b : ι → β → ℝ) :
    ‖encode p b‖ ^ 2 = ∑ i, ∑ t, p i t * (b i t) ^ 2 := by
  have retainedsectionDecidableEqβ := sectionDecidableEqβ
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro t ht
  change (Real.sqrt (p i t) * b i t) ^ 2 = p i t * (b i t) ^ 2
  rw [mul_pow, Real.sq_sqrt (hp i t).le]

theorem centered_variance_le_of_eigenvalue_bound
    (w : Ω → ℝ) (p : ι → β → ℝ) (hp : ∀ i t, 0 < p i t)
    (key : ι → Ω → β)
    (hmarginal : ∀ i t, conditionalSum w key i t (fun _ => 1) = p i t)
    (C : ℝ)
    (heigen : ∀ (lam : ℝ) (b : ι → β → ℝ),
      (∀ i, ∑ t, p i t * b i t = 0) →
      (∃ i t, b i t ≠ 0) →
      (∀ i t, lam * b i t =
        conditionalSum w key i t (fun x => ∑ j, b j (key j x)) / p i t) →
      lam ≤ C)
    (b : ι → β → ℝ) (hb : ∀ i, ∑ t, p i t * b i t = 0) :
    (∑ x, w x * (∑ i, b i (key i x)) ^ 2) ≤
      C * ∑ i, ∑ t, p i t * (b i t) ^ 2 := by
  classical
  let U := centered p
  let T := (gram w p key).restrict (gram_preserves_centered w p hp key hmarginal)
  have hT : T.IsSymmetric :=
    (gram_symmetric w p key).restrict_invariant
      (gram_preserves_centered w p hp key hmarginal)
  let basis := hT.eigenvectorBasis (rfl : Module.finrank ℝ U = Module.finrank ℝ U)
  let ev := hT.eigenvalues (rfl : Module.finrank ℝ U = Module.finrank ℝ U)
  have hbe (k : Fin (Module.finrank ℝ U)) : T (basis k) = ev k • basis k :=
    hT.apply_eigenvectorBasis rfl k
  have hev (k : Fin (Module.finrank ℝ U)) : ev k ≤ C := by
    apply heigen (ev k) (decode p (basis k : Space ι β))
    · intro i
      simp_rw [marginal_mul_decode p hp]
      exact (basis k).property i
    · by_contra hz
      push Not at hz
      have hz0 : (basis k : Space ι β) = 0 := by
        ext it
        have h := hz it.1 it.2
        unfold decode at h
        exact (div_eq_zero_iff).mp h |>.resolve_right (Real.sqrt_pos.2 (hp it.1 it.2)).ne'
      have hzero : basis k = 0 := Subtype.ext hz0
      have hn := basis.orthonormal.1 k
      rw [hzero, norm_zero] at hn
      norm_num at hn
    · intro i t
      exact conditional_eigen_equation w p hp key _ (ev k)
        (congrArg Subtype.val (hbe k)) i t
  have hquad (z : U) : inner ℝ z (T z) ≤ C * ‖z‖ ^ 2 := by
    rw [← basis.sum_inner_mul_inner z (T z), ← basis.sum_sq_inner_right z,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hcoord : inner ℝ (basis k) (T z) = ev k * inner ℝ (basis k) z := by
      rw [← hT (basis k) z, hbe]
      exact real_inner_smul_left (basis k : U) z (ev k)
    rw [hcoord, real_inner_comm z (basis k)]
    have hk := hev k
    nlinarith [sq_nonneg (inner ℝ (basis k) z)]
  let z : U := ⟨encode p b, encode_mem_centered p hp b hb⟩
  have h := hquad z
  change inner ℝ (encode p b) (gram w p key (encode p b)) ≤ C * ‖encode p b‖ ^ 2 at h
  rw [inner_gram, norm_encode_sq p hp] at h
  simpa only [rowSum, decode_encode p hp, mul_assoc, ← pow_two] using h

end Problem315.WeightedConditional

end

end OAI
