import OAI.Analysis.OInfinity.FiniteCAR

namespace OAI

/-! # Finite linear combinations of the corner CAR generators

Only finite sums are used. The anticommutator gives the Euclidean coefficient
bound directly, and the corner shift acts exactly on the required even
products. No infinite CAR algebra or representation theorem is assumed.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]
variable {I : Type*} [Fintype I]

def carSynthesis (x : I → E) (c : I → ℂ) : E := ∑ i, c i • x i

lemma carSynthesis_sub (x : I → E) (c d : I → ℂ) :
    carSynthesis x (c - d) = carSynthesis x c - carSynthesis x d := by
  simp only [carSynthesis, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

lemma carSynthesis_star (x : I → E) (c : I → ℂ) :
    star (carSynthesis x c) = carSynthesis (fun i => star (x i)) (fun i => star (c i)) := by
  simp only [carSynthesis, star_sum, star_smul]

lemma carSynthesis_mul (x y : I → E) (c d : I → ℂ) :
    carSynthesis x c * carSynthesis y d =
      ∑ i, ∑ j, (c i * d j) • (x i * y j) := by
  unfold carSynthesis
  rw [Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

lemma carSynthesis_support (q : E) (x : I → E)
    (hl : ∀ i, q * x i = x i) (hr : ∀ i, x i * q = x i) (c : I → ℂ) :
    q * carSynthesis x c = carSynthesis x c ∧
      carSynthesis x c * q = carSynthesis x c := by
  constructor
  · simp only [carSynthesis, Finset.mul_sum, mul_smul_comm, hl]
  · simp only [carSynthesis, Finset.sum_mul, smul_mul_assoc, hr]

lemma carSynthesis_anticommute (x : I → E)
    (hanti : ∀ i j, x i * x j + x j * x i = 0) (c d : I → ℂ) :
    carSynthesis x c * carSynthesis x d + carSynthesis x d * carSynthesis x c = 0 := by
  have hswap : carSynthesis x d * carSynthesis x c =
      ∑ i, ∑ j, (c i * d j) • (x j * x i) := by
    rw [carSynthesis_mul, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm (d j)]
  rw [carSynthesis_mul, hswap, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, ← smul_add, hanti, smul_zero]
  simp only [Finset.sum_const_zero]

lemma carSynthesis_square_zero (x : I → E)
    (hanti : ∀ i j, x i * x j + x j * x i = 0) (c : I → ℂ) :
    carSynthesis x c * carSynthesis x c = 0 := by
  have h := carSynthesis_anticommute x hanti c c
  have htwo : (2 : ℂ) • (carSynthesis x c * carSynthesis x c) = 0 := by
    rw [two_smul]
    exact h
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

lemma carSynthesis_star_anticommute [DecidableEq I] (q : E) (x : I → E)
    (hcar : ∀ i j, star (x i) * x j + x j * star (x i) = if i = j then q else 0)
    (c d : I → ℂ) :
    star (carSynthesis x c) * carSynthesis x d +
      carSynthesis x d * star (carSynthesis x c) = (∑ i, star (c i) * d i) • q := by
  have hswap : carSynthesis x d * star (carSynthesis x c) =
      ∑ i, ∑ j, (star (c i) * d j) • (x j * star (x i)) := by
    rw [carSynthesis_star, carSynthesis_mul, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm (d j)]
  rw [hswap, carSynthesis_star, carSynthesis_mul, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, ← smul_add, hcar]
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  simp

lemma carSynthesis_norm_sq_le [DecidableEq I] (q : E) (x : I → E)
    (hl : ∀ i, q * x i = x i)
    (hanti : ∀ i j, x i * x j + x j * x i = 0)
    (hcar : ∀ i j, star (x i) * x j + x j * star (x i) = if i = j then q else 0)
    (c : I → ℂ) : ‖carSynthesis x c‖ * ‖carSynthesis x c‖ ≤ ∑ i, ‖c i‖ ^ 2 := by
  have hgram : star (carSynthesis x c) * carSynthesis x c +
      carSynthesis x c * star (carSynthesis x c) = (∑ i, ‖c i‖ ^ 2) • q := by
    rw [carSynthesis_star_anticommute q x hcar]
    simp only [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i _
    have hci : star (c i) * c i = ((‖c i‖ ^ 2 : ℝ) : ℂ) := by
      simpa only [Complex.star_def, Complex.ofReal_pow] using Complex.conj_mul' (c i)
    rw [hci, Complex.coe_smul]
  have hleft : q * carSynthesis x c = carSynthesis x c := by
    simp only [carSynthesis, Finset.mul_sum, mul_smul_comm, hl]
  exact squareZero_norm_sq_le _ q _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (carSynthesis_square_zero x hanti c) hleft hgram

lemma carSynthesis_norm_sub_sq_le [DecidableEq I] (q : E) (x : I → E)
    (hl : ∀ i, q * x i = x i)
    (hanti : ∀ i j, x i * x j + x j * x i = 0)
    (hcar : ∀ i j, star (x i) * x j + x j * star (x i) = if i = j then q else 0)
    (c d : I → ℂ) :
    ‖carSynthesis x c - carSynthesis x d‖ * ‖carSynthesis x c - carSynthesis x d‖ ≤
      ∑ i, ‖c i - d i‖ ^ 2 := by
  simpa only [carSynthesis_sub, Pi.sub_apply] using
    carSynthesis_norm_sq_le q x hl hanti hcar (c - d)

lemma zeroCornerShift_smul (a b x : E) (c : ℂ) :
    zeroCornerShift a b (c • x) = c • zeroCornerShift a b x := by
  simp only [zeroCornerShift, mul_smul_comm, smul_mul_assoc, smul_add]

lemma zeroCornerShift_sum (a b : E) (x : I → E) :
    zeroCornerShift a b (∑ i, x i) = ∑ i, zeroCornerShift a b (x i) := by
  simp only [zeroCornerShift, Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib]

section Corner

variable (q a b : E) (hqstar : star q = q) (hqq : q * q = q)
  (haa : star a * a = q) (hbb : star b * b = q) (hab : star a * b = 0)
  (hsum : a * star a + b * star b = q)

include hqstar hqq haa hbb hab hsum in
lemma zeroCornerCAR_synthesis_norm_sq_le [DecidableEq I] (f : I → ℕ)
    (hf : Function.Injective f) (c : I → ℂ) :
    ‖carSynthesis (fun i => zeroCornerCAR a b (f i)) c‖ *
      ‖carSynthesis (fun i => zeroCornerCAR a b (f i)) c‖ ≤ ∑ i, ‖c i‖ ^ 2 := by
  apply carSynthesis_norm_sq_le q
  · intro i
    exact (zeroCornerCAR_support q a b hqstar hqq haa hbb hab hsum (f i)).1
  · intro i j
    exact zeroCornerCAR_anticommute q a b hqstar hqq haa hbb hab hsum (f i) (f j)
  · intro i j
    simpa only [hf.eq_iff] using
      zeroCornerCAR_star_anticommute q a b hqstar hqq haa hbb hab hsum (f i) (f j)

include hqstar hqq haa hbb hab hsum in
lemma zeroCornerCAR_synthesis_shift_even (f : I → ℕ) (c d : I → ℂ) :
    zeroCornerShift a b
      (carSynthesis (fun i => zeroCornerCAR a b (f i)) c *
        star (carSynthesis (fun i => zeroCornerCAR a b (f i)) d)) =
      carSynthesis (fun i => zeroCornerCAR a b (f i + 1)) c *
        star (carSynthesis (fun i => zeroCornerCAR a b (f i + 1)) d) := by
  simp only [carSynthesis_star, carSynthesis_mul,
    zeroCornerShift_sum, zeroCornerShift_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [zeroCornerCAR_shift_even q a b hqstar hqq haa hbb hab hsum]

include hqstar hqq haa hbb hab hsum in
lemma zeroCornerCAR_synthesis_shift_even_mul (f : I → ℕ) (c d : I → ℂ) :
    zeroCornerShift a b
      (carSynthesis (fun i => zeroCornerCAR a b (f i)) c *
        carSynthesis (fun i => zeroCornerCAR a b (f i)) d) =
      carSynthesis (fun i => zeroCornerCAR a b (f i + 1)) c *
        carSynthesis (fun i => zeroCornerCAR a b (f i + 1)) d := by
  simp only [carSynthesis_mul, zeroCornerShift_sum, zeroCornerShift_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  symm
  exact zeroCornerShift_parity_mul q a b hqstar hqq haa hbb hab hsum _ _
    (zeroCornerCAR_support q a b hqstar hqq haa hbb hab hsum (f j)).1

end Corner
end WeakPureInfiniteness

end

end OAI
