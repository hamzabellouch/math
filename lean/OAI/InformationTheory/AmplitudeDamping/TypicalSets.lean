import OAI.InformationTheory.AmplitudeDamping.SequentialMatrices

namespace OAI

noncomputable section

universe u_1 u_2

section
open scoped BigOperators
namespace GAD
variable {α : Type u_1} [Fintype α]

def iidWeight (q : α → ℝ) (n : ℕ) (x : Fin n → α) : ℝ := ∏ j, q (x j)
def iidSum (f : α → ℝ) (n : ℕ) (x : Fin n → α) : ℝ := ∑ j, f (x j)

omit [Fintype α] in
theorem iidWeight_nonneg (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (n : ℕ) (x : Fin n → α) :
    0 ≤ iidWeight q n x := Finset.prod_nonneg (fun j _ ↦ hq (x j))

theorem iidWeight_total (q : α → ℝ) (hs : ∑ a, q a=1) (n : ℕ) :
    (∑ x : Fin n → α, iidWeight q n x)=1 := by
  rw [show (∑ x : Fin n → α, iidWeight q n x) = ∏ j : Fin n, ∑ a, q a from
    (Fintype.prod_sum (fun _ : Fin n ↦ q)).symm]
  simp only [hs,Finset.prod_const_one]

theorem iid_split_sum (q : α → ℝ) (n : ℕ) (f : (Fin (n+1) → α) → ℝ) :
    (∑ x, iidWeight q (n+1) x*f x) =
      ∑ a, ∑ x : Fin n → α, q a*iidWeight q n x*f (Fin.cons a x) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) ↦ α))
    (fun x ↦ iidWeight q (n+1) x*f x)]
  simp only [Fintype.sum_prod_type,Fin.consEquiv_apply,iidWeight,Fin.prod_univ_succ,
    Fin.cons_zero,Fin.cons_succ]
  rfl

omit [Fintype α] in
theorem iidSum_cons (f : α → ℝ) (n : ℕ) (a : α) (x : Fin n → α) :
    iidSum f (n+1) (Fin.cons a x)=f a+iidSum f n x := by
  simp only [iidSum,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

theorem iid_centered_mean (q f : α → ℝ) (hs : ∑ a, q a=1)
    (hf : ∑ a, q a*f a=0) (n : ℕ) :
    (∑ x : Fin n → α, iidWeight q n x*iidSum f n x)=0 := by
  induction n with
  | zero => simp [iidSum]
  | succ n ih =>
      rw [iid_split_sum]
      have he (a : α) : (∑ x : Fin n → α, q a*iidWeight q n x*iidSum f (n+1) (Fin.cons a x)) = q a*f a := by
        simp only [iidSum_cons]
        have hpoly (x : Fin n → α) : q a*iidWeight q n x*(f a+iidSum f n x) =
            (q a*f a)*iidWeight q n x+q a*(iidWeight q n x*iidSum f n x) := by ring
        simp only [hpoly,Finset.sum_add_distrib,← Finset.mul_sum,iidWeight_total q hs n,
          ih,mul_one,mul_zero,add_zero]
      simpa only [he] using hf

theorem iid_centered_second (q f : α → ℝ) (hs : ∑ a, q a=1)
    (hf : ∑ a, q a*f a=0) (n : ℕ) :
    (∑ x : Fin n → α, iidWeight q n x*(iidSum f n x)^2)=
      (n:ℝ)*(∑ a, q a*(f a)^2) := by
  induction n with
  | zero => simp [iidSum]
  | succ n ih =>
      rw [iid_split_sum]
      simp only [iidSum_cons]
      have he (a : α) : (∑ x : Fin n → α, q a*iidWeight q n x*(f a+iidSum f n x)^2) =
          q a*(f a)^2+q a*((n:ℝ)*∑ b, q b*(f b)^2) := by
        have hpoly (x : Fin n → α) : q a*iidWeight q n x*(f a+iidSum f n x)^2 =
            (q a*(f a)^2)*iidWeight q n x+(2*q a*f a)*(iidWeight q n x*iidSum f n x)+
              q a*(iidWeight q n x*(iidSum f n x)^2) := by ring
        simp only [hpoly,Finset.sum_add_distrib,← Finset.mul_sum,iidWeight_total q hs n,
          iid_centered_mean q f hs hf n,ih,mul_one,mul_zero,add_zero]
      simp only [he,Finset.sum_add_distrib,← Finset.sum_mul,hs,one_mul,Nat.cast_add,Nat.cast_one]
      ring

theorem iid_chebyshev (q f : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hs : ∑ a, q a=1)
    (hf : ∑ a, q a*f a=0) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (∑ x : Fin n → α, if t < |iidSum f n x| then iidWeight q n x else 0) ≤
      (n:ℝ)*(∑ a, q a*(f a)^2)/t^2 := by
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  rw [Finset.sum_mul,← iid_centered_second q f hs hf n]
  apply Finset.sum_le_sum
  intro x _
  split_ifs with hx
  · apply mul_le_mul_of_nonneg_left _ (iidWeight_nonneg q hq n x)
    nlinarith [sq_abs (iidSum f n x)]
  · simp only [zero_mul]
    exact mul_nonneg (iidWeight_nonneg q hq n x) (sq_nonneg _)

end GAD

end

open scoped BigOperators
namespace GAD
variable {α : Type u_2} [Fintype α]
local instance : DecidablePred (fun p : Prop ↦ p) := Classical.propDecidable

def classicalEntropy (q : α → ℝ) : ℝ := ∑ a, Real.negMulLog (q a)
def centeredLog (q : α → ℝ) (a : α) : ℝ := -Real.log (q a)-classicalEntropy q
def logVariance (q : α → ℝ) : ℝ := ∑ a, q a*(centeredLog q a)^2

theorem centeredLog_mean (q : α → ℝ) (hs : ∑ a, q a=1) :
    (∑ a, q a*centeredLog q a)=0 := by
  simp only [centeredLog,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hs,one_mul]
  simp [classicalEntropy,Real.negMulLog,mul_neg]

def IsTypical (q : α → ℝ) (δ : ℝ) (n : ℕ) (x : Fin n → α) : Prop :=
  0 < iidWeight q n x ∧ |iidSum (centeredLog q) n x| ≤ (n:ℝ)*δ

theorem iid_log (q : α → ℝ) (n : ℕ) (x : Fin n → α) (hx : 0 < iidWeight q n x) :
    iidSum (centeredLog q) n x = -Real.log (iidWeight q n x)-(n:ℝ)*classicalEntropy q := by
  have hn : ∀ j ∈ Finset.univ, q (x j) ≠ 0 := (Finset.prod_ne_zero_iff.mp hx.ne')
  simp only [iidSum,centeredLog,Finset.sum_sub_distrib,Finset.sum_neg_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [iidWeight,Real.log_prod hn]

theorem typical_weight_lower (q : α → ℝ) (δ : ℝ) (n : ℕ) (x : Fin n → α)
    (hx : IsTypical q δ n x) : Real.exp (-(n:ℝ)*(classicalEntropy q+δ)) ≤ iidWeight q n x := by
  rw [← Real.exp_log hx.1]
  apply Real.exp_le_exp.mpr
  have h := (abs_le.mp hx.2).2
  rw [iid_log q n x hx.1] at h
  nlinarith

theorem typical_weight_upper (q : α → ℝ) (δ : ℝ) (n : ℕ) (x : Fin n → α)
    (hx : IsTypical q δ n x) : iidWeight q n x ≤ Real.exp (-(n:ℝ)*(classicalEntropy q-δ)) := by
  rw [← Real.exp_log hx.1]
  apply Real.exp_le_exp.mpr
  have h := (abs_le.mp hx.2).1
  rw [iid_log q n x hx.1] at h
  nlinarith

theorem typical_tail (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hs : ∑ a, q a=1)
    {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 0 < n) :
    (∑ x : Fin n → α, if IsTypical q δ n x then 0 else iidWeight q n x) ≤
      logVariance q / ((n:ℝ)*δ^2) := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have he (x : Fin n → α) : (if IsTypical q δ n x then 0 else iidWeight q n x) =
      (if (n:ℝ)*δ < |iidSum (centeredLog q) n x| then iidWeight q n x else 0) := by
    by_cases hx : 0 < iidWeight q n x
    · simp only [IsTypical,hx,true_and]
      split_ifs <;> first | rfl | (exfalso; linarith)
    · have hz : iidWeight q n x=0 := le_antisymm (not_lt.mp hx) (iidWeight_nonneg q hq n x)
      simp [hz]
  simp only [he]
  have h := iid_chebyshev q (centeredLog q) hq hs (centeredLog_mean q hs) n (mul_pos hn' hδ)
  convert h using 1
  dsimp only [logVariance]
  field_simp

def typicalSet (q : α → ℝ) (δ : ℝ) (n : ℕ) : Finset (Fin n → α) :=
  Finset.univ.filter (IsTypical q δ n)

theorem typical_card (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hs : ∑ a, q a=1)
    (δ : ℝ) (n : ℕ) :
    ((typicalSet q δ n).card : ℝ) ≤ Real.exp ((n:ℝ)*(classicalEntropy q+δ)) := by
  let c := Real.exp (-(n:ℝ)*(classicalEntropy q+δ))
  have hc : 0 < c := Real.exp_pos _
  have hsum : ((typicalSet q δ n).card : ℝ)*c ≤ 1 := by
    calc
      _ = ∑ x ∈ typicalSet q δ n, c := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ ∑ x ∈ typicalSet q δ n, iidWeight q n x := by
        apply Finset.sum_le_sum
        intro x hx
        exact typical_weight_lower q δ n x (Finset.mem_filter.mp hx).2
      _ ≤ ∑ x : Fin n → α, iidWeight q n x := Finset.sum_le_univ_sum_of_nonneg
        (fun x ↦ iidWeight_nonneg q hq n x)
      _ = 1 := iidWeight_total q hs n
  have h := mul_le_mul_of_nonneg_right hsum (Real.exp_pos ((n:ℝ)*(classicalEntropy q+δ))).le
  have hexp : c*Real.exp ((n:ℝ)*(classicalEntropy q+δ))=1 := by
    dsimp [c]
    rw [← Real.exp_add]
    simp only [neg_mul, neg_add_cancel, Real.exp_zero]
  rwa [mul_assoc,hexp,mul_one,one_mul] at h

end GAD

end

end OAI
