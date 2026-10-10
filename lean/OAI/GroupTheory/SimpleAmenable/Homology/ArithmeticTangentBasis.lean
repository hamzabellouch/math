import Mathlib
import OAI.GroupTheory.SimpleAmenable.Arithmetic.PropagationArithmetic

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ArithmeticTangentBasis

theorem cutRing_coefficients (z : CutRing) :
    (z.re : CutRing) + (z.im : CutRing)*cutTau = z := by
  apply QuadraticAlgebra.ext <;> simp [cutTau]

theorem cutTau_inverse_mul : (cutTau-1)*cutTau = 1 := by
  apply ordinary_injective
  simp only [map_mul,map_sub,map_one,ordinary_cutTau]
  nlinarith [Real.goldenRatio_sq]

theorem cutRing_coefficients_bound (z : CutRing) :
    |(z.re : ℝ)| + |(z.im : ℝ)| ≤ 4 * (|ordinary z| + |conjugate z|) := by
  have hs : 1 ≤ Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]
  have hq : |(z.im : ℝ)| ≤ |ordinary z| + |conjugate z| := by
    have he : (z.im : ℝ) * Real.sqrt 5 = ordinary z - conjugate z := by
      have := (eq_div_iff (by positivity : Real.sqrt 5 ≠ 0)).mp (endpointLabel_embedding z)
      exact this
    have ht : |ordinary z - conjugate z| ≤ |ordinary z| + |conjugate z| :=
      abs_sub _ _
    rw [← he,abs_mul,abs_of_nonneg (le_trans zero_le_one hs)] at ht
    nlinarith [abs_nonneg (z.im : ℝ)]
  have hp : |(z.re : ℝ)| ≤ |ordinary z| + 2*|(z.im : ℝ)| := by
    have he : (z.re : ℝ) = ordinary z - (z.im : ℝ)*Real.goldenRatio := by
      rw [ordinary_apply]
      ring
    rw [he]
    calc
      _ ≤ |ordinary z| + |(z.im : ℝ)*Real.goldenRatio| := abs_sub _ _
      _ = |ordinary z| + |(z.im : ℝ)| * Real.goldenRatio := by
        rw [abs_mul, abs_of_pos Real.goldenRatio_pos]
      _ ≤ _ := by nlinarith [Real.goldenRatio_lt_two,abs_nonneg (z.im : ℝ)]
  nlinarith [abs_nonneg (conjugate z)]

theorem tangent_basis_coefficients (u v : CutRing) (huv : u*v = 1) (d : CutRing) :
    ∃ p q : ℤ, d = (p : CutRing)*u + (q : CutRing)*(cutTau*u) ∧
      |(p : ℝ)| + |(q : ℝ)| ≤
        (4*(|ordinary v|+|conjugate v|+1))*(|ordinary d|+|conjugate d|) := by
  let z := d*v
  refine ⟨z.re,z.im,?_,?_⟩
  · have he : z*u = d := by dsimp [z]; calc
      d*v*u = d*(u*v) := by ring
      _ = d := by rw [huv,mul_one]
    calc
      d = z*u := he.symm
      _ = ((z.re : CutRing) + (z.im : CutRing)*cutTau)*u :=
        congrArg (fun w : CutRing => w*u) (cutRing_coefficients z).symm
      _ = _ := by ring
  · have hb := cutRing_coefficients_bound z
    have ho : |ordinary z| = |ordinary d| * |ordinary v| := by simp [z,abs_mul]
    have hc : |conjugate z| = |conjugate d| * |conjugate v| := by simp [z,abs_mul]
    rw [ho,hc] at hb
    nlinarith [abs_nonneg (ordinary d),abs_nonneg (conjugate d),
      abs_nonneg (ordinary v),abs_nonneg (conjugate v),
      mul_nonneg (abs_nonneg (ordinary d)) (abs_nonneg (conjugate v)),
      mul_nonneg (abs_nonneg (conjugate d)) (abs_nonneg (ordinary v))]

theorem exists_short_tangent_basis (l : CutRing) {δ : ℝ} (hδ : 0 < δ) :
    ∃ u v : CutRing, u*v = 1 ∧
      (1+|ordinary l|)*(|ordinary u|+|ordinary (cutTau*u)|) < δ := by
  have hsmall : Real.goldenRatio-1 < 1 := by linarith [Real.goldenRatio_lt_two]
  have hpos : 0 < Real.goldenRatio-1 := by linarith [Real.one_lt_goldenRatio]
  have hk : 0 < 3*(1+|ordinary l|) := by positivity
  obtain ⟨b,hb⟩ := exists_pow_lt_of_lt_one (div_pos hδ hk) hsmall
  refine ⟨(cutTau-1)^b,cutTau^b,?_,?_⟩
  · rw [← mul_pow,cutTau_inverse_mul,one_pow]
  · simp only [map_pow,map_sub,map_one,map_mul,ordinary_cutTau,abs_mul,
      abs_pow,abs_of_pos Real.goldenRatio_pos,abs_of_pos hpos]
    have hpow : 0 < (Real.goldenRatio-1)^b := pow_pos hpos b
    have hb' := (lt_div_iff₀ hk).mp hb
    nlinarith [Real.goldenRatio_lt_two,abs_nonneg (ordinary l),
      mul_pos (by positivity : 0 < 1+|ordinary l|) hpow]

end ArithmeticTangentBasis

section FiniteTangentChains

noncomputable def integerSteps (k : ℤ) (u : CutRing) : List CutRing :=
  if 0 ≤ k then List.replicate k.toNat u else List.replicate (-k).toNat (-u)

@[simp]theorem integerSteps_sum (k : ℤ) (u : CutRing) :
    (integerSteps k u).sum = (k : CutRing)*u := by
  by_cases hk : 0 ≤ k
  · have hc : (k.toNat : CutRing) = (k : CutRing) := by
      exact_mod_cast Int.toNat_of_nonneg hk
    simp [integerSteps,hk,List.sum_replicate,nsmul_eq_mul,hc]
  · have hn : 0 ≤ -k := by omega
    have hc : ((-k).toNat : CutRing) = -(k : CutRing) := by
      exact_mod_cast Int.toNat_of_nonneg hn
    simp [integerSteps,hk,List.sum_replicate,nsmul_eq_mul,hc]

theorem integerSteps_length (k : ℤ) (u : CutRing) :
    ((integerSteps k u).length : ℝ) = |(k : ℝ)| := by
  by_cases hk : 0 ≤ k
  · have hc : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk
    simp [integerSteps,hk,hc,abs_of_nonneg (by exact_mod_cast hk : (0:ℝ) ≤ k)]
  · have hn : 0 ≤ -k := by omega
    have hc : ((-k).toNat : ℝ) = -(k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
    simp [integerSteps,hk,hc,abs_of_nonpos (by exact_mod_cast (le_of_not_ge hk) : (k:ℝ) ≤ 0)]

theorem integerSteps_mem (k : ℤ) (u e : CutRing) (he : e ∈ integerSteps k u) :
    e = u ∨ e = -u := by
  by_cases hk : 0 ≤ k
  · left
    exact (List.mem_replicate.mp (by simpa only [integerSteps,ite_eq_left hk] using he)).2
  · right
    exact (List.mem_replicate.mp (by simpa only [integerSteps,ite_eq_right hk] using he)).2

private theorem sum_abs_bound_by_length {α : Type*} (v : α → ℝ)
    (xs : List α) {B : ℝ} (hs : ∀ x ∈ xs, |v x| ≤ B) :
    |(xs.map v).sum| ≤ (xs.length : ℝ)*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hs x (by simp)
    have ht := ih (fun y hy => hs y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    calc
      |v x + (xs.map v).sum| ≤ |v x| + |(xs.map v).sum| := abs_add_le _ _
      _ ≤ B + (xs.length : ℝ)*B := add_le_add hx ht
      _ = _ := by ring

@[simp]theorem endpointLabel_list_sum (xs : List CutRing) :
    (endpointLabel xs.sum : ℝ) = (xs.map (fun z => (endpointLabel z : ℝ))).sum := by
  induction xs with
  | nil => simp [endpointLabel]
  | cons x xs ih => simpa only [List.sum_cons,endpointLabel_add,Int.cast_add,
      List.map_cons] using congrArg (fun r => (endpointLabel x : ℝ)+r) ih

theorem tangent_chain (u v : CutRing) (huv : u*v = 1) (d : CutRing) :
    ∃ w : List CutRing,
      w.sum = d ∧
      (∀ e ∈ w, e = u ∨ e = -u ∨ e = cutTau*u ∨ e = -(cutTau*u)) ∧
      (w.length : ℝ) ≤ (4*(|ordinary v|+|conjugate v|+1))*(|ordinary d|+|conjugate d|) ∧
      (∀ n : ℕ,
        min 0 (ordinary d) - (|ordinary u|+|ordinary (cutTau*u)|) ≤
          ordinary (w.take n).sum ∧
        ordinary (w.take n).sum ≤
          max 0 (ordinary d) + (|ordinary u|+|ordinary (cutTau*u)|)) ∧
      ∀ n : ℕ, |(endpointLabel (w.take n).sum : ℝ)| ≤
        (4*(|ordinary v|+|conjugate v|+1))*(|ordinary d|+|conjugate d|)*
          (|(endpointLabel u : ℝ)|+|(endpointLabel (cutTau*u) : ℝ)|) := by
  obtain ⟨p,q,hd,hpq⟩ := tangent_basis_coefficients u v huv d
  let xs := integerSteps p u ++ integerSteps q (cutTau*u)
  have hsum : xs.sum = d := by simp only [xs,List.sum_append,integerSteps_sum]; exact hd.symm
  have hmem : ∀ e ∈ xs, e = u ∨ e = -u ∨ e = cutTau*u ∨ e = -(cutTau*u) := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · rcases integerSteps_mem p u e he with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · rcases integerSteps_mem q (cutTau*u) e he with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
  have ho : ∀ e ∈ xs, |ordinary e| ≤ |ordinary u|+|ordinary (cutTau*u)| := by
    intro e he
    rcases hmem e he with he | he | he | he
    · rw [he]; exact le_add_of_nonneg_right (abs_nonneg _)
    · rw [he,map_neg,abs_neg]; exact le_add_of_nonneg_right (abs_nonneg _)
    · rw [he]; exact le_add_of_nonneg_left (abs_nonneg _)
    · rw [he,map_neg,abs_neg]; exact le_add_of_nonneg_left (abs_nonneg _)
  obtain ⟨w,hw,hbound⟩ := exists_step_order_near_segment ordinary xs (by positivity) ho
  have hwsum : w.sum = d := hw.sum_eq.trans hsum
  have hwm : ∀ e ∈ w, e = u ∨ e = -u ∨ e = cutTau*u ∨ e = -(cutTau*u) :=
    fun e he => hmem e (hw.mem_iff.mp he)
  have hlen : (w.length : ℝ) ≤
      (4*(|ordinary v|+|conjugate v|+1))*(|ordinary d|+|conjugate d|) := by
    rw [hw.length_eq]
    simpa only [xs,List.length_append,Nat.cast_add,integerSteps_length] using hpq
  refine ⟨w,hwsum,hwm,hlen,?_,?_⟩
  · intro n
    simpa only [← map_list_sum,hsum] using hbound n
  · intro n
    let B := |(endpointLabel u : ℝ)|+|(endpointLabel (cutTau*u) : ℝ)|
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hb : ∀ e ∈ w.take n, |(endpointLabel e : ℝ)| ≤ B := by
      intro e he
      have hew := List.mem_of_mem_take he
      have hneg : ∀ z : CutRing, |(endpointLabel (-z) : ℝ)| = |(endpointLabel z : ℝ)| := by
        intro z
        simp only [endpointLabel,QuadraticAlgebra.im_neg,Int.cast_neg,abs_neg]
      rcases hwm e hew with he | he | he | he
      · rw [he]; exact le_add_of_nonneg_right (abs_nonneg _)
      · rw [he,hneg]; exact le_add_of_nonneg_right (abs_nonneg _)
      · rw [he]; exact le_add_of_nonneg_left (abs_nonneg _)
      · rw [he,hneg]; exact le_add_of_nonneg_left (abs_nonneg _)
    rw [endpointLabel_list_sum]
    calc
      _ ≤ ((w.take n).length : ℝ)*B := sum_abs_bound_by_length _ _ hb
      _ ≤ (w.length : ℝ)*B := mul_le_mul_of_nonneg_right (by exact_mod_cast (show (w.take n).length ≤ w.length by simp only [List.length_take]; exact min_le_right _ _)) hB
      _ ≤ _ := mul_le_mul_of_nonneg_right hlen hB

end FiniteTangentChains

end SimpleAmenable
end
end

end OAI
