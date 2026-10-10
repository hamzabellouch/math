import OAI.NumberTheory.Ostmann.Arithmetic.PrimeSquareLifts

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PrimeSquareLiftFamilies
open scoped BigOperators

def affineSwapEquiv {K : Type*} [Field K] (a b c : K) :
    {z : K × K // a*z.1+b*z.2=c} ≃
      {z : K × K // b*z.1+a*z.2=c} where
  toFun z := ⟨(z.val.2,z.val.1), by simpa [add_comm] using z.property⟩
  invFun z := ⟨(z.val.2,z.val.1), by simpa [add_comm] using z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def affineRowEquiv {K : Type*} [Field K] (a b c : K) (h : a ≠ 0 ∨ b ≠ 0) :
    {z : K × K // a*z.1+b*z.2=c} ≃ K := by
  classical
  by_cases ha : a = 0
  · exact (affineSwapEquiv a b c).trans
      (PrimeSquareLifts.affineLineEquiv b a c (h.resolve_left (not_not.mpr ha)))
  · exact PrimeSquareLifts.affineLineEquiv a b c ha

variable (p : ℕ) [Fact p.Prime]

def row (a b c : ZMod p) : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun z => a*z.1+b*z.2=c

theorem row_card (a b c : ZMod p) (h : a ≠ 0 ∨ b ≠ 0) :
    (row p a b c).card = p := by
  classical
  rw [row, ← Fintype.card_subtype]
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (affineRowEquiv a b c h),
    Nat.card_eq_fintype_card, ZMod.card]

theorem row_probability (a b c : ZMod p) (h : a ≠ 0 ∨ b ≠ 0) :
    ((row p a b c).card : ℝ) / Fintype.card (ZMod p × ZMod p) = (p:ℝ)⁻¹ := by
  rw [row_card p a b c h, Fintype.card_prod, ZMod.card]
  have hp : (p:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  push_cast
  field_simp

variable {ι : Type*} (s : Finset ι) (a b c : ι → ZMod p)

def badLifts : Finset (ZMod p × ZMod p) := by
  classical
  exact s.biUnion fun i => row p (a i) (b i) (c i)

def survivingLifts : Finset (ZMod p × ZMod p) := (badLifts p s a b c)ᶜ

@[simp] theorem mem_badLifts (z : ZMod p × ZMod p) :
    z ∈ badLifts p s a b c ↔ ∃ i ∈ s, a i*z.1+b i*z.2=c i := by
  classical
  simp [badLifts, row]

@[simp] theorem mem_survivingLifts (z : ZMod p × ZMod p) :
    z ∈ survivingLifts p s a b c ↔ ∀ i ∈ s, a i*z.1+b i*z.2 ≠ c i := by
  classical
  simp [survivingLifts]

theorem badLifts_card_le (h : ∀ i ∈ s, a i ≠ 0 ∨ b i ≠ 0) :
    (badLifts p s a b c).card ≤ s.card * p := by
  classical
  calc
    _ ≤ ∑ i ∈ s, (row p (a i) (b i) (c i)).card := Finset.card_biUnion_le
    _ = ∑ _i ∈ s, p := Finset.sum_congr rfl fun i hi => row_card p _ _ _ (h i hi)
    _ = s.card * p := by simp

theorem badLifts_probability_le (h : ∀ i ∈ s, a i ≠ 0 ∨ b i ≠ 0) :
    ((badLifts p s a b c).card : ℝ) / Fintype.card (ZMod p × ZMod p) ≤
      (s.card:ℝ) / p := by
  have hp : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  calc
    _ ≤ ((s.card*p:ℕ):ℝ) / Fintype.card (ZMod p × ZMod p) := by
      gcongr
      exact badLifts_card_le p s a b c h
    _ = (s.card:ℝ) / p := by
      rw [Fintype.card_prod, ZMod.card]
      push_cast
      field_simp

theorem survivingLifts_probability_ge (h : ∀ i ∈ s, a i ≠ 0 ∨ b i ≠ 0) :
    1 - (s.card:ℝ) / p ≤
      ((survivingLifts p s a b c).card : ℝ) / Fintype.card (ZMod p × ZMod p) := by
  classical
  have hn : (0:ℝ) < Fintype.card (ZMod p × ZMod p) := by positivity
  have hcard : (survivingLifts p s a b c).card + (badLifts p s a b c).card =
      Fintype.card (ZMod p × ZMod p) := Finset.card_compl_add_card _
  have hsum : ((survivingLifts p s a b c).card:ℝ) /
      Fintype.card (ZMod p × ZMod p) + ((badLifts p s a b c).card:ℝ) /
      Fintype.card (ZMod p × ZMod p) = 1 := by
    rw [← add_div, ← Nat.cast_add, hcard, div_self (ne_of_gt hn)]
  linarith [badLifts_probability_le p s a b c h]

theorem bounded_test_loss (h : ∀ i ∈ s, a i ≠ 0 ∨ b i ≠ 0)
    (f : ZMod p × ZMod p → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ B) :
    0 ≤ ((∑ z, f z) - ∑ z ∈ survivingLifts p s a b c, f z) /
      Fintype.card (ZMod p × ZMod p) ∧
    ((∑ z, f z) - ∑ z ∈ survivingLifts p s a b c, f z) /
      Fintype.card (ZMod p × ZMod p) ≤ B * ((s.card:ℝ) / p) := by
  classical
  have heq : (∑ z, f z) - ∑ z ∈ survivingLifts p s a b c, f z =
      ∑ z ∈ badLifts p s a b c, f z := by
    have he := Finset.sum_add_sum_compl (badLifts p s a b c) f
    dsimp [survivingLifts]
    linarith
  rw [heq]
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun z _ => (hf z).1) (Nat.cast_nonneg _)
  · calc
      _ ≤ ((badLifts p s a b c).card:ℝ) * B /
          Fintype.card (ZMod p × ZMod p) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        calc
          _ ≤ ∑ _z ∈ badLifts p s a b c, B := Finset.sum_le_sum fun z _ => (hf z).2
          _ = _ := by simp
      _ = B * (((badLifts p s a b c).card:ℝ) /
          Fintype.card (ZMod p × ZMod p)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (badLifts_probability_le p s a b c h) hB

theorem square_divides_some_lift_iff
    (A B k : ι → ℤ) (x y u v : ℤ)
    (hbase : ∀ i ∈ s, A i*x+B i*y=(p:ℤ)*k i) :
    (∃ i ∈ s, (p:ℤ)*(p:ℤ) ∣
      A i*(x+(p:ℤ)*u)+B i*(y+(p:ℤ)*v)) ↔
    ((u:ZMod p),(v:ZMod p)) ∈
      badLifts p s (fun i => (A i:ZMod p)) (fun i => (B i:ZMod p))
        (fun i => -(k i:ZMod p)) := by
  rw [mem_badLifts]
  exact exists_congr fun i => and_congr_right fun hi =>
    PrimeSquareLifts.square_divides_lift_iff_residue p _ _ _ _ _ _ _ (hbase i hi)

def integerBadLifts (A B : ι → ℤ) (x y : ℤ) : Finset (ZMod p × ZMod p) := by
  classical
  exact Finset.univ.filter fun z => ∃ i ∈ s, (p:ℤ)*(p:ℤ) ∣
    A i*(x+(p:ℤ)*(z.1.val:ℤ))+B i*(y+(p:ℤ)*(z.2.val:ℤ))

theorem integerBadLifts_eq (A B k : ι → ℤ) (x y : ℤ)
    (hbase : ∀ i ∈ s, A i*x+B i*y=(p:ℤ)*k i) :
    integerBadLifts p s A B x y =
      badLifts p s (fun i => (A i:ZMod p)) (fun i => (B i:ZMod p))
        (fun i => -(k i:ZMod p)) := by
  classical
  ext z
  simp only [integerBadLifts, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [square_divides_some_lift_iff p s A B k x y _ _ hbase]
  simp

theorem integer_bad_lift_probability_le (A B k : ι → ℤ) (x y : ℤ)
    (hbase : ∀ i ∈ s, A i*x+B i*y=(p:ℤ)*k i)
    (hrow : ∀ i ∈ s, (A i:ZMod p) ≠ 0 ∨ (B i:ZMod p) ≠ 0) :
    ((integerBadLifts p s A B x y).card:ℝ) /
      Fintype.card (ZMod p × ZMod p) ≤ (s.card:ℝ) / p := by
  rw [integerBadLifts_eq p s A B k x y hbase]
  exact badLifts_probability_le p s _ _ _ hrow

end Ostmann.Arithmetic.PrimeSquareLiftFamilies

end

end OAI
