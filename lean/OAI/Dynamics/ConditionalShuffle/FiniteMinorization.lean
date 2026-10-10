import OAI.Dynamics.ConditionalShuffle.InjectionKernel

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace Thorp.Conditional.Reset
variable {X : Type*} [Fintype X] [nonempty_X : Nonempty X]

lemma sum_uniform_deficit (P : X → ℝ) (hP : ∑ x, P x = 1) :
    (∑ x, ((Fintype.card X : ℝ)⁻¹ - min (P x) (Fintype.card X : ℝ)⁻¹)) ≤
      tv P (fun _ => (Fintype.card X : ℝ)⁻¹) := by
  have huw : (∑ _ : X, (Fintype.card X : ℝ)⁻¹) = 1 := by simp
  have hh := sum_sub_le_tv (fun _ : X => (Fintype.card X : ℝ)⁻¹) P
    (huw.trans hP.symm) (Finset.univ.filter (fun x => P x ≤ (Fintype.card X : ℝ)⁻¹))
  have he : (∑ x, ((Fintype.card X : ℝ)⁻¹ - min (P x) (Fintype.card X : ℝ)⁻¹)) =
      ∑ x ∈ Finset.univ.filter (fun x => P x ≤ (Fintype.card X : ℝ)⁻¹),
        ((Fintype.card X : ℝ)⁻¹-P x) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl; intro x _
    by_cases hx : P x ≤ (Fintype.card X : ℝ)⁻¹
    · rw [min_eq_left hx, ite_eq_left hx]
    · rw [min_eq_right (le_of_not_ge hx), ite_eq_right hx, sub_self]
  rw [he]
  have ht : tv (fun _ : X => (Fintype.card X : ℝ)⁻¹) P = tv P (fun _ => (Fintype.card X : ℝ)⁻¹) := by
    unfold tv; simp_rw [abs_sub_comm]
  rwa [ht] at hh

lemma uniform_overlap (P Q : X → ℝ) (hP : ∀ x, 0 ≤ P x) (hQ : ∀ x, 0 ≤ Q x)
    (hP1 : ∑ x, P x = 1) (hQ1 : ∑ x, Q x = 1) (ε : ℝ)
    (hPt : tv P (fun _ => (Fintype.card X : ℝ)⁻¹) ≤ ε)
    (hQt : tv Q (fun _ => (Fintype.card X : ℝ)⁻¹) ≤ ε) :
    (1-2*ε) / Fintype.card X ≤ ∑ x, P x * Q x := by
  let w : ℝ := (Fintype.card X : ℝ)⁻¹
  let a (x : X) := w - min (P x) w
  let b (x : X) := w - min (Q x) w
  have ha : ∑ x, a x ≤ ε := (sum_uniform_deficit P hP1).trans hPt
  have hb : ∑ x, b x ≤ ε := (sum_uniform_deficit Q hQ1).trans hQt
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hlocal (x) : w^2-w*(a x+b x) ≤ P x * Q x := by
    have haa : 0 ≤ a x := sub_nonneg.mpr (min_le_right _ _)
    have hbb : 0 ≤ b x := sub_nonneg.mpr (min_le_right _ _)
    have hprod := mul_le_mul (min_le_left (P x) w) (min_le_left (Q x) w)
      (le_min (hQ x) hw) (hP x)
    dsimp [a,b] at *
    nlinarith [mul_nonneg haa hbb]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hlocal x)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, Finset.sum_add_distrib] at hs
  have hcard : (Fintype.card X : ℝ)*w = 1 := by dsimp [w]; simp
  have hdef : w*(∑ x, a x + ∑ x, b x) ≤ w*(2*ε) := mul_le_mul_of_nonneg_left (by linarith) hw
  change (1-2*ε)*w ≤ _
  nlinarith

def squareKernel (K : X → X → ℝ) (x y : X) : ℝ := ∑ z, K x z * K z y

lemma square_minorization (K : X → X → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hrow : ∀ x, ∑ y, K x y = 1) (hcol : ∀ y, ∑ x, K x y = 1) (ε : ℝ)
    (hrowTV : ∀ x, tv (K x) (fun _ => (Fintype.card X : ℝ)⁻¹) ≤ ε)
    (hcolTV : ∀ y, tv (fun x => K x y) (fun _ => (Fintype.card X : ℝ)⁻¹) ≤ ε)
    (x y : X) : (1-2*ε) / Fintype.card X ≤ squareKernel K x y :=
  uniform_overlap (K x) (fun z => K z y) (hK x) (fun z => hK z y)
    (hrow x) (hcol y) ε (hrowTV x) (hcolTV y)

def acceptance (R : X → X → ℝ) (p : ℝ) (x y : X) : ℝ := p / ((Fintype.card X : ℝ)*R x y)

def markedKernel (R : X → X → ℝ) (p : ℝ) (x : X) (z : X × Bool) : ℝ :=
  R x z.1 * (if z.2 then acceptance R p x z.1 else 1-acceptance R p x z.1)

lemma acceptance_bounds (R : X → X → ℝ) (p : ℝ) (hp : 0 < p)
    (hR : ∀ x y, p / Fintype.card X ≤ R x y) (x y : X) :
    0 ≤ acceptance R p x y ∧ acceptance R p x y ≤ 1 := by
  have hn : 0 < (Fintype.card X : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hxy : 0 < R x y := (div_pos hp hn).trans_le (hR x y)
  constructor
  · unfold acceptance; positivity
  · unfold acceptance; apply (div_le_one (mul_pos hn hxy)).mpr
    have hh := (div_le_iff₀ hn).mp (hR x y); nlinarith

lemma marked_true (R : X → X → ℝ) (p : ℝ) (hp : 0 < p)
    (hR : ∀ x y, p / Fintype.card X ≤ R x y) (x y : X) :
    markedKernel R p x (y,true) = p / Fintype.card X := by
  have hn : 0 < (Fintype.card X : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hxy : 0 < R x y := (div_pos hp hn).trans_le (hR x y)
  simp only [markedKernel, ite_true, acceptance]
  field_simp

lemma marked_marginal (R : X → X → ℝ) (p : ℝ) (x y : X) :
    (∑ b : Bool, markedKernel R p x (y,b)) = R x y := by
  let retained_nonempty_X := nonempty_X
  simp [markedKernel]; ring

lemma marked_nonneg (R : X → X → ℝ) (p : ℝ) (hp : 0 < p)
    (hR : ∀ x y, p / Fintype.card X ≤ R x y) (x : X) (z : X × Bool) :
    0 ≤ markedKernel R p x z := by
  have hb := acceptance_bounds R p hp hR x z.1
  have hxy : 0 ≤ R x z.1 := (div_nonneg hp.le (Nat.cast_nonneg _)).trans (hR x z.1)
  unfold markedKernel
  apply mul_nonneg hxy
  cases z.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> linarith

lemma marked_sum (R : X → X → ℝ) (p : ℝ) (hR : ∀ x, ∑ y, R x y = 1) (x : X) :
    ∑ z, markedKernel R p x z = 1 := by rw [Fintype.sum_prod_type]; simp_rw [marked_marginal]; exact hR x

lemma accepted_uniform (R : X → X → ℝ) (p : ℝ) (hp : 0 < p)
    (hR : ∀ x y, p / Fintype.card X ≤ R x y) (x : X) :
    (∑ y, markedKernel R p x (y,true)) = p ∧
      ∀ y, markedKernel R p x (y,true) / p = (Fintype.card X : ℝ)⁻¹ := by
  simp only [marked_true R p hp hR]
  constructor
  · simp; field_simp
  · intro y; field_simp

end Thorp.Conditional.Reset

end

end OAI
