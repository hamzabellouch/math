import OAI.Combinatorics.Ryser.Probability.Product
import OAI.Combinatorics.Ryser.Probability.RareAnchor
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

namespace RyserCoveringCounterexample.Exposure

open scoped BigOperators

variable {Omega : Type*} [instFintypeOmega : Fintype Omega]

def splitConfig (n : Nat) :
    (Fin (n + 1) → Omega) ≃ Omega × (Fin n → Omega) where
  toFun w := (w 0, fun i => w i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv w := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by
    rcases p with ⟨x, tail⟩
    rfl

theorem cons_head_tail {n : Nat} (w : Fin (n + 1) → Omega) :
    Fin.cons (w 0) (fun i => w i.succ) = w := let _ := instFintypeOmega;
  (splitConfig n).left_inv w

def headMean {n : Nat} (mu : Fin (n + 1) → FiniteLaw Omega)
    (f : (Fin (n + 1) → Omega) → ℝ) (x : Omega) : ℝ :=
  (FiniteLaw.pi (fun i : Fin n => mu i.succ)).expectation
    (fun tail => f (Fin.cons x tail))

theorem expectation_pi_succ {n : Nat}
    (mu : Fin (n + 1) → FiniteLaw Omega)
    (f : (Fin (n + 1) → Omega) → ℝ) :
    (FiniteLaw.pi mu).expectation f =
      (mu 0).expectation (headMean mu f) := by
  classical
  change (∑ w, (∏ i, (mu i).weight (w i)) * f w) =
    ∑ x, (mu 0).weight x *
      (∑ tail : Fin n → Omega,
        (∏ i, (mu i.succ).weight (tail i)) * f (Fin.cons x tail))
  calc
    _ = ∑ p : Omega × (Fin n → Omega),
        ((mu 0).weight p.1 * ∏ i, (mu i.succ).weight (p.2 i)) *
          f (Fin.cons p.1 p.2) := by
      refine Fintype.sum_equiv (splitConfig n) _ _ ?_
      intro w
      change (∏ i, (mu i).weight (w i)) * f w =
        ((mu 0).weight (w 0) * ∏ i : Fin n, (mu i.succ).weight (w i.succ)) *
          f (Fin.cons (w 0) (fun i => w i.succ))
      rw [cons_head_tail, Fin.prod_univ_succ]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tail _
      ring

def ExposureBounds (M : ℝ) : (n : Nat) →
    (Fin n → FiniteLaw Omega) → ((Fin n → Omega) → ℝ) →
    (Fin n → ℝ) → Prop
  | 0, _, _, _ => True
  | n + 1, mu, f, v =>
      (∀ x, |headMean mu f x - (mu 0).expectation (headMean mu f)| ≤ M) ∧
      (mu 0).expectation
        (fun x => (headMean mu f x - (mu 0).expectation (headMean mu f)) ^ 2)
        ≤ v 0 ∧
      ∀ x, ExposureBounds M n (fun i => mu i.succ)
        (fun tail => f (Fin.cons x tail)) (fun i => v i.succ)

theorem mean_difference_bound {A : Type*} [Fintype A]
    (p : FiniteLaw A) (f g : A → ℝ) (C : ℝ)
    (h : ∀ a, |f a - g a| ≤ C) :
    |p.expectation f - p.expectation g| ≤ C := by
  have hlo : p.expectation (fun a => g a - C) ≤ p.expectation f := by
    apply p.expectation_mono
    intro a
    have hh := (abs_le.mp (h a)).1
    linarith
  have hhi : p.expectation f ≤ p.expectation (fun a => g a + C) := by
    apply p.expectation_mono
    intro a
    have hh := (abs_le.mp (h a)).2
    linarith
  rw [FiniteLaw.expectation_sub, FiniteLaw.expectation_const] at hlo
  rw [FiniteLaw.expectation_add, FiniteLaw.expectation_const] at hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem second_moment_le {A : Type*} [Fintype A]
    (p : FiniteLaw A) (f : A → ℝ) (C : ℝ)
    (h : ∀ a, |f a| ≤ C) :
    p.expectation (fun a => (f a) ^ 2) ≤ C ^ 2 := by
  calc
    _ ≤ p.expectation (fun _ => C ^ 2) := by
      apply p.expectation_mono
      intro a
      rcases abs_le.mp (h a) with ⟨hl, hu⟩
      have hp : 0 ≤ (C - f a) * (C + f a) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    _ = C ^ 2 := p.expectation_const _

theorem update_cons_zero {n : Nat} (x y : Omega) (tail : Fin n → Omega) :
    Function.update
        (Fin.cons (n := let _ := instFintypeOmega; n) (α := fun _ : Fin (n + 1) => Omega) x tail) 0 y =
      Fin.cons (n := n) (α := fun _ : Fin (n + 1) => Omega) y tail :=
  Fin.update_cons_zero (n := n) (α := fun _ : Fin (n + 1) => Omega) x tail y

theorem cons_update {n : Nat} (x y : Omega) (tail : Fin n → Omega) (i : Fin n) :
    Fin.cons (n := let _ := instFintypeOmega; n) (α := fun _ : Fin (n + 1) => Omega) x
        (Function.update tail i y) =
      Function.update
        (Fin.cons (n := n) (α := fun _ : Fin (n + 1) => Omega) x tail) i.succ y :=
  Fin.cons_update (n := n) (α := fun _ : Fin (n + 1) => Omega) x tail i y

theorem exposureBounds_of_coordinateBound (M : ℝ) (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (c : Fin n → ℝ)
    (hcoord : ∀ i w x, |f (Function.update w i x) - f w| ≤ c i)
    (hM : ∀ i, c i ≤ M) :
    ExposureBounds M n mu f (fun i => (c i) ^ 2) := by
  classical
  induction n with
  | zero => trivial
  | succ n ih =>
    have hdiam (x y : Omega) :
        |headMean mu f x - headMean mu f y| ≤ c 0 := by
      apply mean_difference_bound
      intro tail
      simpa only [update_cons_zero] using hcoord 0 (Fin.cons y tail) x
    have hcenter (x : Omega) :
        |headMean mu f x - (mu 0).expectation (headMean mu f)| ≤ c 0 := by
      have hh := mean_difference_bound (mu 0) (fun _ => headMean mu f x)
        (headMean mu f) (c 0) (hdiam x)
      simpa only [FiniteLaw.expectation_const] using hh
    refine ⟨fun x => (hcenter x).trans (hM 0), ?_, ?_⟩
    · exact second_moment_le (mu 0)
        (fun x => headMean mu f x - (mu 0).expectation (headMean mu f))
        (c 0) hcenter
    · intro x
      refine ih (fun i => mu i.succ) (fun tail => f (Fin.cons x tail))
        (fun i => c i.succ) ?_ (fun i => hM i.succ)
      intro i tail y
      simpa only [cons_update] using hcoord i.succ (Fin.cons x tail) y

theorem exposureBounds_of_rareAnchor (M : ℝ) (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (e : Omega) (C r : Fin n → ℝ) (rare : Fin n → Omega → Prop)
    (hanchor : ∀ i w, |f w - f (Function.update w i e)| ≤ C i)
    (houtside : ∀ i w, ¬ rare i (w i) → f w = f (Function.update w i e))
    (hrare : ∀ i, (mu i).prob (rare i) ≤ r i)
    (hM : ∀ i, 2 * C i ≤ M) :
    ExposureBounds M n mu f (fun i => (C i) ^ 2 * r i) := by
  classical
  induction n with
  | zero => trivial
  | succ n ih =>
    have hhead (x : Omega) :
        |headMean mu f x - headMean mu f e| ≤ C 0 := by
      apply mean_difference_bound
      intro tail
      simpa only [update_cons_zero] using hanchor 0 (Fin.cons x tail)
    have hheadoutside (x : Omega) (hx : ¬ rare 0 x) :
        headMean mu f x = headMean mu f e := by
      apply congrArg ((FiniteLaw.pi (fun i : Fin n => mu i.succ)).expectation)
      funext tail
      simpa only [update_cons_zero] using houtside 0 (Fin.cons x tail) hx
    rcases FiniteLaw.rareAnchor_centering (mu 0) (headMean mu f)
      (headMean mu f e) (C 0) (r 0) (rare 0) hhead hheadoutside (hrare 0)
      with ⟨hzero, hcenter, hsecond⟩
    refine ⟨fun x => (hcenter x).trans (hM 0), hsecond, ?_⟩
    intro x
    refine ih (fun i => mu i.succ) (fun tail => f (Fin.cons x tail))
      (fun i => C i.succ) (fun i => r i.succ) (fun i => rare i.succ)
      ?_ ?_ (fun i => hrare i.succ) (fun i => hM i.succ)
    · intro i tail
      simpa only [cons_update] using hanchor i.succ (Fin.cons x tail)
    · intro i tail hnot
      simpa only [cons_update] using houtside i.succ (Fin.cons x tail) hnot

end RyserCoveringCounterexample.Exposure

end OAI
