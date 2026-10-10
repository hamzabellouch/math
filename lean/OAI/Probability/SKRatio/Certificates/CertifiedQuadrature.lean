import Mathlib
import OAI.Probability.SKRatio.Certificates.CertifiedJet

namespace OAI

noncomputable section
open Real Set MeasureTheory
namespace SKRatio.Certificate

namespace Box

def absUpper (A : Box) : ℚ := max |A.lo| |A.hi|
def widen (A : Box) (r : ℚ) : Box := ⟨A.lo-r,A.hi+r⟩

def contains (A B : Box) : Bool := decide (A.lo ≤ B.lo ∧ B.hi ≤ A.hi)

lemma mem_of_contains {A B : Box} {x : ℝ} (h : contains A B=true) (hx : x ∈ B) : x ∈ A := by
  have h' : A.lo ≤ B.lo ∧ B.hi ≤ A.hi := of_decide_eq_true h
  have hl : (A.lo:ℝ) ≤ B.lo := by exact_mod_cast h'.1
  have hu : (B.hi:ℝ) ≤ A.hi := by exact_mod_cast h'.2
  exact ⟨hl.trans hx.1,hx.2.trans hu⟩

lemma absUpper_nonneg (A : Box) : (0:ℝ) ≤ A.absUpper := by
  exact_mod_cast (abs_nonneg A.lo).trans (le_max_left |A.lo| |A.hi|)

lemma abs_le_absUpper {A : Box} {x : ℝ} (hx : x ∈ A) : |x| ≤ A.absUpper := by
  have hl : |(A.lo:ℝ)| ≤ (A.absUpper:ℝ) := by simp [absUpper]
  have hu : |(A.hi:ℝ)| ≤ (A.absUpper:ℝ) := by simp [absUpper]
  exact abs_le.mpr ⟨by linarith [hx.1,(abs_le.mp hl).1],by linarith [hx.2,(abs_le.mp hu).2]⟩

lemma mem_widen {A : Box} {x y : ℝ} {r : ℚ} (hx : x ∈ A) (hy : |x-y| ≤ (r:ℝ)) : y ∈ widen A r := by
  change (A.lo-r:ℚ) ≤ y ∧ y ≤ (A.hi+r:ℚ)
  push_cast
  obtain ⟨hy0,hy1⟩ := abs_le.mp hy
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
end Box

lemma trapezoid_bound {f f' f'' : ℝ → ℝ} {a b M : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc a b, HasDerivAt f' (f'' x) x)
    (hM : 0 ≤ M) (hb : ∀ x ∈ Icc a b, |f'' x| ≤ M) :
    |(b-a)/2*(f a+f b)-(∫ x in a..b, f x)| ≤ (b-a)^3*M/12 := by
  have hud := uniqueDiffOn_Icc hab
  have hd : EqOn (derivWithin f (Icc a b)) f' (Icc a b) := fun x hx =>
    (hf x hx).hasDerivWithinAt.derivWithin (hud x hx)
  have hdd : DifferentiableOn ℝ (derivWithin f (Icc a b)) (Icc a b) :=
    (show DifferentiableOn ℝ f' (Icc a b) from
      fun x hx => (hf' x hx).differentiableAt.differentiableWithinAt).congr hd
  have h2 : ∀ x, |iteratedDerivWithin 2 f (Icc a b) x| ≤ M := by
    intro x
    rw [iteratedDerivWithin_succ',iteratedDerivWithin_succ',iteratedDerivWithin_zero]
    by_cases hx : x ∈ Icc a b
    · rw [derivWithin_congr hd (hd hx), (hf' x hx).hasDerivWithinAt.derivWithin (hud x hx)]
      exact hb x hx
    · rw [derivWithin_zero_of_notMem_closure (by simpa using hx), abs_zero]
      exact hM
  have h := trapezoidal_error_le (f := f) (a := a) (b := b)
    (by rw [uIcc_of_lt hab]; exact fun x hx => (hf x hx).differentiableAt.differentiableWithinAt)
    (by rwa [uIcc_of_lt hab]) (ζ := M) (by rwa [uIcc_of_lt hab]) (N := 1) (by decide)
  simpa [trapezoidal_error,trapezoidal_integral_one,abs_of_pos (sub_pos.mpr hab)] using h

namespace Expr

def cell (e : Expr) (a b : ℚ) : Option Box := do
  if ¬a<b then none else
    let JA ← e.compute (Box.rat a)
    let JB ← e.compute (Box.rat b)
    let J ← e.compute ⟨a,b⟩
    return Box.widen (Box.mul (Box.rat ((b-a)/2)) (Box.add JA.val JB.val))
      ((b-a)^3 * J.sec.absUpper/12)

lemma cell_sound (e : Expr) {a b : ℚ} {A : Box} (hc : e.cell a b=some A) :
    IntervalIntegrable e.val volume a b ∧ (∫ x in (a:ℝ)..b, e.val x) ∈ A := by
  unfold cell at hc
  split_ifs at hc with hab
  have hab' : (a:ℝ) < b := by exact_mod_cast hab
  simp only [bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at hc
  obtain ⟨JA,hJA,JB,hJB,J,hJ,rfl⟩ := hc
  have hA := e.compute_sound hJA (Box.mem_rat a)
  have hB := e.compute_sound hJB (Box.mem_rat b)
  have hI (x : ℝ) (hx : x ∈ Icc (a:ℝ) b) := e.compute_sound hJ hx
  have hf (x : ℝ) (hx : x ∈ Icc (a:ℝ) b) := (e.derivatives x (hI x hx).2.2.2).1
  have hf' (x : ℝ) (hx : x ∈ Icc (a:ℝ) b) := (e.derivatives x (hI x hx).2.2.2).2
  refine ⟨(show ContinuousOn e.val (Icc (a:ℝ) b) from
      fun x hx => (hf x hx).continuousAt.continuousWithinAt).intervalIntegrable_of_Icc hab'.le,?_⟩
  have ht := Box.mem_mul (Box.mem_rat ((b-a)/2)) (Box.mem_add hA.1 hB.1)
  apply Box.mem_widen ht
  push_cast
  exact trapezoid_bound hab' hf hf' (Box.absUpper_nonneg J.sec)
    (fun x hx => Box.abs_le_absUpper (hI x hx).2.2.1)

def quad (e : Expr) (h : ℚ) : ℕ → ℚ → Option Box
  | 0,_ => some (Box.rat 0)
  | n+1,a => do
    let A ← e.cell a (a+h)
    let B ← e.quad h n (a+h)
    return Box.add A B

lemma quad_sound (e : Expr) {h a : ℚ} {n : ℕ} {A : Box}
    (hc : e.quad h n a=some A) :
    IntervalIntegrable e.val volume a (a+n*h:ℚ) ∧
      (∫ x in (a:ℝ)..(a+n*h:ℚ), e.val x) ∈ A := by
  induction n generalizing A a with
  | zero =>
    simp only [quad,Option.some.injEq] at hc
    cases hc
    simp only [Nat.cast_zero,zero_mul,add_zero,IntervalIntegrable.refl,intervalIntegral.integral_same]
    exact ⟨trivial,by simpa only [Rat.cast_zero] using Box.mem_rat 0⟩
  | succ n hn =>
    simp only [quad,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at hc
    obtain ⟨B,hB,C,hC,rfl⟩ := hc
    obtain ⟨hi,hm⟩ := e.cell_sound hB
    obtain ⟨hi',hm'⟩ := hn hC
    have hh : a+h+(n:ℚ)*h = a+(n+1:ℕ)*h := by push_cast; ring
    rw [hh] at hi' hm'
    refine ⟨hi.trans hi',?_⟩
    rw [←intervalIntegral.integral_add_adjacent_intervals hi hi']
    exact Box.mem_add hm hm'

def check (e : Expr) (a h : ℚ) (n : ℕ) (A : Box) : Bool :=
  match e.quad h n a with
  | none => false
  | some B => A.contains B

lemma check_sound (e : Expr) {a h : ℚ} {n : ℕ} {A : Box}
    (hc : e.check a h n A=true) :
    IntervalIntegrable e.val volume a (a+n*h:ℚ) ∧
      (∫ x in (a:ℝ)..(a+n*h:ℚ), e.val x) ∈ A := by
  unfold check at hc
  split at hc
  · contradiction
  · rename_i B hB
    obtain ⟨hi,hm⟩ := e.quad_sound hB
    exact ⟨hi,Box.mem_of_contains hc hm⟩

end Expr
end SKRatio.Certificate

end

end OAI
