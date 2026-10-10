import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.Cube

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators

lemma mean_congr {n : ℕ} {f g : Cube n → ℝ} (h : ∀ x, f x = g x) : mean f = mean g :=
  congrArg mean (funext h)

lemma sum_succ {n : ℕ} (f : Cube (n+1) → ℝ) :
    ∑ x, f x = (∑ x : Cube n, f (false,x)) + ∑ x : Cube n, f (true,x) := by
  change (∑ x : Bool × Cube n, f x) = _
  rw [Fintype.sum_prod_type]
  simp [add_comm]

noncomputable def fourier : {n : ℕ} → (Cube n → ℝ) → Cube n → ℝ
  | 0, f, x => f x
  | _+1, f, (b,x) => if b then fourier (oddPart f) x else fourier (evenPart f) x

noncomputable def synth : {n : ℕ} → (Cube n → ℝ) → Cube n → ℝ
  | 0, f, x => f x
  | _+1, f, (b,x) => synth (fun s => f (false,s)) x +
      (if b then -1 else 1) * synth (fun s => f (true,s)) x

lemma evenPart_add {n : ℕ} (f g : Cube (n+1) → ℝ) :
    evenPart (fun x => f x + g x) = fun x => evenPart f x + evenPart g x := by
  funext x; dsimp [evenPart]; ring

lemma oddPart_add {n : ℕ} (f g : Cube (n+1) → ℝ) :
    oddPart (fun x => f x + g x) = fun x => oddPart f x + oddPart g x := by
  funext x; dsimp [oddPart]; ring

lemma evenPart_mul {n : ℕ} (c : ℝ) (f : Cube (n+1) → ℝ) :
    evenPart (fun x => c * f x) = fun x => c * evenPart f x := by
  funext x; dsimp [evenPart]; ring

lemma oddPart_mul {n : ℕ} (c : ℝ) (f : Cube (n+1) → ℝ) :
    oddPart (fun x => c * f x) = fun x => c * oddPart f x := by
  funext x; dsimp [oddPart]; ring

lemma fourier_add {n : ℕ} (f g : Cube n → ℝ) :
    fourier (fun x => f x + g x) = fun s => fourier f s + fourier g s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext ⟨b,s⟩
    cases b <;> simp [fourier, evenPart_add, oddPart_add, ih]

lemma fourier_mul {n : ℕ} (c : ℝ) (f : Cube n → ℝ) :
    fourier (fun x => c * f x) = fun s => c * fourier f s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext ⟨b,s⟩
    cases b <;> simp [fourier, evenPart_mul, oddPart_mul, ih]

lemma fourier_sub {n : ℕ} (f g : Cube n → ℝ) :
    fourier (fun x => f x - g x) = fun s => fourier f s - fourier g s := by
  have he : (fun x => f x - g x) = (fun x => f x + -1 * g x) := by
    funext x; ring
  rw [he, fourier_add, fourier_mul]
  funext s; ring

lemma fourier_parseval {n : ℕ} (f : Cube n → ℝ) :
    (∑ s, (fourier f s)^2) = mean (fun x => f x^2) := by
  induction n with
  | zero => simp [fourier, mean_zero]
  | succ n ih =>
    rw [sum_succ, mean_square_split]
    simp only [fourier, Bool.false_eq_true, ↓reduceIte]
    rw [ih, ih]

lemma fourier_inner {n : ℕ} (f g : Cube n → ℝ) :
    (∑ s, fourier f s * fourier g s) = mean (fun x => f x*g x) := by
  induction n with
  | zero => simp [fourier, mean_zero]
  | succ n ih =>
    rw [sum_succ, mean_product_split]
    simp only [fourier, Bool.false_eq_true, ↓reduceIte]
    rw [ih, ih]

lemma synth_fourier {n : ℕ} (f : Cube n → ℝ) : synth (fourier f) = f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext ⟨b,x⟩
    simp only [synth, fourier, Bool.false_eq_true, ↓reduceIte]
    rw [ih, ih]
    cases b <;> dsimp [evenPart, oddPart] <;> ring

lemma evenPart_synth {n : ℕ} (f : Cube (n+1) → ℝ) :
    evenPart (synth f) = synth (fun s => f (false,s)) := by
  funext x; dsimp [evenPart, synth]; ring

lemma oddPart_synth {n : ℕ} (f : Cube (n+1) → ℝ) :
    oddPart (synth f) = synth (fun s => f (true,s)) := by
  funext x; dsimp [oddPart, synth]; ring

lemma fourier_synth {n : ℕ} (f : Cube n → ℝ) : fourier (synth f) = f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext ⟨b,s⟩
    cases b <;> simp only [fourier, Bool.false_eq_true, ↓reduceIte,
      evenPart_synth, oddPart_synth, ih]

def bit : {n : ℕ} → Cube n → Fin n → Bool
  | _+1, (b,x), i => Fin.cases b (bit x) i

def degree : {n : ℕ} → Cube n → ℕ
  | 0, _ => 0
  | _+1, (b,x) => (if b then 1 else 0) + degree x

lemma fourier_noise {n : ℕ} (ρ : ℝ) (f : Cube n → ℝ) :
    fourier (noise ρ f) = fun s => ρ^(degree s) * fourier f s := by
  induction n with
  | zero => funext s; simp [noise, fourier, degree]
  | succ n ih =>
    funext ⟨b,s⟩
    cases b <;> simp [fourier, evenPart_noise, oddPart_noise, fourier_mul,
      ih, degree, pow_add, mul_assoc]

def flip : {n : ℕ} → Fin n → Cube n → Cube n
  | _+1, i, (b,x) => Fin.cases (!b,x) (fun j => (b,flip j x)) i

noncomputable def diff {n : ℕ} (i : Fin n) (f : Cube n → ℝ) (x : Cube n) : ℝ :=
  (f x - f (flip i x))/2

lemma evenPart_diff_zero {n : ℕ} (f : Cube (n+1) → ℝ) :
    evenPart (diff 0 f) = fun _ => 0 := by
  funext x
  simp only [evenPart, diff, flip, Fin.cases_zero, Bool.not_false, Bool.not_true]
  ring

lemma oddPart_diff_zero {n : ℕ} (f : Cube (n+1) → ℝ) :
    oddPart (diff 0 f) = oddPart f := by
  funext x
  simp only [oddPart, diff, flip, Fin.cases_zero, Bool.not_false, Bool.not_true]
  ring

lemma evenPart_diff_succ {n : ℕ} (i : Fin n) (f : Cube (n+1) → ℝ) :
    evenPart (diff i.succ f) = diff i (evenPart f) := by
  funext x
  dsimp [evenPart, diff, flip]
  ring

lemma oddPart_diff_succ {n : ℕ} (i : Fin n) (f : Cube (n+1) → ℝ) :
    oddPart (diff i.succ f) = diff i (oddPart f) := by
  funext x
  dsimp [oddPart, diff, flip]
  ring

lemma fourier_zero {n : ℕ} : fourier (fun _ : Cube n => (0:ℝ)) = fun _ => 0 := by
  have h := fourier_mul (n := n) 0 (fun _ => 0)
  simpa only [zero_mul] using h

lemma fourier_diff {n : ℕ} (i : Fin n) (f : Cube n → ℝ) :
    fourier (diff i f) = fun s => if bit s i then fourier f s else 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    funext ⟨b,s⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · cases b <;> simp [fourier, bit, evenPart_diff_zero, oddPart_diff_zero, fourier_zero]
    · cases b <;> simp [fourier, bit, evenPart_diff_succ, oddPart_diff_succ, ih]

end LargeIndependentSets.BooleanJunta

end OAI
