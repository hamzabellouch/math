import Mathlib

namespace OAI



section

namespace ExactQuantumFactoring

/-- A worst-case bound for all input lengths, with nonnegative coefficients. -/
def PolyBound (f : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval n

namespace PolyBound
lemma const (c : ℕ) : PolyBound (fun _ => c) :=
  ⟨Polynomial.C c, fun _ => by simp⟩
lemma id : PolyBound (fun n => n) := ⟨Polynomial.X, fun _ => by simp⟩
lemma add {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => f n + g n) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  exact ⟨p+q, fun n => by simpa using Nat.add_le_add (hp n) (hq n)⟩
lemma mul {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => f n * g n) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  exact ⟨p*q, fun n => by simpa using Nat.mul_le_mul (hp n) (hq n)⟩
lemma pow {f : ℕ → ℕ} (hf : PolyBound f) (k : ℕ) :
    PolyBound (fun n => f n ^ k) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p^k, fun n => by simpa using Nat.pow_le_pow_left (hp n) k⟩
lemma of_le {f g : ℕ → ℕ} (hg : PolyBound g) (h : ∀ n, f n ≤ g n) : PolyBound f := by
  obtain ⟨p,hp⟩ := hg
  exact ⟨p, fun n => (h n).trans (hp n)⟩
lemma max {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => max (f n) (g n)) :=
  (hf.add hg).of_le (fun _ => Nat.max_le.mpr ⟨Nat.le_add_right _ _,Nat.le_add_left _ _⟩)
lemma sub {f g : ℕ → ℕ} (hf : PolyBound f) : PolyBound (fun n => f n-g n) :=
  hf.of_le (fun _ => Nat.sub_le _ _)
lemma div {f g : ℕ → ℕ} (hf : PolyBound f) : PolyBound (fun n => f n/g n) :=
  hf.of_le (fun _ => Nat.div_le_self _ _)
lemma mod {f g : ℕ → ℕ} (hf : PolyBound f) : PolyBound (fun n => f n%g n) :=
  hf.of_le (fun _ => Nat.mod_le _ _)
lemma ite {f g : ℕ → ℕ} (p : ℕ → Prop) [∀ n, Decidable (p n)]
    (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => if p n then f n else g n) :=
  (hf.max hg).of_le (fun n => by split_ifs <;> omega)

lemma eval_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  change p.eval a ≤ p.eval b
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i))

lemma comp {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => f (g n)) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  refine ⟨p.comp q, fun n => ?_⟩
  rw [Polynomial.eval_comp]
  exact (hp (g n)).trans (eval_mono p (hq n))

lemma natSize {f : ℕ → ℕ} (hf : PolyBound f) : PolyBound (fun n => (f n).size) :=
  hf.of_le (fun _ => Nat.size_le.mpr (Nat.lt_two_pow_self))
end PolyBound

syntax "poly_bound" : tactic
macro_rules
  | `(tactic| poly_bound) => `(tactic|
    first
    | assumption
    | exact PolyBound.id
    | exact PolyBound.const _
    | (apply PolyBound.add <;> poly_bound)
    | (apply PolyBound.mul <;> poly_bound)
    | (apply PolyBound.pow <;> poly_bound)
    | (apply PolyBound.max <;> poly_bound)
    | (apply PolyBound.sub <;> poly_bound)
    | (apply PolyBound.div <;> poly_bound)
    | (apply PolyBound.mod <;> poly_bound)
    | (apply PolyBound.natSize <;> poly_bound))



end ExactQuantumFactoring

end



end OAI
