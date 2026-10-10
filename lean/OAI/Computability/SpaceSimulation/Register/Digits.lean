import OAI.Computability.SpaceSimulation.Register.Arithmetic

namespace OAI

/-! Little-endian packed buffers. -/
namespace Fifths

namespace Radix
def pack (m : ℕ) (d : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => pack m d n + m^n * d n

def get (m u j : ℕ) : ℕ := u / m^j % m

theorem get_lt {m : ℕ} (h : 0 < m) (u j) : get m u j < m :=
  Nat.mod_lt _ h
theorem get_zero (m u : ℕ) : get m u 0 = u%m := by simp [get]
theorem get_succ (m u j : ℕ) : get m u (j+1) = get m (u/m) j := by
  simp only [get,Nat.div_div_eq_div_mul,pow_succ']

theorem pack_lt {m : ℕ} (_h : 0 < m) (d : ℕ → ℕ) (n : ℕ)
    (o : ∀ i < n, d i < m) : pack m d n < m^n := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    have a := ih (fun i l => o i (by omega))
    have b := o n (by omega)
    rw [pack,pow_succ]
    calc
      _ < m^n + m^n * d n := by omega
      _ = m^n * (d n+1) := by ring
      _ ≤ _ := by gcongr; omega

theorem pack_cons (m : ℕ) (d : ℕ → ℕ) (n : ℕ) :
    pack m d (n+1) = d 0 + m * pack m (fun i => d (i+1)) n := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    rw [pack,ih,pack,pow_succ]
    ring

theorem get_pack {m : ℕ} (h : 0 < m) (d : ℕ → ℕ) (n : ℕ)
    (o : ∀ i < n, d i < m) {i} (l : i < n) :
    get m (pack m d n) i = d i := by
  induction n generalizing d i with
  | zero => omega
  | succ n ih =>
    rw [pack_cons]
    cases i with
    | zero =>
      simp [get_zero,Nat.mod_eq_of_lt (o _ (by omega))]
    | succ i =>
      rw [get_succ]
      have e (p) : (d 0 + m*p)/m = p := by
        simp [Nat.add_mul_div_left, h, o 0 (by omega)]
      rw [e]
      exact ih _ (fun k j => o _ (by omega)) (by omega)

theorem pack_get {m : ℕ} (h : 0 < m) (u n : ℕ) (l : u < m^n) :
    pack m (get m u) n = u := by
  induction n generalizing u with
  | zero => simp at l; simp [pack,l]
  | succ n ih =>
    rw [pack_cons,get_zero]
    simp only [get_succ]
    rw [ih _ ((Nat.div_lt_iff_lt_mul h).mpr (by rwa [pow_succ] at l))]
    exact Nat.mod_add_div u m

theorem pack_congr {m n : ℕ} {d e : ℕ → ℕ} (h : ∀ i < n, d i = e i) :
    pack m d n = pack m e n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pack,pack,h n (by omega), ih (fun i hi => h i (by omega))]

theorem ext {m : ℕ} (h : 0 < m) {u v n : ℕ} (l : u < m^n) (o : v < m^n)
    (p : ∀ i < n, get m u i = get m v i) : u = v :=
  (pack_get h _ _ l).symm.trans ((pack_congr p).trans (pack_get h _ _ o))
end Radix

namespace Comp
open Radix
variable {X I : Type} {x : I → List X} {S a m u b : I → ℕ}

/-- Supplied powers of a computable base are computable when the resulting
integer fits. -/
theorem digit (p : Comp x S a m) (q : Comp x S a u) (h : Comp x S a b)
    (l : Fits S (fun i => m i ^ b i)) :
    Comp x S a (fun i => get (m i) (u i) (b i)) :=
  (q.div (p.pow h l)).mod p

theorem digits (p : Comp x S a m) (q : Comp x S a b)
    (l : Fits S (fun i => m i ^ b i)) (g : ∀ i, 0 < m i)
    (d : I → ℕ → ℕ) (o : ∀ i j, j < b i → d i j < m i)
    (h : ∀ e : Before b → ℕ,
      Comp (fun i => x i.1.1) (fun i => S i.1.1) e (fun i => a i.1.1) →
      Comp (fun i => x i.1.1) (fun i => S i.1.1) e (fun i => i.1.2) →
      Comp (fun i => x i.1.1) (fun i => S i.1.1) e (fun i => d i.1.1 i.1.2)) :
    Comp x S a (fun i => pack (m i) (d i) (b i)) := by
  apply fold (fun i j => pack (m i) (d i) j) q (Comp.constant p.source 0)
  · let f : Through b → I := fun i => i.1.1
    refine (l.pull f).mono (fun i => Nat.le_of_lt ?_)
    exact lt_of_lt_of_le
      (pack_lt (g _) (d (f i)) _ (fun j l => o _ j (lt_of_lt_of_le l i.2)))
      (Nat.pow_le_pow_right (g _) i.2)
  intro e i j k
  let f : Before b → I := fun i => i.1.1
  have h₀ := i.trans (p.pull f)
  have v := h₀.pow j ((l.pull f).mono
    (fun i => Nat.pow_le_pow_right (g _) i.2.le))
  exact k.add (v.mul (h _ i j))
end Comp
end Fifths

end OAI
