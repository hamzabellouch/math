import Mathlib
import OAI.Combinatorics.UniformKServer.BitSampling

namespace OAI

namespace UniformKServer.BitSampling

noncomputable def mean {A : Type*} [Fintype A] (v : A → ℝ) : ℝ :=
  (∑ a, v a) / Fintype.card A

def runCost {S R : Type*} {k b : ℕ} (N : S → R → Fin k → ℕ)
    (hN : ∀ s r, ∑ j, N s r j = 2^b) (next : S → R → Fin k → S)
    (charge : S → R → Fin k → ℝ) :
    (s : S) → (w : List R) → (Fin w.length → Fin b → Bool) → ℝ
  | _, [], _ => 0
  | s, r::w, coins =>
    let j := row (N s r) (hN s r) (coins 0)
    charge s r j + runCost N hN next charge (next s r j) w (Fin.tail coins)

noncomputable def rowCost {S R : Type*} {k b : ℕ} (N : S → R → Fin k → ℕ)
    (next : S → R → Fin k → S) (charge : S → R → Fin k → ℝ) : S → List R → ℝ
  | _, [] => 0
  | s, r::w => ∑ j, (N s r j : ℝ) / (2^b : ℕ) *
    (charge s r j + rowCost (b:=b) N next charge (next s r j) w)

theorem mean_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (v : B → ℝ) : mean (fun a => v (e a)) = mean v := by
  unfold mean
  rw [e.sum_comp, Fintype.card_congr e]

theorem mean_add {A : Type*} [Fintype A] (f g : A → ℝ) :
    mean (fun a => f a + g a) = mean f + mean g := by
  simp only [mean, Finset.sum_add_distrib, add_div]

theorem mean_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    mean (fun _ : A => c) = c := by
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero (α:=A))
  simp [mean, hc]

theorem mean_prod {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    mean f = mean (fun a => mean (fun b => f (a,b))) := by
  simp only [mean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  rw [mul_comm (Fintype.card A : ℝ), div_mul_eq_div_div, Finset.sum_div]

theorem mean_row {k b : ℕ} (N : Fin k → ℕ) (hN : ∑ j, N j = 2^b)
    (f : Fin k → ℝ) : mean (fun coins => f (row N hN coins)) =
      ∑ j, (N j : ℝ) / (2^b : ℕ) * f j := by
  simpa only [mean, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using
    (exact_row N hN).2.2 f

theorem bit_path_mean_proof {S R : Type*} {k b : ℕ} (N : S → R → Fin k → ℕ)
    (hN : ∀ s r, ∑ j, N s r j = 2^b) (next : S → R → Fin k → S)
    (charge : S → R → Fin k → ℝ) (s : S) (w : List R) :
    mean (runCost N hN next charge s w) = rowCost (b:=b) N next charge s w := by
  induction w generalizing s with
  | nil => simp [mean, runCost, rowCost]
  | cons r w ih =>
    let e := Fin.consEquiv (fun _ : Fin (w.length+1) => Fin b → Bool)
    calc
      mean (runCost N hN next charge s (r::w)) =
          mean (fun p : (Fin b → Bool) × (Fin w.length → Fin b → Bool) =>
            charge s r (row (N s r) (hN s r) p.1) +
              runCost N hN next charge (next s r (row (N s r) (hN s r) p.1)) w p.2) := by
        have he := mean_equiv e (runCost N hN next charge s (r::w))
        simpa only [e, runCost, Fin.consEquiv, Equiv.coe_fn_mk,
          Fin.cons_zero, Fin.tail_cons] using he.symm
      _ = mean (fun coin : Fin b → Bool =>
          mean (fun rest : Fin w.length → Fin b → Bool =>
            charge s r (row (N s r) (hN s r) coin) +
              runCost N hN next charge (next s r (row (N s r) (hN s r) coin)) w rest)) := mean_prod _
      _ = mean (fun coin : Fin b → Bool =>
          charge s r (row (N s r) (hN s r) coin) +
            rowCost (b:=b) N next charge (next s r (row (N s r) (hN s r) coin)) w) := by
        congr 1
        funext coin
        rw [mean_add, mean_const, ih]
      _ = rowCost (b:=b) N next charge s (r::w) := by
        exact mean_row (N s r) (hN s r)
          (fun j => charge s r j + rowCost (b:=b) N next charge (next s r j) w)

-- The full finite tape has exactly b fresh unbiased bits per request.
theorem bit_path_mean {S R : Type*} {k b : ℕ} (N : S → R → Fin k → ℕ)
    (hN : ∀ s r, ∑ j, N s r j = 2^b) (next : S → R → Fin k → S)
    (charge : S → R → Fin k → ℝ) (s : S) (w : List R) :
    mean (runCost N hN next charge s w) = rowCost (b:=b) N next charge s w := by
  exact bit_path_mean_proof N hN next charge s w

end UniformKServer.BitSampling



end OAI
