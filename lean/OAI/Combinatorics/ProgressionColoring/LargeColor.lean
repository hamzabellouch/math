import OAI.Combinatorics.ProgressionColoring.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

namespace QuantitativeVanDerWaerden
namespace LargeColor

open scoped BigOperators

def half (b u : ℕ) : Bool := decide (u < (b + 1) / 2)

/-- The same-half bound is strict for both even and odd bases. -/
theorem half_coefficient_bound {b x y z : ℕ} (_hb : 2 ≤ b)
    (hx : x < b) (hy : y < b) (hz : z < b)
    (hxy : half b x = half b y) (hzy : half b z = half b y) :
    |(x : ℤ) - 2 * y + z| < b := by
  rw [abs_lt]
  by_cases h₁ : x < (b + 1) / 2 <;>
    by_cases h₂ : y < (b + 1) / 2 <;>
    by_cases h₃ : z < (b + 1) / 2 <;>
    simp_all [half] <;> omega

/-- A zero base expansion with signed coefficients strictly smaller than
the base has all coefficients zero. -/
theorem coefficients_zero {b : ℕ} (hb : 2 ≤ b) :
    ∀ {s : ℕ} (a : Fin s → ℤ),
      (∀ i, |a i| < (b : ℤ)) →
      (∑ i, a i * (b : ℤ) ^ (i : ℕ)) = 0 → ∀ i, a i = 0 := by
  intro s
  induction s with
  | zero => intro a ha hs i; exact i.elim0
  | succ s ih =>
    intro a ha hs
    have hsplit : a 0 + (b : ℤ) *
        (∑ i : Fin s, a i.succ * (b : ℤ) ^ (i : ℕ)) = 0 := by
      calc
        _ = ∑ i : Fin (s + 1), a i * (b : ℤ) ^ (i : ℕ) := by
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
          rw [Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = 0 := hs
    have hdiv : (b : ℤ) ∣ a 0 := by
      refine ⟨-(∑ i : Fin s, a i.succ * (b : ℤ) ^ (i : ℕ)), ?_⟩
      linarith [hsplit]
    have hzero : a 0 = 0 := Int.eq_zero_of_abs_lt_dvd hdiv (ha 0)
    have htail : (∑ i : Fin s, a i.succ * (b : ℤ) ^ (i : ℕ)) = 0 := by
      rw [hzero, zero_add] at hsplit
      exact (mul_eq_zero.mp hsplit).resolve_left (by exact_mod_cast (by omega : b ≠ 0))
    intro i
    refine Fin.cases hzero (fun j => ?_) i
    exact ih (fun j : Fin s => a j.succ) (fun j => ha j.succ) htail j

/-- Equal sums of squares and a coordinatewise midpoint force equality. -/
theorem equal_of_midpoint_equal_norm {s : ℕ} (x y z : Fin s → ℤ)
    (hm : ∀ i, x i - 2 * y i + z i = 0)
    (hxy : (∑ i, x i ^ 2) = ∑ i, y i ^ 2)
    (hzy : (∑ i, z i ^ 2) = ∑ i, y i ^ 2) : x = y := by
  have hsq : (∑ i, (x i - z i) ^ 2) = 0 := by
    calc
      _ = ∑ i, (2 * x i ^ 2 + 2 * z i ^ 2 - 4 * y i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hmid : x i + z i = 2 * y i := by linarith [hm i]
        have hmidSq := congrArg (fun t : ℤ => t ^ 2) hmid
        nlinarith [hmidSq]
      _ = 2 * (∑ i, x i ^ 2) + 2 * (∑ i, z i ^ 2) -
          4 * (∑ i, y i ^ 2) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      _ = 0 := by rw [hxy, hzy]; ring
  funext i
  have hi : (x i - z i) ^ 2 ≤ ∑ j, (x j - z j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j - z j)) (Finset.mem_univ i)
  rw [hsq] at hi
  have hxz : x i = z i := by nlinarith [sq_nonneg (x i - z i)]
  linarith [hm i]

def normSq {b s : ℕ} (x : Fin s → Fin b) : ℕ := ∑ i, (x i).val ^ 2

theorem normSq_le {b s : ℕ} (x : Fin s → Fin b) :
    normSq x ≤ s * (b - 1) ^ 2 := by
  calc
    _ ≤ ∑ _i : Fin s, (b - 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hx : (x i).val ≤ b - 1 := by have := (x i).isLt; omega
      exact Nat.pow_le_pow_left hx 2
    _ = _ := by simp

abbrev Color (b s : ℕ) := (Fin s → Bool) × Fin (s * (b - 1) ^ 2 + 1)

def vectorColor {b s : ℕ} (x : Fin s → Fin b) : Color b s :=
  (fun i => half b (x i).val, ⟨normSq x, Nat.lt_succ_of_le (normSq_le x)⟩)

theorem card_color (b s : ℕ) :
    Fintype.card (Color b s) = 2 ^ s * (s * (b - 1) ^ 2 + 1) := by
  simp [Color]

theorem vector_eq_of_monochromatic_midpoint {b s : ℕ} (hb : 2 ≤ b)
    (x y z : Fin s → Fin b)
    (hxy : vectorColor x = vectorColor y)
    (hzy : vectorColor z = vectorColor y)
    (hm : ((finFunctionFinEquiv x).val : ℤ) -
      2 * (finFunctionFinEquiv y).val + (finFunctionFinEquiv z).val = 0) : x = y := by
  have hhxy : ∀ i, half b (x i).val = half b (y i).val :=
    fun i => congrFun (congrArg Prod.fst hxy) i
  have hhzy : ∀ i, half b (z i).val = half b (y i).val :=
    fun i => congrFun (congrArg Prod.fst hzy) i
  have hnx : normSq x = normSq y := congrArg (fun c : Color b s => c.2.val) hxy
  have hnz : normSq z = normSq y := congrArg (fun c : Color b s => c.2.val) hzy
  change (∑ i, (x i).val ^ 2) = ∑ i, (y i).val ^ 2 at hnx
  change (∑ i, (z i).val ^ 2) = ∑ i, (y i).val ^ 2 at hnz
  have hsum : (∑ i, ((x i).val : ℤ) ^ 2) = ∑ i, ((y i).val : ℤ) ^ 2 := by
    exact_mod_cast hnx
  have hsumz : (∑ i, ((z i).val : ℤ) ^ 2) = ∑ i, ((y i).val : ℤ) ^ 2 := by
    exact_mod_cast hnz
  have hcoeff : ∀ i, ((x i).val : ℤ) - 2 * (y i).val + (z i).val = 0 := by
    apply coefficients_zero hb
      (fun i => ((x i).val : ℤ) - 2 * (y i).val + (z i).val)
    · intro i
      exact half_coefficient_bound hb (x i).isLt (y i).isLt (z i).isLt
        (hhxy i) (hhzy i)
    · simp only [finFunctionFinEquiv_apply, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] at hm
      simpa only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        mul_assoc, ← Finset.mul_sum] using hm
  have heq := equal_of_midpoint_equal_norm
    (fun i => ((x i).val : ℤ)) (fun i => ((y i).val : ℤ))
    (fun i => ((z i).val : ℤ)) hcoeff hsum hsumz
  funext i
  apply Fin.ext
  exact_mod_cast congrFun heq i

def digits (b s : ℕ) (hb : 0 < b) (n : ℕ) : Fin s → Fin b :=
  finFunctionFinEquiv.symm ⟨n % b ^ s, Nat.mod_lt _ (pow_pos hb s)⟩

theorem digits_value {b s : ℕ} (hb : 0 < b) {n : ℕ} (hn : n < b ^ s) :
    (finFunctionFinEquiv (digits b s hb n)).val = n := by
  simp [digits, Nat.mod_eq_of_lt hn]

def coloring (b s : ℕ) (hb : 0 < b) : ℕ → Color b s :=
  fun n => vectorColor (digits b s hb n)

theorem coloring_avoids_three {b s : ℕ} (hb : 2 ≤ b) :
    ¬ HasMonoAP (coloring b s (by omega)) 3 (b ^ s) := by
  rintro ⟨a, d, hd, hbound, hm⟩
  have hbpos : 0 < b := by omega
  have ha : a < b ^ s := apStart_lt hbound
  have ha1 : a + d < b ^ s := by simpa using apTerm_lt hbound (by decide : 1 < 3)
  have ha2 : a + 2 * d < b ^ s := by simpa using apTerm_lt hbound (by decide : 2 < 3)
  have hc1 : coloring b s hbpos (a + d) = coloring b s hbpos a := by
    simpa using hm 1 (by decide)
  have hc2 : coloring b s hbpos (a + 2 * d) = coloring b s hbpos a := by
    simpa using hm 2 (by decide)
  have hvec := vector_eq_of_monochromatic_midpoint hb
    (digits b s hbpos a) (digits b s hbpos (a + d))
    (digits b s hbpos (a + 2 * d)) hc1.symm (hc2.trans hc1.symm) (by
      rw [digits_value hbpos ha, digits_value hbpos ha1, digits_value hbpos ha2]
      push_cast
      ring)
  have heq := congrArg (fun v : Fin s → Fin b => (finFunctionFinEquiv v).val) hvec
  rw [digits_value hbpos ha, digits_value hbpos ha1] at heq
  omega

theorem coloring_avoids {b s k : ℕ} (hb : 2 ≤ b) (hk : 3 ≤ k) :
    ¬ HasMonoAP (coloring b s (by omega)) k (b ^ s) :=
  fun h => coloring_avoids_three hb (h.mono_length hk)

/-- The exact ambient cardinality suffices to recolor into `Fin r`. -/
theorem exists_avoiding {b s k r : ℕ} (hb : 2 ≤ b) (hk : 3 ≤ k)
    (hcolors : 2 ^ s * (s * (b - 1) ^ 2 + 1) ≤ r) :
    ∃ c : ℕ → Fin r, ¬ HasMonoAP c k (b ^ s) := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Color b s) (β := Fin r) (by simpa [card_color] using hcolors)
  exact ⟨e ∘ coloring b s (by omega),
    not_hasMonoAP_of_recolor_injective e.injective (coloring_avoids hb hk)⟩

theorem pow_lt_W {b s k r : ℕ} (hb : 2 ≤ b) (hk : 3 ≤ k)
    (hcolors : 2 ^ s * (s * (b - 1) ^ 2 + 1) ≤ r)
    (hfinite : ∃ M, 0 < M ∧ IsRamsey (Fin r) k M) : b ^ s < W r k := by
  obtain ⟨c, hc⟩ := exists_avoiding hb hk hcolors
  exact lt_W_of_avoiding hfinite c hc

end LargeColor
end QuantitativeVanDerWaerden

end OAI
