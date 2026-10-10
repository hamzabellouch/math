import Mathlib
import OAI.Computability.MaxCut.Model

namespace OAI

namespace MaxCutGames.Fourier.Parity

def finiteSum {ι : Type} (indices : List ι) (f : ι → Rat) : Rat :=
  match indices with
  | [] => 0
  | i :: rest => f i + finiteSum rest f

theorem finiteSum_le {ι : Type} (indices : List ι) (f : ι → Rat) (bound : Rat)
    (h : ∀ i ∈ indices, f i ≤ bound) :
    finiteSum indices f ≤ (indices.length : Rat) * bound := by
  induction indices with
  | nil => simp [finiteSum]
  | cons i rest ih =>
    have hi := h i (by simp)
    have hr := ih (by intro j hj; exact h j (by simp [hj]))
    simp only [finiteSum, List.length_cons, Rat.natCast_add, Rat.natCast_ofNat]
    grind

theorem finiteSum_split {ι : Type} (indices : List ι) (f : ι → Rat)
    (zeroParity : ι → Bool) :
    finiteSum indices f =
      finiteSum indices (fun i => if zeroParity i then f i else 0) +
      finiteSum indices (fun i => if zeroParity i then 0 else f i) := by
  induction indices with
  | nil => simp [finiteSum]
  | cons i rest ih =>
    simp only [finiteSum]
    cases zeroParity i <;> simp_all <;> grind

theorem nonzero_sum_gt_half {ι : Type} (indices : List ι) (f : ι → Rat)
    (zeroParity : ι → Bool) (ρ : Rat)
    (dense : ρ < finiteSum indices f)
    (zero_bound : finiteSum indices (fun i => if zeroParity i then f i else 0) ≤ ρ / 2) :
    ρ / 2 < finiteSum indices (fun i => if zeroParity i then 0 else f i) := by
  have := finiteSum_split indices f zeroParity
  grind

theorem signed_le_abs (coefficient character : Rat)
    (sign : character = 1 ∨ character = -1) :
    coefficient * character ≤ coefficient.abs := by
  simp only [Rat.abs]
  rcases sign with h | h <;> rw [h] <;> split <;> grind

/-- A finite signed sum with large total and small parity-zero subtotal has a
large coefficient at an index of nonzero parity. `indices` may overcount:
only its length bound is used, so duplicate freedom is unnecessary here. -/
theorem coefficient_of_bounds {ι : Type} (indices : List ι)
    (coefficient character : ι → Rat) (zeroParity : ι → Bool)
    (ρ bound : Rat) (N : Nat)
    (bound_nonneg : 0 ≤ bound)
    (length_bound : indices.length ≤ N)
    (budget : (N : Rat) * bound ≤ ρ / 2)
    (sign : ∀ i ∈ indices, character i = 1 ∨ character i = -1)
    (dense : ρ < finiteSum indices (fun i => coefficient i * character i))
    (zero_bound : finiteSum indices (fun i =>
      if zeroParity i then coefficient i * character i else 0) ≤ ρ / 2) :
    ∃ i ∈ indices, zeroParity i = false ∧ bound < (coefficient i).abs := by
  classical
  by_cases exists_large : ∃ i ∈ indices,
      zeroParity i = false ∧ bound < (coefficient i).abs
  · exact exists_large
  · have hsmall : ∀ i ∈ indices,
        (if zeroParity i then 0 else coefficient i * character i) ≤ bound := by
      intro i hi
      cases hp : zeroParity i with
      | true => simpa [hp] using bound_nonneg
      | false =>
        have habs : (coefficient i).abs ≤ bound := by
          apply Rat.not_lt.mp
          intro hlarge
          exact exists_large ⟨i, hi, hp, hlarge⟩
        simpa [hp] using Rat.le_trans (signed_le_abs _ _ (sign i hi)) habs
    have hsum := finiteSum_le indices
      (fun i => if zeroParity i then 0 else coefficient i * character i) bound hsmall
    have hlength : (indices.length : Rat) ≤ (N : Rat) :=
      Rat.natCast_le_natCast.mpr length_bound
    have hmul := Rat.mul_le_mul_of_nonneg_right hlength bound_nonneg
    have hlarge := nonzero_sum_gt_half indices
      (fun i => coefficient i * character i) zeroParity ρ dense zero_bound
    exact False.elim (by grind)

/-- The exact threshold in Lemma 5.3 before substituting `N = 2^(r*s)`.
The displayed nested fraction is `(ρ / 2) / N`, hence `ρ / (2*N)`. -/
theorem coefficient_gt_half_div {ι : Type} (indices : List ι)
    (coefficient character : ι → Rat) (zeroParity : ι → Bool)
    (ρ : Rat) (N : Nat)
    (ρ_pos : 0 < ρ) (N_pos : 0 < N)
    (length_bound : indices.length ≤ N)
    (sign : ∀ i ∈ indices, character i = 1 ∨ character i = -1)
    (dense : ρ < finiteSum indices (fun i => coefficient i * character i))
    (zero_bound : finiteSum indices (fun i =>
      if zeroParity i then coefficient i * character i else 0) ≤ ρ / 2) :
    ∃ i ∈ indices, zeroParity i = false ∧
      (ρ / 2) / (N : Rat) < (coefficient i).abs := by
  have hN : (0 : Rat) < (N : Rat) := Rat.natCast_pos.mpr N_pos
  have threshold_pos : (0 : Rat) < (ρ / 2) / (N : Rat) := by
    apply (Rat.lt_div_iff hN).mpr
    grind
  have budget : (N : Rat) * ((ρ / 2) / (N : Rat)) = ρ / 2 := by
    rw [Rat.mul_comm, Rat.div_mul_cancel (Rat.ne_of_gt hN)]
  exact coefficient_of_bounds indices coefficient character zeroParity ρ
    ((ρ / 2) / (N : Rat)) N (Rat.le_of_lt threshold_pos) length_bound
    (by rw [budget]) sign dense zero_bound

theorem div_div_eq (a b c : Rat) : (a / b) / c = a / (b * c) := by
  simp only [Rat.div_def, Rat.inv_mul_rev]
  grind

theorem lemma53_arithmetic {ι : Type} (indices : List ι)
    (coefficient character : ι → Rat) (zeroParity : ι → Bool)
    (ρ : Rat) (r s : Nat)
    (ρ_pos : 0 < ρ)
    (length_bound : indices.length ≤ 2 ^ (r * s))
    (sign : ∀ i ∈ indices, character i = 1 ∨ character i = -1)
    (dense : ρ < finiteSum indices (fun i => coefficient i * character i))
    (zero_bound : finiteSum indices (fun i =>
      if zeroParity i then coefficient i * character i else 0) ≤ ρ / 2) :
    ∃ i ∈ indices, zeroParity i = false ∧
      ρ / (2 * ((2 ^ (r * s) : Nat) : Rat)) < (coefficient i).abs := by
  simpa only [div_div_eq] using
    coefficient_gt_half_div indices coefficient character zeroParity ρ
      (2 ^ (r * s)) ρ_pos (Nat.two_pow_pos _) length_bound sign dense zero_bound

end MaxCutGames.Fourier.Parity

end OAI
