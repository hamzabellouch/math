import OAI.Analysis.PeriodicLattice.Machines

namespace OAI

/-! Smooth machine signals and planar residual fields. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingSignals {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace Signal

open Scales

def inSlot (b L n : ℕ) (halt : Bool) (s : ℝ) : ℝ :=
  1 / 2 - beta b L n +
    s * (beta b L n - beta b L (n + 1) + if halt then 2 * beta b L (n + 1) else 0)

theorem start (b L n : ℕ) (h : Bool) :
    inSlot b L n h 0 = 1 / 2 - beta b L n := by simp [inSlot]

theorem nonhalting_end (b L n : ℕ) :
    inSlot b L n false 1 = 1 / 2 - beta b L (n + 1) := by
  simp only [inSlot, Bool.false_eq_true, ↓reduceIte, add_zero, one_mul]
  ring

theorem halting_end (b L n : ℕ) :
    inSlot b L n true 1 = 1 / 2 + beta b L (n + 1) := by
  simp only [inSlot, ↓reduceIte, one_mul]
  ring

theorem nonhalting_interval {b : ℕ} (hb : 2 ≤ b) (L n : ℕ) {s : ℝ}
    (hs : 0 ≤ s) (hs' : s ≤ 1) :
    1 / 2 - beta b L n ≤ inSlot b L n false s ∧
    inSlot b L n false s ≤ 1 / 2 - beta b L (n + 1) ∧
    1 / 4 ≤ inSlot b L n false s ∧ inSlot b L n false s < 1 / 2 := by
  have hdec := beta_strictAnti hb L (Nat.lt_succ_self n)
  have hδ : 0 ≤ beta b L n - beta b L (n + 1) := by linarith
  have hmlo := mul_nonneg hs hδ
  have hmhi := mul_le_mul_of_nonneg_right hs' hδ
  have hβ := beta_pos hb L (n + 1)
  have hβ' := beta_le_quarter hb L n
  simp only [inSlot, Bool.false_eq_true, ↓reduceIte, add_zero, one_mul] at *
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem halting_interval {b : ℕ} (hb : 2 ≤ b) (L n : ℕ) :
    1 / 2 < inSlot b L n true 1 ∧ inSlot b L n true 1 < 1 := by
  rw [halting_end]
  have hp := beta_pos hb L (n + 1)
  have hq := beta_le_quarter hb L (n + 1)
  constructor <;> linarith

theorem displacement_in_plateau {b : ℕ} (hb : 2 ≤ b) (L n : ℕ)
    {c : ℕ} (hc : c < capacity b L (n + 1)) {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) :
    0 ≤ s * epsilon b L (n + 1) * c ∧
    s * epsilon b L (n + 1) * c < epsilon b L n / 4 := by
  have he := epsilon_pos hb L (n + 1)
  have hc' : (c : ℝ) ≤ (capacity b L (n + 1) : ℝ) := by exact_mod_cast hc.le
  have hle : s * epsilon b L (n + 1) * c ≤
      (capacity b L (n + 1) : ℝ) * epsilon b L (n + 1) := by
    calc
      s * epsilon b L (n + 1) * c ≤ 1 * epsilon b L (n + 1) * c :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs' he.le) (by positivity)
      _ ≤ (capacity b L (n + 1) : ℝ) * epsilon b L (n + 1) := by
        simpa only [one_mul, mul_comm] using mul_le_mul_of_nonneg_right hc' he.le
  obtain ⟨ha, hb', hc'⟩ := plateau_bound hb L n
  exact ⟨mul_nonneg (mul_nonneg hs he.le) (by positivity), hle.trans_lt (ha.trans hb' |>.trans_lt hc')⟩

theorem history_in_plateau {b : ℕ} (hb : 2 ≤ b) (L n : ℕ) (c : ℕ → ℕ)
    (hc : c (n + 1) < capacity b L (n + 1)) {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) :
    |(History.coordinate b L c n + s * epsilon b L (n + 1) * c (n + 1) - 1 / 2) /
        epsilon b L n - (History.address b L c n : ℝ)| < 1 / 4 := by
  have he := epsilon_pos hb L n
  obtain ⟨hlo, hhi⟩ := displacement_in_plateau hb L n hc hs hs'
  rw [show History.coordinate b L c n +
      s * epsilon b L (n + 1) * (c (n + 1) : ℝ) - 1 / 2 =
      (History.coordinate b L c n - 1 / 2) +
        s * epsilon b L (n + 1) * (c (n + 1) : ℝ) by ring,
    add_div, History.read_coordinate hb, add_sub_cancel_left,
    abs_of_nonneg (div_nonneg hlo he.le)]
  apply (div_lt_iff₀ he).2
  linarith

end Signal

namespace Residual

def force (ν : ℝ) (u : VectorField) : VectorField :=
  fun t q => timeD u t q + advection u t q - ν • laplacian u t q

@[simp] theorem spaceD_zero (i : Fin 3) : spaceD i (0 : ScalarField) = 0 := by
  funext t q
  simp [spaceD]

@[simp] theorem gradient_zero : gradient (0 : ScalarField) = 0 := by
  funext t q
  ext i
  simp [gradient, spaceD_zero]

theorem spaceD_neg (i : Fin 3) (p : ScalarField) : spaceD i (-p) = -spaceD i p := by
  funext t q
  exact deriv.neg

@[simp] theorem gradient_neg (p : ScalarField) : gradient (-p) = -gradient p := by
  funext t q
  ext i
  change spaceD i (-p) t q = -spaceD i p t q
  exact congrFun (congrFun (spaceD_neg i p) t) q

theorem divergence_gradient (p : ScalarField) : divergence (gradient p) = laplacian p := by
  rfl

theorem equations (ν : ℝ) (u : VectorField) (hdiv : Solenoidal u)
    (hinit : ∀ q, u 0 q = 0) : NavierStokes ν (force ν u) u 0 := by
  refine ⟨?_, hdiv, hinit⟩
  intro t ht q
  rw [gradient_zero]
  simp only [Pi.zero_apply, neg_zero, zero_add, force]
  abel

theorem projection_equations (ν : ℝ) (g u : VectorField) (φ : ScalarField)
    (h : NavierStokes ν g u 0) :
    NavierStokes ν (fun t q => g t q - gradient φ t q) u (-φ) := by
  refine ⟨?_, h.2⟩
  intro t ht q
  have heq := h.1 t ht q
  rw [gradient_zero] at heq
  rw [gradient_neg]
  simp only [Pi.zero_apply, neg_zero, zero_add] at heq
  simp only [Pi.neg_apply, neg_neg]
  rw [heq]
  abel

end Residual

namespace Scales

def crudeSlotBound (b L k n : ℕ) : ℕ :=
  1 + capacity b L (n + 1) * b ^ (exponent L n * k)

theorem slotSize_le_crude {b : ℕ} (hb : 2 ≤ b) (L k n : ℕ) :
    slotSize b L k n ≤ (crudeSlotBound b L k n : ℝ) := by
  have hβ : (if k = 0 then beta b L n else (0 : ℝ)) ≤ 1 := by
    split_ifs
    · have := beta_le_quarter hb L n
      linarith
    · norm_num
  have he := epsilon_le_one hb L (n + 1)
  have hmul : 0 ≤ (capacity b L (n + 1) : ℝ) * (b : ℝ) ^ (exponent L n * k) := by
    positivity
  have hrec : (capacity b L (n + 1) : ℝ) * epsilon b L (n + 1) /
      epsilon b L n ^ k ≤
      (capacity b L (n + 1) : ℝ) * (b : ℝ) ^ (exponent L n * k) := by
    rw [show epsilon b L n = ((b : ℝ) ^ exponent L n)⁻¹ from rfl,
      inv_pow, div_inv_eq_mul, ← pow_mul]
    have h := mul_le_mul_of_nonneg_right he hmul
    nlinarith
  unfold slotSize crudeSlotBound
  push_cast
  linarith

def allSlotsBound (b L k J : ℕ) : ℕ :=
  2 * weightBound J + ∑ n ∈ Finset.range (max 1 k), (n + 3) ^ J * crudeSlotBound b L k n

theorem weighted_slotSize_bound_all {b : ℕ} (hb : 2 ≤ b) (L k J n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (hT : t ≤ (n : ℝ) + 2) :
    (1 + t) ^ J * slotSize b L k n ≤ (allSlotsBound b L k J : ℝ) := by
  by_cases hn : max 1 k ≤ n
  · have hsharp := weighted_slotSize_bound hb L J
      ((le_max_left 1 k).trans hn) ((le_max_right 1 k).trans hn) ht hT
    apply hsharp.trans
    have hnat : 2 * weightBound J ≤ allSlotsBound b L k J := by
      unfold allSlotsBound
      omega
    exact_mod_cast hnat
  · have hmem : n ∈ Finset.range (max 1 k) := Finset.mem_range.mpr (by omega)
    have hsingle : (n + 3) ^ J * crudeSlotBound b L k n ≤
        ∑ m ∈ Finset.range (max 1 k), (m + 3) ^ J * crudeSlotBound b L k m :=
      Finset.single_le_sum (f := fun m : ℕ => (m + 3) ^ J * crudeSlotBound b L k m)
        (by intro i hi; exact Nat.zero_le _) hmem
    have hnat : (n + 3) ^ J * crudeSlotBound b L k n ≤ allSlotsBound b L k J := by
      unfold allSlotsBound
      omega
    calc
      (1 + t) ^ J * slotSize b L k n ≤
          (1 + t) ^ J * (crudeSlotBound b L k n : ℝ) :=
        mul_le_mul_of_nonneg_left (slotSize_le_crude hb L k n) (by positivity)
      _ ≤ ((n : ℝ) + 3) ^ J * (crudeSlotBound b L k n : ℝ) :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by linarith) (by linarith) J) (by positivity)
      _ ≤ (allSlotsBound b L k J : ℝ) := by exact_mod_cast hnat

end Scales

end
end PeriodicLattice

end OAI
