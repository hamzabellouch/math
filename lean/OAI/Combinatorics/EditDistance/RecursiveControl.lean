import OAI.Combinatorics.EditDistance.Families
import OAI.Combinatorics.EditDistance.DirectSums
import OAI.Combinatorics.EditDistance.Slots

namespace OAI

/-!
# Averaged displacement control for recursive word families
-/

namespace EditFamily
open scoped BigOperators
open EditDistortion EditAverage EditFourier EditSlots

section InductiveControl
variable {J : Type} [Fintype J] [DecidableEq J] (i : J)

noncomputable def weight (j : J) : ℝ := (EditSlots.multiplicity i j : ℝ) / (2 * (2 * Fintype.card J - 1))

lemma weight_pos (j : J) : 0 < weight i j := by
  have hb : 0 < (Fintype.card J : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  have hb' : (1 : ℝ) ≤ Fintype.card J := by
    exact_mod_cast (show 1 ≤ Fintype.card J by exact Fintype.card_pos_iff.mpr ⟨i⟩)
  have hc : 0 < (EditSlots.multiplicity i j : ℝ) := by
    by_cases hj : j = i <;> simp [EditSlots.multiplicity, hj, hb]
  exact div_pos hc (by linarith)

lemma sum_weight : (∑ j : J, weight i j) = 1 / 2 := by
  have hb : (1 : ℝ) ≤ Fintype.card J := by
    exact_mod_cast (show 1 ≤ Fintype.card J by exact Fintype.card_pos_iff.mpr ⟨i⟩)
  simp only [weight, ← Finset.sum_div, sum_multiplicity]
  field_simp [show (2 * (Fintype.card J : ℝ) - 1) ≠ 0 by linarith]

variable {p : J → ℕ} {m A : ℕ} {α Q : ℝ}
variable (F : ∀ j, Family (p j) m A α Q)

abbrev ProductState := ∀ j, (F j).State

def lift (j : J) (e : (F j).State) : ProductState F := Pi.single j e

def allPhase : ProductState F := fun j => (F j).v

lemma sum_lift_vectors : (∑ j, lift F j (F j).v) = allPhase F := by
  ext j
  simp [lift, allPhase]

omit [Fintype J] in
lemma lift_nsmul (j : J) (u : ℕ) (e : (F j).State) :
    lift F j (u • e) = u • lift F j e := by
  ext k
  by_cases hk : k = j
  · subst k; simp [lift]
  · simp [lift, hk]

lemma variation_zero (H : ProductState F → L1) : variation H 0 = 0 := by
  simp [variation, avg]

lemma component_control (hQ : 0 ≤ Q) (H : ProductState F → L1)
    (hh : ∀ j e r, (e,r) ∈ (F j).steps →
      variation H (lift F j e) ≤ weight i j * r)
    (j : J) (a : ℕ) (ha : a < p j) :
    variation H (a • lift F j (F j).v) ≤ weight i j * Q := by
  by_cases ha0 : a = 0
  · simp only [ha0, zero_nsmul, variation_zero]
    exact mul_nonneg (weight_pos i j).le hQ
  let T := EditSlices.slice (fun j => (F j).State) H j (weight i j)
  have hT : ∀ e r, (e,r) ∈ (F j).steps → variation T e ≤ r := by
    intro e r her
    rw [EditSlices.variation_slice _ H j _ (weight_pos i j)]
    apply (div_le_iff₀ (weight_pos i j)).mpr
    simpa only [lift, mul_comm] using hh j e r her
  have hC := (F j).control T hT a (Nat.pos_of_ne_zero ha0) ha
  rw [EditSlices.variation_slice _ H j _ (weight_pos i j)] at hC
  have hC' := (div_le_iff₀ (weight_pos i j)).mp hC
  change variation H (lift F j (a • (F j).v)) ≤ Q * weight i j at hC'
  rw [lift_nsmul] at hC'
  simpa only [mul_comm] using hC'

theorem successor_control
    (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (P : ℝ) (hP : 1 ≤ 2 * P) (hpP : ∀ j, (p j : ℝ) ≤ 2 * P)
    (h : ℕ) (hh : 0 < h) (L : ℕ) (hQ : 0 ≤ Q)
    (H : ProductState F → L1) (hτ : variation H (allPhase F) ≤ 2 / L)
    (hlift : ∀ j e r, (e,r) ∈ (F j).steps →
      variation H (lift F j e) ≤ weight i j * r)
    (u : ℕ) (hu : u < p i) :
    variation H (u • lift F i (F i).v) ≤
      2 * (2 * P) ^ (2 * h) / L + Q / h := by
  let (j : J) : NeZero (p j) := ⟨(hp j).ne_zero⟩
  have hv (j : J) : p j • lift F j (F j).v = 0 := by
    rw [← lift_nsmul, (F j).annihilate]
    simp [lift]
  have hc := prime_vector_displacement p (fun j => lift F j (F j).v) hv hp hinj
    P hP hpP h hh H i (u : ZMod (p i))
  rw [ZMod.val_natCast_of_lt hu, sum_lift_vectors] at hc
  have hb (j : J) : avg (fun a : ZMod (p j) => variation H (a.val • lift F j (F j).v)) ≤
      weight i j * Q := by
    rw [← avg_const (X := ZMod (p j)) (weight i j * Q)]
    exact avg_mono (fun a => component_control i F hQ H hlift j a.val (ZMod.val_lt a))
  calc
    _ ≤ (2 * P) ^ (2 * h) * variation H (allPhase F) +
        (2 / (h : ℝ)) * ∑ j, avg (fun a : ZMod (p j) =>
          variation H (a.val • lift F j (F j).v)) := hc
    _ ≤ (2 * P) ^ (2 * h) * (2 / (L : ℝ)) +
        (2 / (h : ℝ)) * ∑ j, weight i j * Q := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hτ (pow_nonneg (by linarith) _)
      · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hb j)) (by positivity)
    _ = _ := by rw [← Finset.sum_mul, sum_weight]; ring

end InductiveControl
end EditFamily

end OAI
