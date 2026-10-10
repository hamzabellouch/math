import Mathlib

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open scoped BigOperators
open Filter Set
namespace PlanarEndpoint.TransverseInformation

lemma bad_conditioning_mass_le {Y : Type*} [Fintype Y]
    (p q : Y → ℝ) (hp : ∀ y, 0 ≤ p y) (_hq : ∀ y, 0 ≤ q y)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (∑ y, if q y < ε * p y then q y else 0) ≤ ε * ∑ y, p y := by
  classical
  calc
    _ ≤ ∑ y, ε * p y := Finset.sum_le_sum (fun y _ => by
      split_ifs with h
      · exact h.le
      · exact mul_nonneg hε (hp y))
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma bad_conditioning_probability_le {Y : Type*} [Fintype Y]
    (p q : Y → ℝ) (hp : ∀ y, 0 ≤ p y) (hq : ∀ y, 0 ≤ q y)
    (hp1 : ∑ y, p y = 1) {ε : ℝ} (hε : 0 ≤ ε) :
    (∑ y, if q y < ε * p y then q y else 0) ≤ ε := by
  simpa only [hp1,mul_one] using bad_conditioning_mass_le p q hp hq hε

lemma mixture_bad_conditioning_probability_le {Y V : Type*} [Fintype Y] [Fintype V]
    (w : V → ℝ) (p q : V → Y → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hw1 : ∑ v, w v = 1)
    (hp : ∀ v y, 0 ≤ p v y) (hq : ∀ v y, 0 ≤ q v y)
    (hp1 : ∀ v, ∑ y, p v y = 1) {ε : ℝ} (hε : 0 ≤ ε) :
    (∑ v, w v * ∑ y, if q v y < ε * p v y then q v y else 0) ≤ ε := by
  classical
  calc
    _ ≤ ∑ v, w v * ε := Finset.sum_le_sum (fun v _ =>
      mul_le_mul_of_nonneg_left
        (bad_conditioning_probability_le (p v) (q v) (hp v) (hq v) (hp1 v) hε) (hw v))
    _ = ε := by rw [← Finset.sum_mul,hw1,one_mul]

lemma low_probability_mass_le {Y : Type*} (S : Finset Y) (p : Y → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (∑ y ∈ S, if p y < δ then p y else 0) ≤ S.card * δ := by
  classical
  calc
    _ ≤ ∑ _y ∈ S, δ := Finset.sum_le_sum (fun y _ => by
      split_ifs with h
      · exact h.le
      · exact hδ)
    _ = _ := by simp

lemma restricted_low_probability_mass_le {Y : Type*} (S : Finset Y)
    (p e : Y → ℝ) (_hp : ∀ y, 0 ≤ p y)
    (he : ∀ y, 0 ≤ e y ∧ e y ≤ p y) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∑ y ∈ S, if p y < δ then e y else 0) ≤ S.card * δ := by
  classical
  apply le_trans _ (low_probability_mass_le S p hδ)
  exact Finset.sum_le_sum (fun y _ => by
    split_ifs <;> simp_all only [le_refl])

def information (L p : ℝ) : ℝ := -Real.log p / Real.log L

lemma information_difference_eq (L p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    information L p - information L q = Real.log (q/p) / Real.log L := by
  rw [Real.log_div hq.ne' hp.ne']
  unfold information
  ring

lemma information_bad_iff {L p q η : ℝ} (hL : 1 < L) (hp : 0 < p) (hq : 0 < q) :
    information L p - information L q < -η ↔ q < L ^ (-η) * p := by
  rw [information_difference_eq L p q hp hq]
  rw [div_lt_iff₀ (Real.log_pos hL)]
  rw [← Real.log_rpow (by linarith : 0 < L) (-η)]
  rw [Real.log_lt_log_iff (div_pos hq hp) (Real.rpow_pos_of_pos (by linarith) _)]
  exact div_lt_iff₀ hp

lemma conditioning_information_exception_le {Y : Type*} [Fintype Y]
    (p q : Y → ℝ) (hp : ∀ y, 0 < p y) (hq : ∀ y, 0 < q y)
    (hp1 : ∑ y, p y = 1) {L η : ℝ} (hL : 1 < L) :
    (∑ y, if information L (p y) - information L (q y) < -η then q y else 0)
      ≤ L ^ (-η) := by
  classical
  simp_rw [information_bad_iff hL (hp _) (hq _)]
  exact bad_conditioning_probability_le p q (fun y => (hp y).le)
    (fun y => (hq y).le) hp1 (Real.rpow_nonneg (by linarith) _)

end PlanarEndpoint.TransverseInformation
end

end OAI
