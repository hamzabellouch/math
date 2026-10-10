import OAI.Analysis.PeriodicLattice.Profiles

namespace OAI

/-! Planar velocity fields implementing the encoded dynamics. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingPlanar {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace Planar

open Profiles Scales
open scoped ContDiff

abbrev Point := ℝ × ℝ

def slot (b L n : ℕ) (F H : ℤ → ℝ) (y : ℝ) : Point :=
  letI := twoAtLeastTwo
  (beta b L n - beta b L (n + 1) +
      2 * beta b L (n + 1) * selector (epsilon b L n) H y,
    epsilon b L (n + 1) * selector (epsilon b L n) F y)

def coefficients (b L c₀ : ℕ) (F H : ℕ → ℤ → ℝ) : ℕ → ℝ → Point :=
  fun n => Nat.casesOn n (fun _ => (0, epsilon b L 0 * c₀))
    (fun k => slot b L k (F k) (H k))

def field (b L c₀ : ℕ) (F H : ℕ → ℤ → ℝ) (t : ℝ) (x : Point) : Point :=
  schedule (coefficients b L c₀ F H) t x.2

theorem slot_contDiff (b L n : ℕ) (F H : ℤ → ℝ) :
    ContDiff ℝ ∞ (slot b L n F H) :=
  (contDiff_const.add (contDiff_const.mul (selector_contDiff _ _))).prodMk
    (contDiff_const.mul (selector_contDiff _ _))

theorem field_contDiff (b L c₀ : ℕ) (F H : ℕ → ℤ → ℝ) :
    ContDiff ℝ ∞ (fun tx : ℝ × Point => field b L c₀ F H tx.1 tx.2) := by
  have hV : ∀ n, ContDiff ℝ ∞ (coefficients b L c₀ F H n) := by
    intro n
    cases n with
    | zero => exact contDiff_const
    | succ n => exact slot_contDiff b L n (F n) (H n)
  exact (schedule_contDiff _ hV).comp (contDiff_fst.prodMk (contDiff_snd.snd))

theorem field_at_start (b L c₀ : ℕ) (F H : ℕ → ℤ → ℝ) (x : Point) :
    field b L c₀ F H 0 x = 0 := schedule_zero_at_start _ _

theorem field_on_loader (b L c₀ : ℕ) (F H : ℕ → ℤ → ℝ) {t : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1) (x : Point) :
    field b L c₀ F H t x = deriv clock t • (0, epsilon b L 0 * c₀) := by
  simpa [field, coefficients, pulse] using
    schedule_on_slot (coefficients b L c₀ F H) 0 (by simpa using ht) (by simpa using ht') x.2

theorem field_on_slot (b L c₀ n : ℕ) (F H : ℕ → ℤ → ℝ) {t : ℝ}
    (ht : n + 1 ≤ t) (ht' : t ≤ n + 2) (x : Point) :
    field b L c₀ F H t x = deriv clock (t - 1 - n) • slot b L n (F n) (H n) x.2 := by
  have hl : ((n + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast ht
  have hu : t ≤ ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
  simpa only [field, coefficients, pulse, Nat.cast_add, Nat.cast_one,
    sub_add_eq_sub_sub, sub_right_comm] using
    schedule_on_slot (coefficients b L c₀ F H) (n + 1) hl hu x.2

theorem field_periodic_y {b : ℕ} (hb : 2 ≤ b) (L c₀ : ℕ) (F H : ℕ → ℤ → ℝ)
    (hF : ∀ n, Function.Periodic (F n) (capacity b L n : ℤ))
    (hH : ∀ n, Function.Periodic (H n) (capacity b L n : ℤ)) (t x : ℝ) :
    Function.Periodic (fun y => field b L c₀ F H t (x, y)) 1 := by
  intro y
  apply finsum_congr
  intro n
  congr 1
  cases n with
  | zero => rfl
  | succ n =>
    dsimp [coefficients, slot]
    rw [selector_unit_periodic hb L n (H n) (hH n) y,
      selector_unit_periodic hb L n (F n) (hF n) y]

def slotCurve (b L n : ℕ) (F H : ℤ → ℝ) (j : ℤ) (a : Point) (τ : ℝ) : Point :=
  a + clock τ • (beta b L n - beta b L (n + 1) + 2 * beta b L (n + 1) * H j,
    epsilon b L (n + 1) * F j)

theorem slotCurve_hasDerivAt {b : ℕ} (hb : 2 ≤ b) (L n : ℕ) (F H : ℤ → ℝ)
    (j : ℤ) (a : Point) (ha : (a.2 - 1 / 2) / epsilon b L n = (j : ℝ))
    (hF : 0 ≤ F j) (hF' : F j ≤ capacity b L (n + 1)) (τ : ℝ) :
    HasDerivAt (slotCurve b L n F H j a)
      (deriv clock τ • slot b L n F H (slotCurve b L n F H j a τ).2) τ := by
  have he := epsilon_pos hb L n
  have he' := epsilon_pos hb L (n + 1)
  have hplo := mul_nonneg (clock_nonneg τ) (mul_nonneg he'.le hF)
  have hphi : clock τ * (epsilon b L (n + 1) * F j) < epsilon b L n / 4 := by
    have hbound : clock τ * (epsilon b L (n + 1) * F j) ≤
        (capacity b L (n + 1) : ℝ) * epsilon b L (n + 1) := calc
      _ ≤ 1 * (epsilon b L (n + 1) * F j) :=
        mul_le_mul_of_nonneg_right (clock_le_one τ) (mul_nonneg he'.le hF)
      _ ≤ (capacity b L (n + 1) : ℝ) * epsilon b L (n + 1) := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hF' he'.le
    obtain ⟨h₁, h₂, h₃⟩ := plateau_bound hb L n
    exact hbound.trans_lt (h₁.trans h₂ |>.trans_lt h₃)
  have hplateau : |((slotCurve b L n F H j a τ).2 - 1 / 2) / epsilon b L n - j| ≤
      1 / 4 := by
    change |(a.2 + clock τ * (epsilon b L (n + 1) * F j) - 1 / 2) /
      epsilon b L n - j| ≤ 1 / 4
    rw [show a.2 + clock τ * (epsilon b L (n + 1) * F j) - 1 / 2 =
      (a.2 - 1 / 2) + clock τ * (epsilon b L (n + 1) * F j) by ring,
      add_div, ha, add_sub_cancel_left, abs_of_nonneg (div_nonneg hplo he.le)]
    exact (div_le_iff₀ he).mpr (by linarith)
  have hslot : slot b L n F H (slotCurve b L n F H j a τ).2 =
      (beta b L n - beta b L (n + 1) + 2 * beta b L (n + 1) * H j,
        epsilon b L (n + 1) * F j) := by
    dsimp [slot]
    rw [selector_plateau _ _ hplateau, selector_plateau _ _ hplateau]
  rw [hslot]
  exact (((contDiff_infty_iff_deriv.mp clock_contDiff).1 τ).hasDerivAt.smul_const _).const_add a

end Planar

end
end PeriodicLattice

end OAI
