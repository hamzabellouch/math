import Mathlib

namespace OAI

namespace IndependentSetsGames.Foundations.CorrelatedSampling

noncomputable section

variable {σ : Type*} [Fintype σ]

def eventMass (w : σ → ℝ) (event : σ → Bool) : ℝ :=
  ∑ s, if event s then w s else 0

theorem eventMass_nonneg (w : σ → ℝ) (event : σ → Bool) (hw : ∀ s, 0 ≤ w s) :
    0 ≤ eventMass w event := by
  apply Finset.sum_nonneg
  intro s _
  split <;> simp_all

theorem eventMass_complement (w : σ → ℝ) (event : σ → Bool)
    (hw : ∑ s, w s = 1) :
    eventMass w event + eventMass w (fun s => !(event s)) = 1 := by
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  calc
    ∑ s, ((if event s then w s else 0) + (if !event s then w s else 0)) = ∑ s, w s := by
      apply Finset.sum_congr rfl
      intro s _
      cases event s <;> simp
    _ = 1 := hw

def geometricMass (r : ℝ) : Nat → ℝ
  | 0 => 0
  | n + 1 => 1 + r * geometricMass r n

theorem geometricMass_nonneg (r : ℝ) (hr : 0 ≤ r) (n : Nat) :
    0 ≤ geometricMass r n := by
  induction n with
  | zero => simp [geometricMass]
  | succ n ih => exact add_nonneg (by norm_num) (mul_nonneg hr ih)

theorem geometricMass_identity (r : ℝ) (n : Nat) :
    (1 - r) * geometricMass r n = 1 - r ^ n := by
  induction n with
  | zero => simp [geometricMass]
  | succ n ih =>
      simp only [geometricMass, pow_succ]
      calc
        (1 - r) * (1 + r * geometricMass r n) =
            (1 - r) + r * ((1 - r) * geometricMass r n) := by ring
        _ = 1 - r ^ n * r := by rw [ih]; ring

def firstHitWeight (w : σ → ℝ) (accept : σ → Bool) : Nat → Option σ → ℝ
  | 0, none => 1
  | 0, some _ => 0
  | n + 1, none => eventMass w (fun s => !(accept s)) * firstHitWeight w accept n none
  | n + 1, some s =>
      (if accept s then w s else 0) +
        eventMass w (fun s => !(accept s)) * firstHitWeight w accept n (some s)

theorem firstHitWeight_nonneg (w : σ → ℝ) (accept : σ → Bool)
    (hw : ∀ s, 0 ≤ w s) (n : Nat) (output : Option σ) :
    0 ≤ firstHitWeight w accept n output := by
  induction n generalizing output with
  | zero => cases output <;> simp [firstHitWeight]
  | succ n ih =>
      have hr := eventMass_nonneg w (fun s => !(accept s)) hw
      cases output with
      | none => exact mul_nonneg hr (ih none)
      | some s =>
          apply add_nonneg
          · split <;> simp_all
          · exact mul_nonneg hr (ih (some s))

theorem firstHitWeight_none (w : σ → ℝ) (accept : σ → Bool) (n : Nat) :
    firstHitWeight w accept n none = eventMass w (fun s => !(accept s)) ^ n := by
  induction n with
  | zero => simp [firstHitWeight]
  | succ n ih => simp [firstHitWeight, ih, pow_succ, mul_comm]

theorem firstHitWeight_some (w : σ → ℝ) (accept : σ → Bool) (n : Nat) (s : σ) :
    firstHitWeight w accept n (some s) =
      (if accept s then w s else 0) *
        geometricMass (eventMass w (fun s => !(accept s))) n := by
  induction n with
  | zero => simp [firstHitWeight, geometricMass]
  | succ n ih =>
      rw [firstHitWeight, geometricMass, ih]
      ring

theorem firstHitWeight_normalized (w : σ → ℝ) (accept : σ → Bool)
    (hw : ∑ s, w s = 1) (n : Nat) : ∑ output, firstHitWeight w accept n output = 1 := by
  rw [Fintype.sum_option, firstHitWeight_none]
  simp_rw [firstHitWeight_some]
  rw [← Finset.sum_mul]
  change eventMass w (fun s => !(accept s)) ^ n +
    eventMass w accept * geometricMass (eventMass w (fun s => !(accept s))) n = 1
  have hc := eventMass_complement w accept hw
  have hg := geometricMass_identity (eventMass w (fun s => !(accept s))) n
  have ha : eventMass w accept = 1 - eventMass w (fun s => !(accept s)) := by linarith
  rw [ha, hg]
  ring

def goodFirstMass (w : σ → ℝ) (accept good : σ → Bool) (n : Nat) : ℝ :=
  ∑ s, if good s then firstHitWeight w accept n (some s) else 0

theorem goodFirstMass_eq (w : σ → ℝ) (accept good : σ → Bool) (n : Nat) :
    goodFirstMass w accept good n =
      eventMass w (fun s => accept s && good s) *
        geometricMass (eventMass w (fun s => !(accept s))) n := by
  unfold goodFirstMass eventMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [firstHitWeight_some]
  cases ha : accept s <;> cases hg : good s <;> simp [ha, hg, eventMass]

theorem goodFirstMass_exact (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∑ s, w s = 1) (ha : eventMass w accept ≠ 0) (n : Nat) :
    goodFirstMass w accept good n =
      eventMass w (fun s => accept s && good s) / eventMass w accept *
        (1 - eventMass w (fun s => !(accept s)) ^ n) := by
  rw [goodFirstMass_eq]
  have hc := eventMass_complement w accept hw
  have hg := geometricMass_identity (eventMass w (fun s => !(accept s))) n
  have hgeom : eventMass w accept *
      geometricMass (eventMass w (fun s => !(accept s))) n =
      1 - eventMass w (fun s => !(accept s)) ^ n := by
    have heq : eventMass w accept = 1 - eventMass w (fun s => !(accept s)) := by linarith
    rw [heq, hg]
  rw [← hgeom]
  field_simp

theorem commonMass_le_acceptMass (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∀ s, 0 ≤ w s) :
    eventMass w (fun s => accept s && good s) ≤ eventMass w accept := by
  apply Finset.sum_le_sum
  intro s _
  cases ha : accept s <;> cases hg : good s <;> simp [ha, hg, hw s]

theorem goodFirstMass_lower_bound (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∀ s, 0 ≤ w s) (hw_sum : ∑ s, w s = 1)
    (ha : 0 < eventMass w accept) (n : Nat) :
    eventMass w (fun s => accept s && good s) / eventMass w accept -
        eventMass w (fun s => !(accept s)) ^ n ≤ goodFirstMass w accept good n := by
  rw [goodFirstMass_exact w accept good hw_sum (ne_of_gt ha) n]
  have hratio : eventMass w (fun s => accept s && good s) / eventMass w accept ≤ 1 := by
    apply (div_le_one ha).2
    exact commonMass_le_acceptMass w accept good hw
  have htail : 0 ≤ eventMass w (fun s => !(accept s)) ^ n :=
    pow_nonneg (eventMass_nonneg w (fun s => !(accept s)) hw) n
  nlinarith

end

end IndependentSetsGames.Foundations.CorrelatedSampling

end OAI
