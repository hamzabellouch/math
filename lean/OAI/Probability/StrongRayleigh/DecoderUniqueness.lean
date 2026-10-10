import Mathlib

namespace OAI

universe u_1 u_2

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace Problem336AdditiveD139.Decoder

def envelope (M L : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  M * L ^ n * t ^ n / (n.factorial : ℝ)

theorem envelope_nonneg {M L t : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (ht : 0 ≤ t) (n : ℕ) : 0 ≤ envelope M L n t := by
  unfold envelope
  positivity

theorem continuous_envelope (M L : ℝ) (n : ℕ) : Continuous (envelope M L n) := by
  unfold envelope
  fun_prop

theorem integral_envelope (M L t : ℝ) (n : ℕ) :
    (∫ s in 0..t, L * envelope M L n s) = envelope M L (n + 1) t := by
  have hfun : (fun s => L * envelope M L n s) =
      (fun s => (L * M * L ^ n / (n.factorial : ℝ)) * s ^ n) := by
    funext s
    unfold envelope
    ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
  simp only [envelope, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, zero_pow (Nat.succ_ne_zero n), sub_zero, pow_succ]
  field_simp

theorem envelope_tendsto_zero (M L t : ℝ) :
    Tendsto (fun n => envelope M L n t) atTop (𝓝 0) := by
  have h := (FloorSemiring.tendsto_pow_div_factorial_atTop (L * t)).const_mul M
  simpa only [envelope, mul_pow, mul_div_assoc, mul_assoc, mul_zero] using h

theorem uniform_volterra_unique {I : Type u_1} (u : I → ℝ → ℝ)
    (M L T : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hbound : ∀ i t, t ∈ Icc 0 T → |u i t| ≤ M)
    (hresponse : ∀ a : ℝ → ℝ, Continuous a →
      (∀ t ∈ Icc 0 T, 0 ≤ a t) →
      (∀ i t, t ∈ Icc 0 T → |u i t| ≤ a t) →
      ∀ i t, t ∈ Icc 0 T → |u i t| ≤ ∫ s in 0..t, L * a s) :
    ∀ i t, t ∈ Icc 0 T → u i t = 0 := by
  have hn : ∀ n i t, t ∈ Icc 0 T → |u i t| ≤ envelope M L n t := by
    intro n
    induction n with
    | zero => simpa [envelope] using hbound
    | succ n ih =>
      intro i t ht
      have h := hresponse (envelope M L n) (continuous_envelope M L n)
        (fun s hs => envelope_nonneg hM hL hs.1 n) ih i t ht
      simpa only [integral_envelope] using h
  intro i t ht
  have hle : |u i t| ≤ 0 :=
    ge_of_tendsto (envelope_tendsto_zero M L t) (Eventually.of_forall fun n => hn n i t ht)
  exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))

theorem bounded_drift_decoder_unique {I : Type u_2}
    (b : ℝ → (I → ℝ) → I → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ t, 0 ≤ t → ∀ x i, 0 ≤ b t x i ∧ b t x i ≤ 1)
    (hlip : ∀ t, 0 ≤ t → ∀ x y D, 0 ≤ D →
      (∀ i, |x i - y i| ≤ D) → ∀ i, |b t x i - b t y i| ≤ L * D)
    (w z z' : I → ℝ → ℝ)
    (hzint : ∀ i t, 0 ≤ t →
      IntervalIntegrable (fun s => b s (fun j => z j s) i) volume 0 t)
    (hz'int : ∀ i t, 0 ≤ t →
      IntervalIntegrable (fun s => b s (fun j => z' j s) i) volume 0 t)
    (hz : ∀ i t, 0 ≤ t →
      z i t = w i t + ∫ s in 0..t, b s (fun j => z j s) i)
    (hz' : ∀ i t, 0 ≤ t →
      z' i t = w i t + ∫ s in 0..t, b s (fun j => z' j s) i) :
    ∀ i t, 0 ≤ t → z i t = z' i t := by
  let u : I → ℝ → ℝ := fun i t => z i t - z' i t
  have hdiff : ∀ i t, 0 ≤ t → u i t =
      ∫ s in 0..t, b s (fun j => z j s) i - b s (fun j => z' j s) i := by
    intro i t ht
    rw [intervalIntegral.integral_sub (hzint i t ht) (hz'int i t ht)]
    dsimp [u]
    rw [hz i t ht, hz' i t ht]
    ring
  intro i T hT
  have hbound : ∀ j t, t ∈ Icc 0 T → |u j t| ≤ T := by
    intro j t ht
    rw [hdiff j t ht.1]
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := t) (C := (1 : ℝ))
      (f := fun s => b s (fun k => z k s) j - b s (fun k => z' k s) j) (by
        intro s hs
        rw [uIoc_of_le ht.1] at hs
        rw [Real.norm_eq_abs]
        have h₁ := hb s hs.1.le (fun k => z k s) j
        have h₂ := hb s hs.1.le (fun k => z' k s) j
        apply abs_le.mpr
        constructor <;> linarith)
    have hn' : |∫ s in 0..t,
        b s (fun k => z k s) j - b s (fun k => z' k s) j| ≤ t := by
      simpa only [Real.norm_eq_abs, sub_zero, one_mul, abs_of_nonneg ht.1] using hn
    exact hn'.trans ht.2
  have hresponse : ∀ a : ℝ → ℝ, Continuous a →
      (∀ t ∈ Icc 0 T, 0 ≤ a t) →
      (∀ j t, t ∈ Icc 0 T → |u j t| ≤ a t) →
      ∀ j t, t ∈ Icc 0 T → |u j t| ≤ ∫ s in 0..t, L * a s := by
    intro a ha hnon hmajor j t ht
    rw [hdiff j t ht.1, ← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le ht.1
      (Eventually.of_forall ?_) ((continuous_const.mul ha).intervalIntegrable 0 t)
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.trans ht.2⟩
    rw [Real.norm_eq_abs]
    exact hlip s hs.1.le (fun k => z k s) (fun k => z' k s) (a s)
      (hnon s hsT) (fun k => hmajor k s hsT) j
  have hzero := uniform_volterra_unique u T L T hT hL hbound hresponse i T ⟨hT, le_rfl⟩
  exact sub_eq_zero.mp hzero

end Problem336AdditiveD139.Decoder

end

end OAI
