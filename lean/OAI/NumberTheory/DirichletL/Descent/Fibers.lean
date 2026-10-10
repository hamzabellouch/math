import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators

noncomputable section

def weightedEnergy {ι : Type*} (s : Finset ι) (w : ι → ℝ) (f : ι → ℂ) : ℝ :=
  ∑ i ∈ s, w i * ‖f i‖ ^ 2

theorem weightedEnergy_nonneg {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (f : ι → ℂ) (hw : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ weightedEnergy s w f := by
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)

theorem weighted_cauchy {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (f g : ι → ℂ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ‖∑ i ∈ s, (w i : ℂ) * f i * star (g i)‖ ≤
      Real.sqrt (weightedEnergy s w f) * Real.sqrt (weightedEnergy s w g) := by
  have hf : ∑ i ∈ s, (Real.sqrt (w i) * ‖f i‖) ^ 2 = weightedEnergy s w f := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  have hg : ∑ i ∈ s, (Real.sqrt (w i) * ‖g i‖) ^ 2 = weightedEnergy s w g := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  calc
    ‖∑ i ∈ s, (w i : ℂ) * f i * star (g i)‖ ≤
        ∑ i ∈ s, ‖(w i : ℂ) * f i * star (g i)‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, (Real.sqrt (w i) * ‖f i‖) * (Real.sqrt (w i) * ‖g i‖) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hw i hi)]
      calc
        w i * ‖f i‖ * ‖g i‖ =
            (Real.sqrt (w i) * Real.sqrt (w i)) * ‖f i‖ * ‖g i‖ := by
          rw [Real.mul_self_sqrt (hw i hi)]
        _ = _ := by ring
    _ ≤ Real.sqrt (weightedEnergy s w f) * Real.sqrt (weightedEnergy s w g) := by
      simpa only [hf, hg] using Real.sum_mul_le_sqrt_mul_sqrt s
        (fun i => Real.sqrt (w i) * ‖f i‖) (fun i => Real.sqrt (w i) * ‖g i‖)

theorem fiber_energy_bound {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (p : ι → κ) (w : ι → ℝ)
    (D E : κ → ℝ) (hp : ∀ i ∈ s, p i ∈ t)
    (hE : ∀ j ∈ t, 0 ≤ E j)
    (hD : ∀ j ∈ t, ∑ i ∈ s with p i = j, w i ≤ D j) :
    ∑ i ∈ s, w i * E (p i) ≤ ∑ j ∈ t, D j * E j := by
  calc
    ∑ i ∈ s, w i * E (p i) =
        ∑ j ∈ t, ∑ i ∈ s with p i = j, w i * E (p i) :=
      (Finset.sum_fiberwise_of_maps_to hp _).symm
    _ = ∑ j ∈ t, (∑ i ∈ s with p i = j, w i) * E j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ ≤ ∑ j ∈ t, D j * E j :=
      Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hD j hj) (hE j hj)

theorem weightedEnergy_fiber_bound {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (p : ι → κ) (w : ι → ℝ)
    (D : κ → ℝ) (f : κ → ℂ) (hp : ∀ i ∈ s, p i ∈ t)
    (hD : ∀ j ∈ t, ∑ i ∈ s with p i = j, w i ≤ D j) :
    weightedEnergy s w (f ∘ p) ≤ weightedEnergy t D f := by
  exact fiber_energy_bound s t p w D (fun j => ‖f j‖ ^ 2) hp
    (fun j _ => sq_nonneg _) hD

theorem weighted_cauchy_fiber {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (p : ι → κ) (w : ι → ℝ)
    (D : κ → ℝ) (f g : κ → ℂ) (hp : ∀ i ∈ s, p i ∈ t)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hD : ∀ j ∈ t, ∑ i ∈ s with p i = j, w i ≤ D j) :
    ‖∑ i ∈ s, (w i : ℂ) * f (p i) * star (g (p i))‖ ≤
      Real.sqrt (weightedEnergy t D f) * Real.sqrt (weightedEnergy t D g) := by
  apply (weighted_cauchy s w (f ∘ p) (g ∘ p) hw).trans
  exact mul_le_mul
    (Real.sqrt_le_sqrt (weightedEnergy_fiber_bound s t p w D f hp hD))
    (Real.sqrt_le_sqrt (weightedEnergy_fiber_bound s t p w D g hp hD))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem finite_expansion_energy {κ ι : Type*} [DecidableEq ι]
    (rows : Finset κ) (terms : Finset ι) (active : κ → Finset ι)
    (w F : κ → ι → ℂ) (C : ℝ)
    (hsub : ∀ k ∈ rows, active k ⊆ terms)
    (hw : ∀ k ∈ rows, ∀ i ∈ active k, ‖w k i‖ ≤ 1)
    (hcard : ∀ k ∈ rows, ((active k).card : ℝ) ≤ C) :
    (∑ k ∈ rows, ‖∑ i ∈ active k, w k i * F k i‖ ^ 2) ≤
      C * ∑ i ∈ terms, ∑ k ∈ rows, if i ∈ active k then ‖F k i‖ ^ 2 else 0 := by
  have hlocal (k : κ) (hk : k ∈ rows) :
      ‖∑ i ∈ active k, w k i * F k i‖ ^ 2 ≤
        C * ∑ i ∈ active k, ‖F k i‖ ^ 2 := by
    have hb : ‖∑ i ∈ active k, w k i * F k i‖ ^ 2 ≤
        ((active k).card : ℝ) * ∑ i ∈ active k, ‖w k i * F k i‖ ^ 2 := by
      calc
        _ ≤ (∑ i ∈ active k, ‖w k i * F k i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ _ := by
          simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
            Finset.sum_mul_sq_le_sq_mul_sq (active k) (fun _ => (1 : ℝ))
              (fun i => ‖w k i * F k i‖)
    have hsum : (∑ i ∈ active k, ‖w k i * F k i‖ ^ 2) ≤
        ∑ i ∈ active k, ‖F k i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hw k hk i hi)
    exact hb.trans (mul_le_mul (hcard k hk) hsum
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (le_trans (Nat.cast_nonneg _) (hcard k hk)))
  calc
    _ ≤ ∑ k ∈ rows, C * ∑ i ∈ active k, ‖F k i‖ ^ 2 :=
      Finset.sum_le_sum hlocal
    _ = C * ∑ k ∈ rows, ∑ i ∈ active k, ‖F k i‖ ^ 2 := by rw [Finset.mul_sum]
    _ = C * ∑ k ∈ rows, ∑ i ∈ terms, if i ∈ active k then ‖F k i‖ ^ 2 else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter]
      exact ⟨fun hi => ⟨hsub k hk hi, hi⟩, And.right⟩
    _ = _ := by rw [Finset.sum_comm]

end

end SevenEighths.InverseMoment

end OAI
