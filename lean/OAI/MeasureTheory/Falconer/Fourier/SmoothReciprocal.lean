import OAI.MeasureTheory.Falconer.Angular.SmoothInverseSine
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace OAI

/-!
# Smooth reciprocal of a nonstationary phase derivative

The reciprocal is extended smoothly across zero by a scalar bump. At a
point where the denominator is bounded below, its derivative bounds
depend only on the normalized derivatives of that denominator.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

noncomputable def smoothReciprocal (τ : ℝ) (hτ : 0 < τ) (u : ℝ) : ℝ :=
  (1 - PlanarFalconer.sineZeroCutoff τ hτ u) * u⁻¹

theorem smoothReciprocal_contDiff (τ : ℝ) (hτ : 0 < τ) :
    ContDiff ℝ ∞ (smoothReciprocal τ hτ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hb := (PlanarFalconer.sineZeroCutoff τ hτ).eventuallyEq_one
    have he : smoothReciprocal τ hτ =ᶠ[𝓝 0] (fun _ => 0) := by
      filter_upwards [hb] with y hy
      simp [smoothReciprocal,hy]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (contDiffAt_const.sub (PlanarFalconer.sineZeroCutoff τ hτ).contDiffAt).mul
      (contDiffAt_id.inv hx)

theorem smoothReciprocal_eq {τ u : ℝ} (hτ : 0 < τ) (hu : τ ≤ |u|) :
    u * smoothReciprocal τ hτ u = 1 := by
  have hb : PlanarFalconer.sineZeroCutoff τ hτ u = 0 :=
    (PlanarFalconer.sineZeroCutoff τ hτ).zero_of_le_dist
      (by simpa [PlanarFalconer.sineZeroCutoff, Real.dist_eq] using hu)
  have hune : u ≠ 0 := by intro he; simp [he] at hu; linarith
  simp [smoothReciprocal,hb,hune]

theorem smoothReciprocal_half_germ {g : ℝ → ℝ} (hg : Continuous g)
    {τ x : ℝ} (hτ : 0 < τ) (hx : τ ≤ |g x|) :
    (fun y => smoothReciprocal (τ/2) (half_pos hτ) (g y) * g y)
      =ᶠ[𝓝 x] (fun _ => 1) := by
  have hlt : τ/2 < |g x| := (half_lt_self hτ).trans_le hx
  have he : ∀ᶠ y in 𝓝 x, τ/2 < |g y| := hg.abs.continuousAt.eventually (lt_mem_nhds hlt)
  filter_upwards [he] with y hy
  simpa only [mul_comm] using smoothReciprocal_eq (half_pos hτ) hy.le

/-- The derivative constants are independent of the denominator, its
lower bound, and the frequency scale. Only positive-order derivatives
of the denominator enter the recurrence. -/
theorem reciprocal_germ_derivatives (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g q : ℝ → ℝ), ContDiff ℝ ∞ g → ContDiff ℝ ∞ q →
      ∀ (τ D x : ℝ), 0 < τ → 0 ≤ D → τ ≤ |g x| →
      (fun y => q y * g y) =ᶠ[𝓝 x] (fun _ => 1) →
      (∀ k, 1 ≤ k → k ≤ n → |iteratedDeriv k g x| ≤ B k * τ * D^k) →
      |iteratedDeriv n q x| ≤ C * τ⁻¹ * D^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      refine ⟨1, zero_le_one, ?_⟩
      intro g q hg hq τ D x hτ hD hx he _
      have hgne : g x ≠ 0 := by intro hz; simp [hz] at hx; linarith
      have hqv : q x = (g x)⁻¹ := by
        calc
          q x = q x * g x * (g x)⁻¹ := by rw [mul_assoc,mul_inv_cancel₀ hgne,mul_one]
          _ = _ := by rw [he.eq_of_nhds,one_mul]
      simp only [iteratedDeriv_zero,hqv,abs_inv,pow_zero,mul_one,one_mul]
      exact (inv_le_inv₀ (lt_of_lt_of_le hτ hx) hτ).mpr hx
    | succ n =>
      let C₀ : ℕ → ℝ := fun k => if hk : k < n+1 then (ih k hk).choose else 0
      have hC₀ (k : ℕ) : 0 ≤ C₀ k := by
        dsimp [C₀]
        split_ifs with hk
        · exact (ih k hk).choose_spec.1
        · exact le_rfl
      let C := ∑ k ∈ Finset.range (n+1), ((n+1).choose k : ℝ) * C₀ k * B (n+1-k)
      have hC : 0 ≤ C := Finset.sum_nonneg (fun k _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC₀ k)) (hB _))
      refine ⟨C,hC,?_⟩
      intro g q hg hq τ D x hτ hD hx he hgb
      have hqfin : ContDiffAt ℝ (n+1 : ℕ) q x :=
        (hq.of_le (WithTop.coe_le_coe.mpr (show ((n+1 : ℕ) : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      have hgfin : ContDiffAt ℝ (n+1 : ℕ) g x :=
        (hg.of_le (WithTop.coe_le_coe.mpr (show ((n+1 : ℕ) : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      have hid := he.iteratedDeriv_eq (n+1)
      rw [iteratedDeriv_fun_mul hqfin hgfin, Finset.sum_range_succ] at hid
      simp only [Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self,iteratedDeriv_zero,
        iteratedDeriv_const,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte] at hid
      have hlast : iteratedDeriv (n+1) q x * g x =
          -(∑ k ∈ Finset.range (n+1), ((n+1).choose k : ℝ) *
            iteratedDeriv k q x * iteratedDeriv (n+1-k) g x) := by linarith
      have hsum : |iteratedDeriv (n+1) q x| * |g x| ≤ C * D^(n+1) := by
        rw [← abs_mul,hlast,abs_neg]
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        change _ ≤ (∑ k ∈ Finset.range (n+1), _) * _
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro k hk
        have hk' : k < n+1 := Finset.mem_range.mp hk
        have hqk := (ih k hk').choose_spec.2 g q hg hq τ D x hτ hD hx he
          (fun j hj hjk => hgb j hj (by omega))
        have hCk : C₀ k = (ih k hk').choose := dite_eq_left hk'
        rw [← hCk] at hqk
        rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
        calc
          _ ≤ ((n+1).choose k : ℝ) * (C₀ k * τ⁻¹ * D^k) *
              (B (n+1-k) * τ * D^(n+1-k)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hqk (Nat.cast_nonneg _))
              (hgb (n+1-k) (by omega) (by omega)) (abs_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _)
                (mul_nonneg (mul_nonneg (hC₀ k) (inv_nonneg.mpr hτ.le)) (pow_nonneg hD k)))
          _ = ((n+1).choose k : ℝ) * C₀ k * B (n+1-k) * D^(n+1) := by
            have hpow : D^k * D^(n+1-k) = D^(n+1) := by
              rw [← pow_add, Nat.add_sub_of_le (by omega : k ≤ n+1)]
            calc
              _ = ((n+1).choose k : ℝ) * C₀ k * B (n+1-k) *
                  (τ⁻¹*τ) * (D^k*D^(n+1-k)) := by ring
              _ = _ := by rw [inv_mul_cancel₀ hτ.ne',mul_one,hpow]
      have hsmall : |iteratedDeriv (n+1) q x| * τ ≤ C * D^(n+1) :=
        (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans hsum
      have hh := (le_div_iff₀ hτ).mpr hsmall
      simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh

end Falconer

end OAI
