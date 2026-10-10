import OAI.MeasureTheory.Falconer.Angular.SmoothInverseSine
import OAI.MeasureTheory.Falconer.Angular.InheritedCircleRegularity

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

theorem reciprocal_sine_germ_derivatives (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℝ → ℝ), ContDiff ℝ ∞ q →
      ∀ η, 0 < η → η ≤ 1 → ∀ x, η ≤ |Real.sin x| →
      (fun y => q y * Real.sin y) =ᶠ[𝓝 x] (fun _ => 1) →
      |iteratedDeriv n q x| ≤ C * η⁻¹^(n+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      refine ⟨1, zero_le_one, ?_⟩
      intro q hq η hη hη1 x hx he
      have heq := he.eq_of_nhds
      have hs : Real.sin x ≠ 0 := by intro hz; simp [hz] at hx; linarith
      have hqv : q x = (Real.sin x)⁻¹ := by
        calc
          q x = q x * Real.sin x * (Real.sin x)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hs, mul_one]
          _ = (Real.sin x)⁻¹ := by rw [heq, one_mul]
      simp only [iteratedDeriv_zero, hqv, abs_inv, Nat.zero_add, pow_one, one_mul]
      exact inv_le_inv₀ (lt_of_lt_of_le hη hx) hη |>.mpr hx
    | succ n =>
      classical
      let B : ℕ → ℝ := fun k => if hk : k < n+1 then (ih k hk).choose else 0
      have hB0 (k : ℕ) : 0 ≤ B k := by
        dsimp [B]
        split_ifs with hk
        · exact (ih k hk).choose_spec.1
        · exact le_rfl
      let C := ∑ k ∈ Finset.range (n+1), ((n+1).choose k : ℝ) * B k
      have hC : 0 ≤ C := Finset.sum_nonneg (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hB0 k))
      refine ⟨C, hC, ?_⟩
      intro q hq η hη hη1 x hx he
      have hηinv : 1 ≤ η⁻¹ := (one_le_inv₀ hη).mpr hη1
      have hqfin : ContDiffAt ℝ (n+1 : ℕ) q x :=
        (hq.of_le (WithTop.coe_le_coe.mpr (show ((n+1 : ℕ) : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      have hsfin : ContDiffAt ℝ (n+1 : ℕ) Real.sin x := Real.contDiff_sin.contDiffAt
      have hid := he.iteratedDeriv_eq (n+1)
      rw [iteratedDeriv_fun_mul hqfin hsfin, Finset.sum_range_succ] at hid
      simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self,
        iteratedDeriv_zero, iteratedDeriv_const, Nat.add_eq_zero_iff,
        Nat.one_ne_zero, and_false, ↓reduceIte] at hid
      have hlast : iteratedDeriv (n+1) q x * Real.sin x =
          -(∑ k ∈ Finset.range (n+1),
            ((n+1).choose k : ℝ) * iteratedDeriv k q x * iteratedDeriv (n+1-k) Real.sin x) := by
        linarith
      have hsum : |iteratedDeriv (n+1) q x| * |Real.sin x| ≤ C * η⁻¹^(n+1) := by
        rw [← abs_mul, hlast, abs_neg]
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        change _ ≤ (∑ k ∈ Finset.range (n+1), _) * _
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro k hk
        have hk' : k < n+1 := Finset.mem_range.mp hk
        have hb := (ih k hk').choose_spec.2 q hq η hη hη1 x hx he
        change |iteratedDeriv k q x| ≤ (ih k hk').choose * η⁻¹^(k+1) at hb
        have hbk : |iteratedDeriv k q x| ≤ B k * η⁻¹^(n+1) := by
          have heB : B k = (ih k hk').choose := dite_eq_left hk'
          rw [heB]
          exact hb.trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hηinv (by omega)) (ih k hk').choose_spec.1)
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        calc
          _ ≤ ((n+1).choose k : ℝ) * (B k * η⁻¹^(n+1)) * 1 := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left hbk (Nat.cast_nonneg _))
              (Real.abs_iteratedDeriv_sin_le_one _ _) (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
                (mul_nonneg (hB0 k) (pow_nonneg (le_of_lt (inv_pos.mpr hη)) _)))
          _ = _ := by ring
      have hsmall : |iteratedDeriv (n+1) q x| * η ≤ C * η⁻¹^(n+1) :=
        (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans hsum
      have hh := (le_div_iff₀ hη).mpr hsmall
      simpa only [div_eq_mul_inv, pow_succ, mul_assoc] using hh

theorem smoothInverseSine_half_germ {η : ℝ} (hη : 0 < η) {x : ℝ}
    (hx : η ≤ |Real.sin x|) :
    (fun y => smoothInverseSine (η/2) (half_pos hη) y * Real.sin y)
      =ᶠ[𝓝 x] (fun _ => 1) := by
  have hh : η/2 < |Real.sin x| := (half_lt_self hη).trans_le hx
  have he : ∀ᶠ y in 𝓝 x, η/2 < |Real.sin y| :=
    (Real.continuous_sin.abs.continuousAt.eventually (lt_mem_nhds hh))
  filter_upwards [he] with y hy
  simpa only [mul_comm] using smoothInverseSine_eq (half_pos hη) hy.le

theorem smoothInverseSine_half_derivatives (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η (hη : 0 < η), η ≤ 1 → ∀ x, η ≤ |Real.sin x| →
      ‖iteratedDeriv n (fun y => (smoothInverseSine (η/2) (half_pos hη) y : ℂ)) x‖ ≤
        C * η⁻¹^(n+1) := by
  obtain ⟨C,hC,hb⟩ := reciprocal_sine_germ_derivatives n
  refine ⟨C,hC,?_⟩
  intro η hη hη1 x hx
  rw [iteratedDeriv_ofReal (smoothInverseSine_contDiff _ _), Complex.norm_real, Real.norm_eq_abs]
  exact hb _ (smoothInverseSine_contDiff _ _) η hη hη1 x hx (smoothInverseSine_half_germ hη hx)

end PlanarFalconer

end OAI
