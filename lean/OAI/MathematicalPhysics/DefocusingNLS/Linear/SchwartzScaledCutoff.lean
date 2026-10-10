import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzAnnulusSampling

namespace OAI

/-! # Uniform finite jets after a slowly varying cutoff

On normalized annuli the extra cutoff is χ(δ x), with 0 < δ ≤ 1.  Its
derivatives cost no inverse scale, so the same finite jet bound is uniform in δ.
-/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def schwartzScaledCutoff (δ : ℝ) (χ ψ : 𝓢(E, ℂ))
    (hψ : HasCompactSupport (ψ : E → ℂ)) : 𝓢(E, ℂ) :=
  (hψ.mul_right (f' := fun x => χ (δ • x))).toSchwartzMap
    (ψ.smooth'.mul (χ.smooth'.comp (contDiff_id.const_smul δ)))

@[simp] theorem schwartzScaledCutoff_apply (δ : ℝ) (χ ψ : 𝓢(E, ℂ))
    (hψ : HasCompactSupport (ψ : E → ℂ)) (x : E) :
    schwartzScaledCutoff δ χ ψ hψ x = ψ x * χ (δ • x) := rfl

noncomputable def schwartzCutoffJetConstant (χ : 𝓢(E, ℂ)) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 (n - i) χ

theorem schwartzCutoffJetConstant_nonneg (χ : 𝓢(E, ℂ)) (N : ℕ) :
    0 ≤ schwartzCutoffJetConstant χ N := by
  unfold schwartzCutoffJetConstant
  positivity

theorem schwartzScaledCutoff_jet_bound (δ D : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hD : 0 ≤ D) (χ ψ : 𝓢(E, ℂ)) (hψ : HasCompactSupport (ψ : E → ℂ))
    (N : ℕ)
    (hjet : ∀ n ≤ N, ∀ x : E, (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n ψ x‖ ≤ D)
    (n : ℕ) (hn : n ≤ N) (x : E) :
    (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n (schwartzScaledCutoff δ χ ψ hψ) x‖ ≤
      schwartzCutoffJetConstant χ N * D := by
  have hχ (j : ℕ) : ‖iteratedFDeriv ℝ j (fun y : E => χ (δ • y)) x‖ ≤
      SchwartzMap.seminorm ℝ 0 j χ := by
    have hd : iteratedFDeriv ℝ j (fun y : E => χ (δ • y)) x =
        δ ^ j • iteratedFDeriv ℝ j χ (δ • x) := by
      simpa only using! congrFun
        (iteratedFDeriv_comp_const_smul δ (χ.smooth'.of_le (by simp))) x
    rw [hd]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hδ j)]
    calc
      _ ≤ 1 * SchwartzMap.seminorm ℝ 0 j χ :=
        mul_le_mul (pow_le_one₀ hδ.le hδ1)
          (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ χ j (δ • x))
          (norm_nonneg _) (by positivity)
      _ = _ := one_mul _
  have hp : ‖iteratedFDeriv ℝ n (schwartzScaledCutoff δ χ ψ hψ) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i ψ x‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun y : E => χ (δ • y)) x‖ := by
    exact norm_iteratedFDeriv_mul_le ψ.smooth'
      (χ.smooth'.comp (contDiff_id.const_smul δ)) x (by simp)
  have hsum : (∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 (n - i) χ) ≤
      schwartzCutoffJetConstant χ N := by
    unfold schwartzCutoffJetConstant
    exact Finset.single_le_sum (f := fun j : ℕ => ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 (j - i) χ)
      (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  calc
    _ ≤ (1 + ‖x‖) ^ N * (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ x‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun y : E => χ (δ • y)) x‖) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ((1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ i ψ x‖) *
          ‖iteratedFDeriv ℝ (n - i) (fun y : E => χ (δ • y)) x‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * D *
        SchwartzMap.seminorm ℝ 0 (n - i) χ := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i ≤ N := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hn
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hjet i hiN x) (Nat.cast_nonneg _))
        (hχ (n - i)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hD)
    _ = (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 (n - i) χ) * D := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsum hD

end DefocusingNLS

end OAI
