import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzScaledCutoff

namespace OAI

/-! # Uniform sampling of the fixed compact core of a profile -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem exists_schwartz_weightedJet_bound (ψ : 𝓢(E, ℂ)) (N : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n ≤ N, ∀ x : E,
      (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n ψ x‖ ≤ D := by
  let D : ℝ := 2 ^ N * (Finset.Iic (N, N)).sup (schwartzSeminormFamily ℝ E ℂ) ψ
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro n hn x
  simpa only [D, schwartzSeminormFamily] using!
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (N, N)) (k := N) (n := n) le_rfl hn ψ x

theorem exists_schwartzCore_sampling_bound (a k : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (χ ψ : 𝓢(E, ℂ)) (hψ : HasCompactSupport (ψ : E → ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 ≤ L),
      ‖schwartzTorusSample a k L ha1 hk hL
        (radianFourierKernel (schwartzScaledCutoff L⁻¹ χ ψ hψ))‖ ≤ C := by
  obtain ⟨N, C, hC, hb⟩ := exists_schwartzTorusSample_physicalJet_bound a k ha1 hk
  obtain ⟨D, hD, hjet⟩ := exists_schwartz_weightedJet_bound ψ N
  let B := schwartzCutoffJetConstant χ N
  have hB : 0 ≤ B := schwartzCutoffJetConstant_nonneg χ N
  refine ⟨C * (B * D), mul_nonneg hC (mul_nonneg hB hD), ?_⟩
  intro L hL
  have hLp : 0 < L := by linarith
  exact hb (schwartzScaledCutoff L⁻¹ χ ψ hψ) (B * D) (mul_nonneg hB hD)
    (fun n hn x => schwartzScaledCutoff_jet_bound L⁻¹ D (inv_pos.mpr hLp)
      ((inv_le_one₀ hLp).mpr hL) hD χ ψ hψ N hjet n hn x) L hL

end DefocusingNLS

end OAI
