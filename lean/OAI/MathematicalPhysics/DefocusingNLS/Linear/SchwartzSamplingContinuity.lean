import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSamplingSum
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingWeightIdentification

namespace OAI

/-! # Continuous sampling at a fixed period

The finite-jet estimate gives a continuous linear sampling map.  Combining it
with the exact dilation identity handles families at a changing physical scale.
-/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem physicalSampling_seminorm_bound (a k : ℝ)
    (ha1 : a < 1) (hk : 8 < k) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (L : ℝ) (hL : 1 ≤ L) (ψ : 𝓢(E, ℂ)),
        ‖physicalSchwartzTorusSamplingLinear a k L ha1 hk hL ψ‖ ≤
          C * S.sup (schwartzSeminormFamily ℂ E ℂ) ψ := by
  obtain ⟨N, C, hC, hb⟩ := exists_schwartzTorusSample_physicalJet_bound a k ha1 hk
  refine ⟨Finset.Iic (N, N), C * 2 ^ N, mul_nonneg hC (by positivity), ?_⟩
  intro L hL ψ
  have hj (n : ℕ) (hn : n ≤ N) (x : E) :
      (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n ψ x‖ ≤
        2 ^ N * (Finset.Iic (N, N)).sup (schwartzSeminormFamily ℂ E ℂ) ψ := by
    exact SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
      (m := (N, N)) (k := N) (n := n) le_rfl hn ψ x
  have h := hb ψ
    (2 ^ N * (Finset.Iic (N, N)).sup (schwartzSeminormFamily ℂ E ℂ) ψ)
    (by positivity) hj L hL
  simpa only [physicalSchwartzTorusSamplingLinear_apply, mul_assoc] using h

noncomputable def physicalSchwartzTorusSamplingCLM (a k L : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) : 𝓢(E, ℂ) →L[ℂ] FourierL2 :=
  SchwartzMap.mkCLMtoNormedSpace
    (physicalSchwartzTorusSamplingLinear a k L ha1 hk hL)
    (fun ψ φ => map_add (physicalSchwartzTorusSamplingLinear a k L ha1 hk hL) ψ φ)
    (fun c ψ => by
      exact map_smul (physicalSchwartzTorusSamplingLinear a k L ha1 hk hL) c ψ) (by
      obtain ⟨S, C, hC, hb⟩ := physicalSampling_seminorm_bound a k ha1 hk
      exact ⟨S, C, hC, hb L hL⟩)

@[simp] theorem physicalSchwartzTorusSamplingCLM_apply (a k L : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (ψ : 𝓢(E, ℂ)) :
    physicalSchwartzTorusSamplingCLM a k L ha1 hk hL ψ =
      schwartzTorusSample a k L ha1 hk hL (radianFourierKernel ψ) := rfl

/-- Changing period is reduced to period one after the physical dilation. -/
theorem continuous_dilatedPhysicalSampling {P : Type*} [TopologicalSpace P]
    (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (L : P → {L : ℝ // 1 ≤ L}) (hL : Continuous L)
    (ψ : P → 𝓢(E, ℂ)) (hψ : Continuous ψ) :
    Continuous (fun t => schwartzTorusSample a k (L t).1 ha1 hk (L t).2
      (radianFourierKernel
        (schwartzPhysicalDilation a (L t).1
          (lt_of_lt_of_le zero_lt_one (L t).2) (ψ t)))) := by
  have he (t : P) :
      schwartzTorusSample a k (L t).1 ha1 hk (L t).2
        (radianFourierKernel (schwartzPhysicalDilation a (L t).1
          (lt_of_lt_of_le zero_lt_one (L t).2) (ψ t))) =
      ((L t).1 ^ (-2 * a) : ℝ) •
        (expandingScaleTransfer a k 1 (L t).1 ha hk le_rfl (L t).2
          (physicalSchwartzTorusSamplingCLM a k 1 ha1 hk le_rfl (ψ t))) := by
    rw [radianFourierKernel_schwartzPhysicalDilation,
      schwartzTorusSample_homogeneousDilation a k (L t).1 (L t).1 ha ha1 hk
        (L t).2 le_rfl]
    simp only [div_self (ne_of_gt (lt_of_lt_of_le zero_lt_one (L t).2)),
      physicalSchwartzTorusSamplingCLM_apply]
  simp_rw [he]
  have hc : Continuous (fun t => (L t).1 ^ (-2 * a)) :=
    (continuous_subtype_val.comp hL).rpow_const
      (fun t => Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (L t).2)))
  exact hc.smul (((continuous_expandingScaleTransfer_from_one a k ha hk).comp hL).clm_apply
    ((physicalSchwartzTorusSamplingCLM a k 1 ha1 hk le_rfl).continuous.comp hψ))

end DefocusingNLS

end OAI
