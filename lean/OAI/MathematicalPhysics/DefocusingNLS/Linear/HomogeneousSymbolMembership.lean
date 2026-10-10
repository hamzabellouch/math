import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDyadicPartition

namespace OAI

/-! # Actual homogeneous-space membership from physical symbol estimates

A smooth physical profile with the manuscript's `|x|^(-2a)` derivative decay
has a representative in the faithful Fourier completion.  The proof builds
the representative from a compact core and normalized dyadic annuli.
-/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem exists_finite_symbol_membership_order (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    ∃ N : ℕ, ∀ (Q : E → ℂ), ContDiff ℝ ∞ Q → ∀ D : ℝ, 0 ≤ D →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 →
        ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      ∃ q : HomogeneousY a k, ∀ y : E, homogeneousPhysicalCLM a k ha ha1 hk q y = Q y := by
  obtain ⟨N, C, _hC, hCbound⟩ := exists_homogeneous_from_schwartz_annuli a k ha ha1 hk
  refine ⟨N, ?_⟩
  intro Q hQ D hD hsymbol
  let κ := homogeneousAnnulusCutoff
  let hκ := homogeneousAnnulusCutoff_hasCompactSupport
  let ψ : ℕ → 𝓢(E, ℂ) := fun j =>
    homogeneousAnnulusPiece a ((2 : ℝ) ^ j) κ hκ Q hQ
  let J := homogeneousAnnulusJetConstant a κ N
  have hJ : 0 ≤ J := homogeneousAnnulusJetConstant_nonneg a κ N
  have hjet (j n : ℕ) (hn : n ≤ N) (x : E) :
      (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n (ψ j) x‖ ≤ J * D :=
    homogeneousAnnulusPiece_jet_bound a ((2 : ℝ) ^ j) D ha (by positivity) hD
      κ hκ homogeneousAnnulusCutoff_support Q hQ N hsymbol n hn x
  obtain ⟨qtail, htail, _hnorm⟩ := hCbound ψ (J * D) (mul_nonneg hJ hD) hjet
  let core : 𝓢(E, ℂ) :=
    (homogeneousCoreCutoff_hasCompactSupport.mul_right (f' := Q)).toSchwartzMap
      (homogeneousCoreCutoff.smooth'.mul hQ)
  refine ⟨homogeneousSchwartzEmbedding a k ha ha1 hk core + qtail, ?_⟩
  intro y
  have ht : homogeneousPhysicalCLM a k ha ha1 hk qtail y =
      (1 - homogeneousCoreCutoff y) * Q y := by
    rw [htail]
    have he (j : ℕ) :
        (((2 : ℝ) ^ j) ^ (-2 * a) : ℝ) * ψ j (((2 : ℝ) ^ j)⁻¹ • y) =
          homogeneousAnnulusCutoff (((2 : ℝ) ^ j)⁻¹ • y) * Q y :=
      homogeneousAnnulusPiece_rescale a ((2 : ℝ) ^ j) (by positivity) κ hκ Q hQ y
    simp_rw [he]
    exact ((homogeneousAnnulusCutoff_dyadic_sum y).mul_right (Q y)).tsum_eq
  rw [map_add]
  change homogeneousPhysicalCLM a k ha ha1 hk
    (homogeneousSchwartzEmbedding a k ha ha1 hk core) y +
      homogeneousPhysicalCLM a k ha ha1 hk qtail y = _
  rw [homogeneousPhysicalCLM_Schwartz, ht]
  change homogeneousCoreCutoff y * Q y + (1 - homogeneousCoreCutoff y) * Q y = Q y
  ring

theorem exists_homogeneous_of_symbol_decay (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) :
    ∃ q : HomogeneousY a k, ∀ y : E, homogeneousPhysicalCLM a k ha ha1 hk q y = Q y := by
  obtain ⟨N, hN⟩ := exists_finite_symbol_membership_order a k ha ha1 hk
  choose D hD hDbound using hsymbol
  let B := ∑ n ∈ Finset.range (N + 1), D n
  have hB : 0 ≤ B := Finset.sum_nonneg (fun n _ => hD n)
  apply hN Q hQ B hB
  intro n hn y hy
  have hnB : D n ≤ B :=
    Finset.single_le_sum (fun j _ => hD j) (Finset.mem_range.mpr (by omega))
  exact (hDbound n y hy).trans
    (mul_le_mul_of_nonneg_right hnB (Real.rpow_nonneg (norm_nonneg _) _))

/-- Only the decay at infinity needs to be supplied; smoothness controls the core. -/
theorem exists_homogeneous_of_symbol_decay_at_infinity (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, ∀ y : E, 1 ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) :
    ∃ q : HomogeneousY a k, ∀ y : E, homogeneousPhysicalCLM a k ha ha1 hk q y = Q y := by
  apply exists_homogeneous_of_symbol_decay a k ha ha1 hk Q hQ
  intro n
  obtain ⟨D, hD⟩ := hsymbol n
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn
    ((hQ.of_le (by simp : (n : ℕ∞ω) ≤ ∞)).continuous_iteratedFDeriv'.continuousOn)
  let B := max (max C 0) D
  have hB : 0 ≤ B := (le_max_right C 0).trans (le_max_left _ _)
  refine ⟨B, hB, ?_⟩
  intro y hy
  by_cases hlarge : 1 ≤ ‖y‖
  · exact (hD y hlarge).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _))
  · have hsmall : ‖y‖ ≤ 1 := (lt_of_not_ge hlarge).le
    have hyB : ‖iteratedFDeriv ℝ n Q y‖ ≤ B :=
      (hC y (by simpa [Metric.mem_closedBall, dist_zero_right] using hsmall)).trans
        ((le_max_left C 0).trans (le_max_left _ _))
    have hpow : 1 ≤ ‖y‖ ^ (-2 * a - (n : ℝ)) := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      have h := Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hy) hsmall
        (show -2 * a - (n : ℝ) ≤ 0 by linarith)
      simpa using h
    exact hyB.trans (le_mul_of_one_le_right hB hpow)

end DefocusingNLS

end OAI
