import OAI.Analysis.KadisonKastler.NestCornerExtension

namespace OAI

/-! # Contractive completion for a finite chain of projections -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem extend_finite_projection_chain (T : H →L[ℂ] H)
    (L : List (H →L[ℂ] H))
    (hchain : L.Pairwise (fun P R => P * R = P))
    (hdata : ∀ R ∈ L, IsStarProjection R ∧ ‖(1 - R) * T * R‖ ≤ 1)
    (P X : H →L[ℂ] H) (hP : IsStarProjection P)
    (hbase : ∀ R ∈ L, P * R = P)
    (hX : ‖X‖ ≤ 1) (hXP : X * P = X)
    (hmatch : (1 - P) * X = (1 - P) * T * P) :
    ∃ Y : H →L[ℂ] H, ‖Y‖ ≤ 1 ∧ Y * P = X ∧
      ∀ R ∈ L, (1 - R) * Y * R = (1 - R) * T * R := by
  induction L generalizing P X with
  | nil => exact ⟨X, hX, hXP, by simp⟩
  | cons R L ih =>
    obtain ⟨hRL, hchainL⟩ := List.pairwise_cons.mp hchain
    obtain ⟨hR, hTR⟩ := hdata R (by simp)
    have hPR : P * R = P := hbase R (by simp)
    have hRP := nested_projection_reverse hP hR hPR
    have hQP : (1 - R) * P = 0 := by rw [sub_mul, one_mul, hRP, sub_self]
    have hQQ : (1 - R) * (1 - P) = 1 - R := by
      rw [mul_sub, mul_one, hQP, sub_zero]
    have hnext : (1 - R) * X = (1 - R) * T * P := by
      calc
        _ = (1 - R) * ((1 - P) * X) := by rw [← mul_assoc, hQQ]
        _ = (1 - R) * ((1 - P) * T * P) := by rw [hmatch]
        _ = _ := by rw [← mul_assoc, ← mul_assoc, hQQ]
    obtain ⟨Z, hZ, hZP, hZR, hQZ⟩ :=
      extend_contractive_nest_corner P R (1 - R) T X hP hR hR.one_sub hPR hX hXP hnext hTR
    obtain ⟨Y, hY, hYR, hrest⟩ := ih hchainL
      (fun S hS => hdata S (by simp [hS])) R Z hR hRL hZ hZR hQZ
    refine ⟨Y, hY, ?_, ?_⟩
    · calc
        Y * P = Y * (R * P) := by rw [hRP]
        _ = Z * P := by rw [← mul_assoc, hYR]
        _ = X := hZP
    · intro S hS
      rcases List.mem_cons.mp hS with rfl | hS
      · rw [mul_assoc, hYR, hQZ]
      · exact hrest S hS

theorem finite_projection_chain_completion (T : H →L[ℂ] H)
    (L : List (H →L[ℂ] H))
    (hchain : L.Pairwise (fun P R => P * R = P))
    (hdata : ∀ R ∈ L, IsStarProjection R ∧ ‖(1 - R) * T * R‖ ≤ 1) :
    ∃ X : H →L[ℂ] H, ‖X‖ ≤ 1 ∧
      ∀ R ∈ L, (1 - R) * X * R = (1 - R) * T * R := by
  obtain ⟨X, hX, _, hfix⟩ := extend_finite_projection_chain T L hchain hdata 0 0
    (IsStarProjection.zero (H →L[ℂ] H)) (by simp) (by simp) (by simp) (by simp)
  exact ⟨X, hX, hfix⟩

end

end KadisonKastler

end OAI
