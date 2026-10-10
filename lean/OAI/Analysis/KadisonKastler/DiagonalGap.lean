import OAI.Analysis.KadisonKastler.CountableDiagonalAlgebra

namespace OAI

/-! # Exact preservation of the operator-norm gap by countable diagonalization -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem countableDiagonalAlgebra_mono {M N : VonNeumannAlgebra H} (hMN : M ≤ N) :
    countableDiagonalAlgebra M ≤ countableDiagonalAlgebra N := by
  apply generatedVonNeumannAlgebra_le_of_le
  rintro T ⟨a, rfl⟩
  exact subset_generatedVonNeumannAlgebra _ ⟨⟨a.val, hMN a.property⟩, rfl⟩

theorem unitBall_countableDiagonal (M : VonNeumannAlgebra H) :
    unitBall (countableDiagonalAlgebra M) =
      l2Diagonal '' unitBall M := by
  ext T
  constructor
  · intro hT
    obtain ⟨a, ha, rfl⟩ := countableDiagonalHom_surjective_unitBall M T hT.1 hT.2
    exact ⟨a.val, ⟨a.property, ha⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨subset_generatedVonNeumannAlgebra _ ⟨⟨a, ha.1⟩, rfl⟩,
      (norm_l2Diagonal H a).le.trans ha.2⟩

theorem kkDistance_countableDiagonal (M N : VonNeumannAlgebra H) :
    kkDistance (countableDiagonalAlgebra M) (countableDiagonalAlgebra N) =
      kkDistance M N := by
  have hi : Isometry (l2Diagonal (E := H)) := by
    apply isometry_iff_dist_eq.mpr
    intro a b
    simp only [dist_eq_norm]
    change ‖(l2DiagonalHom (E := H)) a - (l2DiagonalHom (E := H)) b‖ = ‖a - b‖
    rw [← map_sub]
    exact norm_l2Diagonal H (a - b)
  change Metric.hausdorffDist _ _ = Metric.hausdorffDist _ _
  rw [unitBall_countableDiagonal, unitBall_countableDiagonal]
  exact Metric.hausdorffDist_image hi

theorem kkDistance_lt_two_mul_of_nearInclusions {M N : VonNeumannAlgebra H}
    {γ : ℝ} (hγ : 0 < γ) (hMN : NearInclusion M N γ) (hNM : NearInclusion N M γ) :
    kkDistance M N < 2 * γ := by
  obtain ⟨a, ha, hMa⟩ := hMN
  obtain ⟨b, hb, hNb⟩ := hNM
  let c := max 0 (max a b)
  have hc : c < γ := max_lt hγ (max_lt ha hb)
  have hca : a ≤ c := (le_max_left a b).trans (le_max_right 0 (max a b))
  have hcb : b ≤ c := (le_max_right a b).trans (le_max_right 0 (max a b))
  have hc0 : 0 ≤ c := le_max_left _ _
  have hMc : NearInclusion M N ((c + γ) / 2) :=
    ⟨a, by linarith, hMa⟩
  have hNc : NearInclusion N M ((c + γ) / 2) :=
    ⟨b, by linarith, hNb⟩
  exact (kkDistance_le_two_mul_of_nearInclusions (by linarith) hMc hNc).trans_lt
    (by linarith)

end

end KadisonKastler

end OAI
