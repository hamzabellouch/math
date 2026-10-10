import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteBlocks

namespace OAI

/-! Uniform gaps between the outgoing two-plane and each incoming line.
No gap is imposed within the outgoing block. -/

namespace DefocusingNLS

theorem spectralRemote_root_branch_bounds (h c : ℝ) (hh : h^2 = 1) (hc : |c| ≤ 1/32) :
    ‖homogeneousSpectralLocalizationRemoteRoot h 1 c‖ ≤ 1/8 ∧
      3/8 ≤ ‖homogeneousSpectralLocalizationRemoteRoot h (-1) c‖ := by
  have habs : |h| = 1 := by nlinarith [sq_abs h,abs_nonneg h]
  have hcl := (abs_le.mp hc).1
  have hcu := (abs_le.mp hc).2
  have hs0 := Real.sqrt_nonneg (1/16-c)
  have hs2 := Real.sq_sqrt (by linarith : 0 ≤ 1/16-c)
  have hslo : 1/8 ≤ Real.sqrt (1/16-c) := by nlinarith
  have hshi : Real.sqrt (1/16-c) ≤ 3/8 := by nlinarith
  simp only [homogeneousSpectralLocalizationRemoteRoot,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,Complex.norm_I,habs,one_mul]
  constructor
  · exact abs_le.mpr ⟨by linarith,by linarith⟩
  · rw [neg_one_mul,abs_of_nonpos (by linarith)]
    linarith

theorem spectralRemote_root_outgoing_incoming_gap (h k c d : ℝ)
    (hh : h^2 = 1) (hk : k^2 = 1) (hc : |c| ≤ 1/32) (hd : |d| ≤ 1/32) :
    1/4 ≤ ‖homogeneousSpectralLocalizationRemoteRoot h 1 c-
      homogeneousSpectralLocalizationRemoteRoot k (-1) d‖ := by
  have hp := (spectralRemote_root_branch_bounds h c hh hc).1
  have hm := (spectralRemote_root_branch_bounds k d hk hd).2
  have hn := norm_sub_norm_le
    (homogeneousSpectralLocalizationRemoteRoot k (-1) d)
    (homogeneousSpectralLocalizationRemoteRoot h 1 c)
  rw [norm_sub_rev] at hn
  linarith

theorem spectralRemote_root_incoming_gap (c d : ℝ) :
    1/2 ≤ ‖homogeneousSpectralLocalizationRemoteRoot 1 (-1) c-
      homogeneousSpectralLocalizationRemoteRoot (-1) (-1) d‖ := by
  have hs := Real.sqrt_nonneg (1/16-c)
  have ht := Real.sqrt_nonneg (1/16-d)
  have he : homogeneousSpectralLocalizationRemoteRoot 1 (-1) c-
      homogeneousSpectralLocalizationRemoteRoot (-1) (-1) d =
      -Complex.I*((1/2+Real.sqrt (1/16-c)+Real.sqrt (1/16-d) : ℝ) : ℂ) := by
    dsimp only [homogeneousSpectralLocalizationRemoteRoot]
    push_cast
    ring
  rw [he,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  linarith

noncomputable def spectralRemoteDiagonalRoot (c : Fin 2 → ℝ) (i : SpectralRemoteIndex) : ℂ :=
  homogeneousSpectralLocalizationRemoteRoot (if i.1 = 0 then 1 else -1)
    (if i.2 = 0 then 1 else -1) (c i.1)

theorem spectralRemote_block_gap (c : Fin 2 → ℝ) (hc : ∀ i, |c i| ≤ 1/32)
    (i j : SpectralRemoteIndex) (hij : spectralRemoteBlock i ≠ spectralRemoteBlock j) :
    1/4 ≤ ‖spectralRemoteDiagonalRoot c i-spectralRemoteDiagonalRoot c j‖ := by
  rcases i with ⟨i,bi⟩
  rcases j with ⟨j,bj⟩
  have hsign (a : Fin 2) : ((if a = 0 then 1 else -1) : ℝ)^2 = 1 := by
    split_ifs <;> norm_num
  by_cases hi : bi = 0
  · by_cases hj : bj = 0
    · simp [spectralRemoteBlock,hi,hj] at hij
    · simpa only [spectralRemoteDiagonalRoot,Prod.fst,Prod.snd,hi,hj,ite_true,ite_false] using
        spectralRemote_root_outgoing_incoming_gap _ _ _ _ (hsign i) (hsign j) (hc i) (hc j)
  · by_cases hj : bj = 0
    · have hg := spectralRemote_root_outgoing_incoming_gap _ _ _ _ (hsign j) (hsign i) (hc j) (hc i)
      rw [norm_sub_rev] at hg
      simpa only [spectralRemoteDiagonalRoot,Prod.fst,Prod.snd,hi,hj,ite_true,ite_false] using hg
    · have hne : i ≠ j := by
        intro he
        simp [spectralRemoteBlock,hi,hj,he] at hij
      fin_cases i <;> fin_cases j
      · exact False.elim (hne rfl)
      · have hg := spectralRemote_root_incoming_gap (c 0) (c 1)
        change 1/4 ≤ ‖homogeneousSpectralLocalizationRemoteRoot 1 (if bi = 0 then 1 else -1) (c 0)-
          homogeneousSpectralLocalizationRemoteRoot (-1) (if bj = 0 then 1 else -1) (c 1)‖
        rw [ite_eq_right hi,ite_eq_right hj]
        linarith
      · have hg := spectralRemote_root_incoming_gap (c 0) (c 1)
        rw [norm_sub_rev] at hg
        change 1/4 ≤ ‖homogeneousSpectralLocalizationRemoteRoot (-1) (if bi = 0 then 1 else -1) (c 1)-
          homogeneousSpectralLocalizationRemoteRoot 1 (if bj = 0 then 1 else -1) (c 0)‖
        rw [ite_eq_right hi,ite_eq_right hj]
        linarith
      · exact False.elim (hne rfl)

end DefocusingNLS

end OAI
