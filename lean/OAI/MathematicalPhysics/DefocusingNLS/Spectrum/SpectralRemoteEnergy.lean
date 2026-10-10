import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemotePhysicalFrame
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDefectEnergy

namespace OAI

/-! Four-coordinate energy estimates for the remote evolution; the imaginary leading part cancels. -/

namespace DefocusingNLS

noncomputable def spectralRemoteEnergy (z : SpectralRemoteSpace) : ℝ :=
  homogeneousPairEnergy z.1+homogeneousPairEnergy z.2
noncomputable def spectralRemoteReal (z e : SpectralRemoteSpace) : ℝ :=
  homogeneousPairReal z.1 e.1+homogeneousPairReal z.2 e.2

noncomputable def spectralRemoteSkew (omega : SpectralRemoteIndex → ℝ)
    (z : SpectralRemoteSpace) : SpectralRemoteSpace :=
  ((Complex.I*(omega (0,0) : ℂ)*z.1.1,Complex.I*(omega (0,1) : ℂ)*z.1.2),
   (Complex.I*(omega (1,0) : ℂ)*z.2.1,Complex.I*(omega (1,1) : ℂ)*z.2.2))

theorem spectralRemoteEnergy_nonneg (z : SpectralRemoteSpace) : 0 ≤ spectralRemoteEnergy z :=
  add_nonneg (homogeneousPairEnergy_nonneg _) (homogeneousPairEnergy_nonneg _)

theorem spectralRemoteEnergy_lower (z : SpectralRemoteSpace) : ‖z‖^2 ≤ spectralRemoteEnergy z := by
  rcases le_total ‖z.1‖ ‖z.2‖ with h | h
  · rw [Prod.norm_def,max_eq_right h]
    exact (homogeneousPairEnergy_lower _).trans (le_add_of_nonneg_left (homogeneousPairEnergy_nonneg _))
  · rw [Prod.norm_def,max_eq_left h]
    exact (homogeneousPairEnergy_lower _).trans (le_add_of_nonneg_right (homogeneousPairEnergy_nonneg _))

theorem spectralRemoteEnergy_upper (z : SpectralRemoteSpace) : spectralRemoteEnergy z ≤ 4*‖z‖^2 := by
  have hp := homogeneousPairEnergy_upper z.1
  have hm := homogeneousPairEnergy_upper z.2
  have hpn := (sq_le_sq₀ (norm_nonneg z.1) (norm_nonneg z)).mpr (norm_fst_le z)
  have hmn := (sq_le_sq₀ (norm_nonneg z.2) (norm_nonneg z)).mpr (norm_snd_le z)
  dsimp only [spectralRemoteEnergy]
  nlinarith

theorem spectralRemoteReal_bound (z e : SpectralRemoteSpace) :
    |spectralRemoteReal z e| ≤ 4*‖z‖*‖e‖ := by
  have hp := homogeneousPairReal_bound z.1 e.1
  have hm := homogeneousPairReal_bound z.2 e.2
  calc
    _ ≤ |homogeneousPairReal z.1 e.1|+|homogeneousPairReal z.2 e.2| := abs_add_le _ _
    _ ≤ 2*‖z.1‖*‖e.1‖+2*‖z.2‖*‖e.2‖ := add_le_add hp hm
    _ ≤ 2*‖z‖*‖e‖+2*‖z‖*‖e‖ := by
      gcongr <;> first | exact norm_fst_le _ | exact norm_snd_le _
    _ = _ := by ring

theorem spectralRemoteReal_skew (z e : SpectralRemoteSpace) (omega : SpectralRemoteIndex → ℝ) :
    spectralRemoteReal z (spectralRemoteSkew omega z+e) = spectralRemoteReal z e := by
  simp only [spectralRemoteReal,spectralRemoteSkew,homogeneousPairReal,Prod.fst_add,Prod.snd_add,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem spectralRemoteEnergy_hasDerivAt (Y : ℝ → SpectralRemoteSpace) (e : SpectralRemoteSpace)
    (t : ℝ) (hY : HasDerivAt Y e t) :
    HasDerivAt (fun s => spectralRemoteEnergy (Y s)) (2*spectralRemoteReal (Y t) e) t := by
  have hp := (ContinuousLinearMap.fst ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt t hY
  have hm := (ContinuousLinearMap.snd ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt t hY
  have hd := (homogeneousPairEnergy_hasDerivAt hp).add (homogeneousPairEnergy_hasDerivAt hm)
  convert hd using 1
  · rfl
  · change 2*(homogeneousPairReal (Y t).1 e.1+homogeneousPairReal (Y t).2 e.2) =
      2*homogeneousPairReal (Y t).1 e.1+2*homogeneousPairReal (Y t).2 e.2
    ring

theorem spectralRemoteEnergy_skew_bound (Y : ℝ → SpectralRemoteSpace)
    (e : SpectralRemoteSpace) (omega : SpectralRemoteIndex → ℝ) (t C : ℝ) (hC : 0 ≤ C)
    (hY : HasDerivAt Y (spectralRemoteSkew omega (Y t)+e) t)
    (he : ‖e‖ ≤ C*‖Y t‖) :
    HasDerivAt (fun s => spectralRemoteEnergy (Y s)) (2*spectralRemoteReal (Y t) e) t ∧
      |2*spectralRemoteReal (Y t) e| ≤ 8*C*spectralRemoteEnergy (Y t) := by
  refine ⟨?_,?_⟩
  · simpa only [spectralRemoteReal_skew] using spectralRemoteEnergy_hasDerivAt Y _ t hY
  · calc
      _ = 2*|spectralRemoteReal (Y t) e| := by rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2*(4*‖Y t‖*‖e‖) := mul_le_mul_of_nonneg_left (spectralRemoteReal_bound _ _) (by norm_num)
      _ ≤ 2*(4*‖Y t‖*(C*‖Y t‖)) := by gcongr
      _ = 8*C*‖Y t‖^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (spectralRemoteEnergy_lower _) (by positivity)

end DefocusingNLS

end OAI
