import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningRootConstruction

namespace OAI

/-! The explicit turn lies before half the natural remote radius. -/

namespace DefocusingNLS

theorem spectralTurningRoot_remote (ell : ℕ) (h b omega E : ℝ)
    (hh : |h| ≤ 1) (hb : 0 ≤ b) (hw : 0 ≤ omega) (hE : 0 < E)
    (hscale : E^2 = 256*max ((ell : ℝ)+1) omega) :
    2*spectralTurningRoot h b ((ell : ℝ)*(ell+10)) omega ≤ E := by
  let S := max ((ell : ℝ)+1) omega
  let r := E/2
  let L := (ell : ℝ)*(ell+10)+99/4
  have hell : 0 ≤ (ell : ℝ) := Nat.cast_nonneg ell
  have hS : 1 ≤ S := le_trans (by linarith) (le_max_left _ _)
  have hwS : omega ≤ S := le_max_right _ _
  have hr : 0 < r := by dsimp only [r]; positivity
  have hr2 : r^2 = 64*S := by dsimp only [r,S]; nlinarith [hscale]
  have hL : L ≤ 25*S^2 := by
    have he : ((ell : ℝ)+1)^2 ≤ S^2 :=
      (sq_le_sq₀ (by positivity) (by linarith)).mpr (le_max_left _ _)
    dsimp only [L]
    nlinarith
  have hhw : h*omega ≤ omega := by nlinarith [abs_le.mp hh]
  have hprod : h*omega*r^2 ≤ S*r^2 :=
    mul_le_mul_of_nonneg_right (hhw.trans hwS) (sq_nonneg r)
  have hbr : 0 ≤ b*r^2 := mul_nonneg hb (sq_nonneg r)
  have hid : r^2*homogeneousSpectralLocalizationFrequency h b
      ((ell : ℝ)*(ell+10)) omega r = r^4/16+b*r^2-h*omega*r^2-L := by
    dsimp only [homogeneousSpectralLocalizationFrequency,L]
    field_simp [hr.ne']
  have hF : 0 < homogeneousSpectralLocalizationFrequency h b
      ((ell : ℝ)*(ell+10)) omega r := by
    have hS2 : 0 < S^2 := sq_pos_of_pos (by linarith)
    have hr4 : r^4 = (64*S)^2 := by rw [show r^4 = (r^2)^2 by ring,hr2]
    have hp : 0 < r^2*homogeneousSpectralLocalizationFrequency h b
        ((ell : ℝ)*(ell+10)) omega r := by
      rw [hid,hr4]
      rw [hr2] at hprod
      nlinarith
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hr)).mp hp
  obtain ⟨ht,htF⟩ := spectralTurningRoot_data h b ((ell : ℝ)*(ell+10)) omega (by positivity)
  have hlt : spectralTurningRoot h b ((ell : ℝ)*(ell+10)) omega < r := by
    by_contra hn
    have hm := (homogeneousSpectralLocalizationFrequency_strictMono h b
      ((ell : ℝ)*(ell+10)) omega (by positivity)).monotoneOn hr ht (le_of_not_gt hn)
    rw [htF] at hm
    exact (not_le_of_gt hF) hm
  dsimp only [r] at hlt
  linarith

end DefocusingNLS

end OAI
