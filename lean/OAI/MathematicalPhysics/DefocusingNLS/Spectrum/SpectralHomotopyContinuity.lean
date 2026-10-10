import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHomotopyHolomorphy

namespace OAI

/-! # Joint continuity in the tail homotopy and spectral parameters -/

open Matrix

namespace DefocusingNLS

attribute [local irreducible] slowTailRatio backwardProduct

theorem continuousAt_joint_matchingHomotopyColumn (ell : ℕ) (s q : ℂ) (ρ : ℝ)
    (hq : -(1 / 32 : ℝ) ≤ q.re - (ell : ℝ) / 2)
    (hs : s.re = 0) (hi : s.im ≠ 0) :
    ContinuousAt (fun x : ℝ × ℂ => matchingHomotopyColumn (ell + 5) 8 s x.1 x.2) (ρ, q) := by
  have hr := (analyticAt_slowTailRatio q ell 8 s (by decide) hq hs hi).continuousAt.comp
    (continuous_snd.continuousAt : ContinuousAt (fun x : ℝ × ℂ => x.2) (ρ, q))
  have hP (i j : Fin 2) :=
    (analyticAt_backwardProduct_entry (ell + 5) s q 8 i j).continuousAt.comp
      (continuous_snd.continuousAt : ContinuousAt (fun x : ℝ × ℂ => x.2) (ρ, q))
  apply continuousAt_pi.mpr
  intro i
  simp only [matchingHomotopyColumn, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have he : ell + 5 + 1 = ell + 6 := by omega
  rw [he]
  have hc := ((hP i 0).mul
    ((Complex.continuous_ofReal.comp continuous_fst).continuousAt.mul hr)).add
      ((hP i 1).mul (show ContinuousAt (fun _ : ℝ × ℂ => (1 : ℂ)) (ρ, q) from
        continuousAt_const))
  convert! hc using 1
  funext x
  simp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply, Nat.cast_add, Nat.cast_ofNat]

theorem continuousAt_joint_spectralHomotopyColumn (ell : ℕ) (h b Z ρ : ℝ) (z : ℂ)
    (hh : h ≠ 0) (hZ : Z ≠ 0) (hz : -(1 / 32 : ℝ) ≤ z.re) :
    ContinuousAt (fun x : ℝ × ℂ => matchingHomotopyColumn (ell + 5) 8
      ((h : ℂ) * Complex.I * Z) x.1 (spectralQ ell h b x.2)) (ρ, z) := by
  have hq : -(1 / 32 : ℝ) ≤ (spectralQ ell h b z).re - (ell : ℝ) / 2 := by
    rw [spectralQ_re]
    linarith
  have hj := continuousAt_joint_matchingHomotopyColumn ell ((h : ℂ) * Complex.I * Z)
    (spectralQ ell h b z) ρ hq (by simp) (by simpa using mul_ne_zero hh hZ)
  have hc : ContinuousAt (fun x : ℝ × ℂ => (x.1, spectralQ ell h b x.2)) (ρ, z) :=
    continuousAt_fst.prodMk (ContinuousAt.comp (f := Prod.snd)
      (g := spectralQ ell h b) (analyticAt_spectralQ ell h b z).continuousAt continuousAt_snd)
  exact ContinuousAt.comp
    (f := fun x : ℝ × ℂ => (x.1, spectralQ ell h b x.2))
    (g := fun x : ℝ × ℂ => matchingHomotopyColumn (ell + 5) 8
      ((h : ℂ) * Complex.I * Z) x.1 x.2) hj hc

theorem continuousAt_joint_spectralHomotopyDeterminant (ell : ℕ) (b Z ρ : ℝ) (z : ℂ)
    (hZ : Z ≠ 0) (hz : -(1 / 32 : ℝ) ≤ z.re) :
    ContinuousAt (fun x : ℝ × ℂ => spectralHomotopyDeterminant ell b Z x.1 x.2) (ρ, z) := by
  have hp := continuousAt_joint_spectralHomotopyColumn ell 1 b Z ρ z (by norm_num) hZ hz
  have hm := continuousAt_joint_spectralHomotopyColumn ell (-1) b Z ρ z (by norm_num) hZ hz
  have h := ((continuousAt_pi.mp hp 0).mul (continuousAt_pi.mp hm 1)).sub
    ((continuousAt_pi.mp hp 1).mul (continuousAt_pi.mp hm 0))
  unfold spectralHomotopyDeterminant
  convert! h using 1
  funext x
  simp only [matchingColumnDeterminant, Pi.mul_apply, Pi.sub_apply,
    Complex.ofReal_one, Complex.ofReal_neg, one_mul, neg_one_mul]

end DefocusingNLS

end OAI
