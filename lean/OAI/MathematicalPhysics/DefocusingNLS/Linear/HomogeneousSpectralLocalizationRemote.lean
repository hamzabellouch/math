import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralLocalizationGeometry
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingMatrix

namespace OAI

/-! The two remote leading eigenvectors have a uniform gap.  The scalar
`c` is the actual combination `h * omega / r² + ell * (ell + 10) / r⁴`. -/

namespace DefocusingNLS

noncomputable def homogeneousSpectralLocalizationRemoteRoot (h j c : ℝ) : ℂ :=
  (h : ℂ) * Complex.I * ((-1 / 4 + j * Real.sqrt (1 / 16 - c) : ℝ) : ℂ)

noncomputable def homogeneousSpectralLocalizationRemoteField
    (h c : ℝ) (v : ℂ × ℂ) : ℂ × ℂ :=
  (v.2, (c : ℂ) * v.1 - (h : ℂ) * Complex.I / 2 * v.2)

theorem homogeneousSpectralLocalizationRemoteRoot_equation
    (h j c : ℝ) (hh : h^2 = 1) (hj : j^2 = 1) (hc : c ≤ 1 / 16) :
    homogeneousSpectralLocalizationRemoteRoot h j c ^ 2 +
        (h : ℂ) * Complex.I / 2 * homogeneousSpectralLocalizationRemoteRoot h j c -
        (c : ℂ) = 0 := by
  have hhC : (h : ℂ)^2 = 1 := by exact_mod_cast hh
  have hjC : (j : ℂ)^2 = 1 := by exact_mod_cast hj
  have hs : (Real.sqrt (1 / 16 - c) : ℂ)^2 = (1 / 16 : ℂ) - (c : ℂ) := by
    have he := congrArg Complex.ofReal (Real.sq_sqrt (sub_nonneg.mpr hc))
    push_cast at he
    exact he
  dsimp only [homogeneousSpectralLocalizationRemoteRoot]
  push_cast
  ring_nf
  simp only [Complex.I_sq, hhC, hjC, hs]
  ring

theorem homogeneousSpectralLocalizationRemoteField_eigenvector
    (h j c : ℝ) (hh : h^2 = 1) (hj : j^2 = 1) (hc : c ≤ 1 / 16) :
    homogeneousSpectralLocalizationRemoteField h c
      (1, homogeneousSpectralLocalizationRemoteRoot h j c) =
      homogeneousSpectralLocalizationRemoteRoot h j c •
        (1, homogeneousSpectralLocalizationRemoteRoot h j c) := by
  have he := homogeneousSpectralLocalizationRemoteRoot_equation h j c hh hj hc
  apply Prod.ext
  · simp only [homogeneousSpectralLocalizationRemoteField, Prod.smul_fst, smul_eq_mul, mul_one]
  · dsimp only [homogeneousSpectralLocalizationRemoteField, Prod.smul_snd, smul_eq_mul]
    linear_combination -he

theorem homogeneousSpectralLocalizationRemoteRoot_gap
    (h c : ℝ) (hh : h^2 = 1) :
    ‖homogeneousSpectralLocalizationRemoteRoot h 1 c -
      homogeneousSpectralLocalizationRemoteRoot h (-1) c‖ =
      2 * Real.sqrt (1 / 16 - c) := by
  have habs : |h| = 1 := by nlinarith [sq_abs h, abs_nonneg h]
  have he : homogeneousSpectralLocalizationRemoteRoot h 1 c -
      homogeneousSpectralLocalizationRemoteRoot h (-1) c =
      (2 : ℂ) * (h : ℂ) * Complex.I * (Real.sqrt (1 / 16 - c) : ℂ) := by
    dsimp only [homogeneousSpectralLocalizationRemoteRoot]
    push_cast
    ring
  rw [he, norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    habs, abs_of_nonneg (Real.sqrt_nonneg _), mul_one]

theorem homogeneousSpectralLocalizationRemoteRoot_uniform
    (h c : ℝ) (hh : h^2 = 1) (hc : |c| ≤ 1 / 32) :
    1 / 4 ≤ ‖homogeneousSpectralLocalizationRemoteRoot h 1 c -
      homogeneousSpectralLocalizationRemoteRoot h (-1) c‖ ∧
    homogeneousSpectralLocalizationRemoteRoot h 1 c ≠
      homogeneousSpectralLocalizationRemoteRoot h (-1) c := by
  have hcu : c ≤ 1 / 32 := (abs_le.mp hc).2
  have hd : 0 ≤ 1 / 16 - c := by linarith
  have hs := Real.sq_sqrt hd
  have hs0 := Real.sqrt_nonneg (1 / 16 - c)
  have hgap := homogeneousSpectralLocalizationRemoteRoot_gap h c hh
  have hb : 1 / 4 ≤ ‖homogeneousSpectralLocalizationRemoteRoot h 1 c -
      homogeneousSpectralLocalizationRemoteRoot h (-1) c‖ := by
    rw [hgap]
    nlinarith
  refine ⟨hb, ?_⟩
  intro heq
  rw [heq, sub_self, norm_zero] at hb
  norm_num at hb

theorem homogeneousSpectralLocalizationRemoteRoot_norm
    (h j c : ℝ) (hh : h^2 = 1) (hj : j^2 = 1) (hc : |c| ≤ 1 / 32) :
    ‖homogeneousSpectralLocalizationRemoteRoot h j c‖ ≤ 1 := by
  have habs : |h| = 1 := by nlinarith [sq_abs h, abs_nonneg h]
  have jabs : |j| = 1 := by nlinarith [sq_abs j, abs_nonneg j]
  have hcl := (abs_le.mp hc).1
  have hcu := (abs_le.mp hc).2
  have hd : 0 ≤ 1 / 16 - c := by linarith
  have hs := Real.sq_sqrt hd
  have hs0 := Real.sqrt_nonneg (1 / 16 - c)
  have hs1 : Real.sqrt (1 / 16 - c) ≤ 1 / 2 := by nlinarith
  have ha : |(-1 / 4 : ℝ) + j * Real.sqrt (1 / 16 - c)| ≤
      1 / 4 + Real.sqrt (1 / 16 - c) := by
    calc
      _ ≤ |(-1 / 4 : ℝ)| + |j * Real.sqrt (1 / 16 - c)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, jabs, abs_of_nonneg hs0]; norm_num
  simp only [homogeneousSpectralLocalizationRemoteRoot, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, habs, mul_one, one_mul]
  linarith

theorem homogeneousSpectralLocalizationRemoteFrame_bounds
    (h c : ℝ) (hh : h^2 = 1) (hc : |c| ≤ 1 / 32) :
    let u : ℂ × ℂ := (1, homogeneousSpectralLocalizationRemoteRoot h 1 c)
    let v : ℂ × ℂ := (1, homogeneousSpectralLocalizationRemoteRoot h (-1) c)
    spectralValueDet u v ≠ 0 ∧ ‖spectralTwoColumns u v‖ ≤ 2 ∧
      ‖spectralValueInverse u v‖ ≤ 8 := by
  intro u v
  have hp := homogeneousSpectralLocalizationRemoteRoot_norm h 1 c hh (by norm_num) hc
  have hm := homogeneousSpectralLocalizationRemoteRoot_norm h (-1) c hh (by norm_num) hc
  have hgap := (homogeneousSpectralLocalizationRemoteRoot_uniform h c hh hc).1
  have hdet : 1 / 4 ≤ ‖spectralValueDet u v‖ := by
    simpa only [spectralValueDet, u, v, one_mul, mul_one, norm_sub_rev] using hgap
  have hdet0 : 0 < ‖spectralValueDet u v‖ := by linarith
  have hu : ‖u‖ ≤ 1 := by simpa only [u, Prod.norm_def, norm_one, max_le_iff, le_refl, true_and] using hp
  have hv : ‖v‖ ≤ 1 := by simpa only [v, Prod.norm_def, norm_one, max_le_iff, le_refl, true_and] using hm
  have hcol := homogeneousTwoColumns_norm u v
  refine ⟨norm_pos_iff.mp hdet0, by linarith, ?_⟩
  have hfirst : ‖(v.2, -u.2)‖ ≤ 1 := by
    simpa only [u, v, Prod.norm_def, norm_neg, max_le_iff] using And.intro hm hp
  have hsecond : ‖(-v.1, u.1)‖ ≤ 1 := by simp only [u, v, Prod.norm_def, norm_neg, norm_one, max_self, le_refl]
  have hc2 : ‖spectralTwoColumns (v.2, -u.2) (-v.1, u.1)‖ ≤ 2 :=
    (homogeneousTwoColumns_norm _ _).trans (by linarith)
  have hinv : ‖spectralValueDet u v‖⁻¹ ≤ 4 :=
    (inv_le_iff_one_le_mul₀ hdet0).mpr (by linarith)
  rw [spectralValueInverse, norm_smul, norm_inv]
  exact (mul_le_mul hinv hc2 (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem homogeneousSpectralLocalizationRemote_coefficient
    (ell : ℕ) (h omega S r : ℝ) (hh : |h| ≤ 1) (homega : 0 ≤ omega)
    (hS : (ell : ℝ) + 1 ≤ S) (hωS : omega ≤ S)
    (hr : 0 < r) (hrS : 256 * S ≤ r^2) :
    |h * omega / r^2 + (ell : ℝ) * (ell + 10) / r^4| ≤ 1 / 32 := by
  have hell : 0 ≤ (ell : ℝ) := Nat.cast_nonneg ell
  have hS0 : 0 ≤ S := by linarith
  have hr2 : 0 < r^2 := sq_pos_of_pos hr
  have hr4 : 0 < r^4 := pow_pos hr 4
  have hSsq : S^2 ≤ (r^2 / 256)^2 :=
    (sq_le_sq₀ hS0 (by positivity)).mpr (by linarith)
  have hη : (ell : ℝ) * (ell + 10) ≤ 16 * S^2 := by
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ (ell : ℝ) + 1) hS0).mpr hS
    nlinarith
  have hηr : (ell : ℝ) * (ell + 10) / r^4 ≤ 1 / 256 :=
    (div_le_iff₀ hr4).mpr (by nlinarith)
  have hωr : omega / r^2 ≤ 1 / 256 :=
    (div_le_iff₀ hr2).mpr (by linarith)
  have hhω : |h * omega| ≤ omega := by
    rw [abs_mul, abs_of_nonneg homega]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh homega
  have hhωr : |h * omega / r^2| ≤ 1 / 256 := by
    rw [abs_div, abs_of_pos hr2]
    exact (div_le_div_of_nonneg_right hhω hr2.le).trans hωr
  have hη0 : 0 ≤ (ell : ℝ) * (ell + 10) / r^4 := by positivity
  calc
    _ ≤ |h * omega / r^2| + |(ell : ℝ) * (ell + 10) / r^4| := abs_add_le _ _
    _ ≤ 1 / 256 + 1 / 256 := add_le_add hhωr (by rwa [abs_of_nonneg hη0])
    _ ≤ 1 / 32 := by norm_num

theorem homogeneousSpectralLocalizationRemote_actual_gap
    (ell : ℕ) (h omega S r : ℝ) (hh : h^2 = 1) (homega : 0 ≤ omega)
    (hS : (ell : ℝ) + 1 ≤ S) (hωS : omega ≤ S)
    (hr : 0 < r) (hrS : 256 * S ≤ r^2) :
    1 / 4 ≤ ‖homogeneousSpectralLocalizationRemoteRoot h 1
      (h * omega / r^2 + (ell : ℝ) * (ell + 10) / r^4) -
      homogeneousSpectralLocalizationRemoteRoot h (-1)
      (h * omega / r^2 + (ell : ℝ) * (ell + 10) / r^4)‖ := by
  have habs : |h| ≤ 1 := by nlinarith [sq_abs h, abs_nonneg h]
  exact (homogeneousSpectralLocalizationRemoteRoot_uniform h _ hh
    (homogeneousSpectralLocalizationRemote_coefficient ell h omega S r habs
      homega hS hωS hr hrS)).1

end DefocusingNLS

end OAI
