import OAI.Analysis.HyperbolicCones.MatrixPositive

namespace OAI

/-! Spectral identities for the inverse square root. -/

noncomputable section

open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix

namespace Paper256

theorem inverseSquareRoot_eq_cfc {n : ℕ} (H : Sym n) :
    inverseSquareRoot H = cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (H : Mat n ℝ) := by
  let hH : (H : Mat n ℝ).IsHermitian := H.property
  rw [hH.cfc_eq]
  simp [inverseSquareRoot, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Function.comp_def, Matrix.star_eq_conjTranspose]

theorem matrix_cfc_mul {n : ℕ} (H : Sym n) (f g : ℝ → ℝ) :
    cfc (fun x => f x * g x) (H : Mat n ℝ) =
      cfc f (H : Mat n ℝ) * cfc g (H : Mat n ℝ) :=
  cfc_mul f g _ (H.val.finite_real_spectrum.continuousOn f)
    (H.val.finite_real_spectrum.continuousOn g)

theorem inverseSquareRoot_isHermitian {n : ℕ} (H : Sym n) :
    (inverseSquareRoot H).IsHermitian := by
  rw [inverseSquareRoot_eq_cfc]
  exact IsSelfAdjoint.cfc

theorem inverseSquareRoot_transpose {n : ℕ} (H : Sym n) :
    (inverseSquareRoot H)ᵀ = inverseSquareRoot H :=
  Matrix.isHermitian_iff_isSymm.mp (inverseSquareRoot_isHermitian H)

theorem posDef_real_spectrum_positive {n : ℕ} {A : Mat n ℝ} (hA : A.PosDef)
    {x : ℝ} (hx : x ∈ spectrum ℝ A) : 0 < x := by
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hA.eigenvalues_pos i

theorem inverseSquareRoot_conjugate {n : ℕ} (H : Sym n) (hH : (H : Mat n ℝ).PosDef) :
    (inverseSquareRoot H)ᵀ * (H : Mat n ℝ) * inverseSquareRoot H = 1 := by
  rw [inverseSquareRoot_transpose, inverseSquareRoot_eq_cfc]
  let f : ℝ → ℝ := fun x => (Real.sqrt x)⁻¹
  have hid : cfc (fun x : ℝ => x) (H : Mat n ℝ) = (H : Mat n ℝ) :=
    cfc_id' ℝ (H : Mat n ℝ) H.property
  change cfc f (H : Mat n ℝ) * (H : Mat n ℝ) * cfc f (H : Mat n ℝ) = 1
  calc
    cfc f (H : Mat n ℝ) * (H : Mat n ℝ) * cfc f (H : Mat n ℝ) =
        cfc (fun x => f x * x * f x) (H : Mat n ℝ) := by
      rw [matrix_cfc_mul H (fun x => f x * x) f,
        matrix_cfc_mul H f (fun x => x)]
      rw [hid]
    _ = cfc (fun _ : ℝ => 1) (H : Mat n ℝ) := by
      apply cfc_congr
      intro x hx
      have hxpos := posDef_real_spectrum_positive hH hx
      have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hxpos).ne'
      dsimp [f]
      field_simp
      exact (Real.sq_sqrt hxpos.le).symm
    _ = 1 := cfc_const_one ℝ (H : Mat n ℝ) H.property

theorem inverseSquareRoot_isUnit {n : ℕ} (H : Sym n) (hH : (H : Mat n ℝ).PosDef) :
    IsUnit (inverseSquareRoot H) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hs
  have h := congrArg Matrix.det (inverseSquareRoot_conjugate H hH)
  simp [Matrix.det_mul, Matrix.det_transpose, hs] at h

theorem inverseSquareRoot_commute {n : ℕ} (H : Sym n) :
    Commute (inverseSquareRoot H) (H : Mat n ℝ) := by
  rw [inverseSquareRoot_eq_cfc]
  have hid : cfc (fun x : ℝ => x) (H : Mat n ℝ) = (H : Mat n ℝ) :=
    cfc_id' ℝ (H : Mat n ℝ) H.property
  simpa only [hid] using
    cfc_commute_cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (fun x => x) (H : Mat n ℝ)

theorem inverseSquareRoot_sq {n : ℕ} (H : Sym n) (hH : (H : Mat n ℝ).PosDef) :
    inverseSquareRoot H * inverseSquareRoot H = (H : Mat n ℝ)⁻¹ := by
  have h := inverseSquareRoot_conjugate H hH
  rw [inverseSquareRoot_transpose] at h
  have hi : (inverseSquareRoot H * inverseSquareRoot H) * (H : Mat n ℝ) = 1 := by
    calc
      _ = inverseSquareRoot H * (inverseSquareRoot H * (H : Mat n ℝ)) := mul_assoc _ _ _
      _ = inverseSquareRoot H * ((H : Mat n ℝ) * inverseSquareRoot H) := by
        rw [(inverseSquareRoot_commute H).eq]
      _ = 1 := by simpa only [mul_assoc] using h
  exact (Matrix.inv_eq_left_inv hi).symm

end Paper256

end

end OAI
