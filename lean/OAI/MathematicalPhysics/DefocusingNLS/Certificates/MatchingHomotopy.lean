import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HomotopyCone

namespace OAI

/-! # Holomorphic matching columns along the straight tail homotopy -/

open Matrix

namespace DefocusingNLS

theorem analyticAt_backwardMatrix_entry (M s q : ℂ) (n : ℕ) (i j : Fin 2) :
    AnalyticAt ℂ (fun z => backwardMatrix M s (z + n) i j) q := by
  fin_cases i <;> fin_cases j
  · change AnalyticAt ℂ (fun z : ℂ => z + n - M - s) q
    exact ((analyticAt_id.add analyticAt_const).sub analyticAt_const).sub analyticAt_const
  · change AnalyticAt ℂ (fun _ : ℂ => -s) q
    exact analyticAt_const
  · change AnalyticAt ℂ (fun z : ℂ => z + n) q
    exact analyticAt_id.add analyticAt_const
  · change AnalyticAt ℂ (fun z : ℂ => z + n) q
    exact analyticAt_id.add analyticAt_const

theorem analyticAt_backwardProduct_entry (M s q : ℂ) (K : ℕ) (i j : Fin 2) :
    AnalyticAt ℂ (fun z => backwardProduct M s z K i j) q := by
  induction K generalizing i j with
  | zero =>
      change AnalyticAt ℂ (fun _ : ℂ => (1 : Matrix (Fin 2) (Fin 2) ℂ) i j) q
      exact analyticAt_const
  | succ K ih =>
      simp only [backwardProduct, Matrix.mul_apply, Fin.sum_univ_two]
      exact ((ih i 0).mul (analyticAt_backwardMatrix_entry M s q K 0 j)).add
        ((ih i 1).mul (analyticAt_backwardMatrix_entry M s q K 1 j))

noncomputable def matchingHomotopyColumn (M K : ℕ) (s : ℂ) (ρ : ℝ) (q : ℂ) : Fin 2 → ℂ :=
  backwardProduct M s q K *ᵥ ![(ρ : ℂ) * slowTailRatio q (M + 1) K s, 1]

theorem analyticAt_matchingHomotopyColumn (ℓ K : ℕ) (s q : ℂ) (ρ : ℝ)
    (hK : 3 ≤ K) (hq : -(1 / 32 : ℝ) ≤ q.re - (ℓ : ℝ) / 2)
    (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    AnalyticAt ℂ (matchingHomotopyColumn (ℓ + 5) K s ρ) q := by
  have hr := analyticAt_slowTailRatio q ℓ K s hK hq hsre hsim
  apply AnalyticAt.pi
  intro i
  have he : ℓ + 5 + 1 = ℓ + 6 := by omega
  convert ((analyticAt_backwardProduct_entry (ℓ + 5) s q K i 0).mul
    ((show AnalyticAt ℂ (fun _ : ℂ => (ρ : ℂ)) q from analyticAt_const).mul hr)).add (analyticAt_backwardProduct_entry (ℓ + 5) s q K i 1) using 1
  funext z
  simp [matchingHomotopyColumn, he, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem matchingHomotopyColumn_zero (M K : ℕ) (s q : ℂ) :
    matchingHomotopyColumn M K s 0 q = backwardProduct M s q K *ᵥ ![0, 1] := by
  simp [matchingHomotopyColumn]

theorem matchingHomotopyColumn_one (M K : ℕ) (s q : ℂ)
    (hK : 0 < K) (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0)
    (hC : normalizedMatchingC q (M + 1) s K ≠ 0) :
    matchingHomotopyColumn M K s 1 q =
      (normalizedMatchingC q (M + 1) s K)⁻¹ • slowBoundaryColumn q (M + 1) s := by
  simpa only [matchingHomotopyColumn, Complex.ofReal_one, one_mul, slowTailRatio] using
    normalizedMatching_ratio_column q M K s hK hq hsre hsim hC

theorem matchingHomotopyColumn_one_ne_zero (ℓ K : ℕ) (s q : ℂ)
    (hK : 3 ≤ K) (hq : -(1 / 32 : ℝ) ≤ q.re - (ℓ : ℝ) / 2)
    (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    matchingHomotopyColumn (ℓ + 5) K s 1 q ≠ 0 := by
  have hq' : -1 < q.re := by linarith [Nat.cast_nonneg (α := ℝ) ℓ]
  have hC := (normalizedMatching_tail_disk (q.re - (ℓ : ℝ) / 2) ℓ K q s hq hK
    (by ring) hsre hsim).1
  have he : ℓ + 5 + 1 = ℓ + 6 := by omega
  rw [matchingHomotopyColumn_one (ℓ + 5) K s q (by omega) hq' hsre hsim (by simpa only [he] using hC)]
  exact smul_ne_zero (inv_ne_zero (by simpa only [he] using hC))
    (slowBoundaryColumn_ne_zero q (ℓ + 5 + 1) s hq' hsre hsim)

/-- The scalar identifying the endpoint with the actual column is holomorphic
and nonzero throughout the counting half-plane, including q=0. -/
theorem analyticAt_matchingTailScalar (ℓ K : ℕ) (s q : ℂ)
    (hK : 3 ≤ K) (hq : -(1 / 32 : ℝ) ≤ q.re - (ℓ : ℝ) / 2)
    (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    AnalyticAt ℂ (fun z => (normalizedMatchingC z (ℓ + 6) s K)⁻¹) q ∧
      (normalizedMatchingC q (ℓ + 6) s K)⁻¹ ≠ 0 := by
  have hq' : -1 < q.re := by linarith [Nat.cast_nonneg (α := ℝ) ℓ]
  have hC := (normalizedMatching_tail_disk (q.re - (ℓ : ℝ) / 2) ℓ K q s hq hK
    (by ring) hsre hsim).1
  exact ⟨((analyticOnNhd_normalizedMatchingC (ℓ + 6) K s hsre hsim) q hq').inv hC,
    inv_ne_zero hC⟩

noncomputable def matchingColumnDeterminant (u v : Fin 2 → ℂ) : ℂ := u 0 * v 1 - u 1 * v 0

theorem matchingColumnDeterminant_smul (a b : ℂ) (u v : Fin 2 → ℂ) :
    matchingColumnDeterminant (a • u) (b • v) = a * b * matchingColumnDeterminant u v := by
  simp only [matchingColumnDeterminant, Pi.smul_apply, smul_eq_mul]
  ring

theorem matchingHomotopy_endpoint_determinant (M K : ℕ) (s₁ s₂ q₁ q₂ : ℂ)
    (hK : 0 < K) (hq₁ : -1 < q₁.re) (hq₂ : -1 < q₂.re)
    (hs₁ : s₁.re = 0) (hs₂ : s₂.re = 0) (hi₁ : s₁.im ≠ 0) (hi₂ : s₂.im ≠ 0)
    (hC₁ : normalizedMatchingC q₁ (M + 1) s₁ K ≠ 0)
    (hC₂ : normalizedMatchingC q₂ (M + 1) s₂ K ≠ 0) :
    matchingColumnDeterminant (matchingHomotopyColumn M K s₁ 1 q₁)
        (matchingHomotopyColumn M K s₂ 1 q₂) = 0 ↔
      matchingColumnDeterminant (slowBoundaryColumn q₁ (M + 1) s₁)
        (slowBoundaryColumn q₂ (M + 1) s₂) = 0 := by
  rw [matchingHomotopyColumn_one M K s₁ q₁ hK hq₁ hs₁ hi₁ hC₁,
    matchingHomotopyColumn_one M K s₂ q₂ hK hq₂ hs₂ hi₂ hC₂,
    matchingColumnDeterminant_smul]
  exact mul_eq_zero.trans (or_iff_right (mul_ne_zero (inv_ne_zero hC₁) (inv_ne_zero hC₂)))

end DefocusingNLS

end OAI
