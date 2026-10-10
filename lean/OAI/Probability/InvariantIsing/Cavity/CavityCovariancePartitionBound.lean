import OAI.Probability.InvariantIsing.Cavity.CavityMatrixResolventBound

namespace OAI

/-! The common root, all positive levels, and the residual have total
covariance mass one. This estimate is independent of the number of steps. -/

noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_covariance_partition_bound {d n : ℕ}
    (T : ℝ → Matrix (Fin d) (Fin d) ℝ) (G : Matrix (Fin d) (Fin d) ℝ)
    (q x : Fin (n + 1) → ℝ) (b : Fin n → ℝ) {C : ℝ}
    (hT0 : T 0 = 0)
    (hT : ∀ u v, 0 ≤ u → u ≤ v → ‖T v - T u‖ ≤ C * (v - u))
    (hG : ‖G‖ ≤ C) (hq : Monotone q) (hq0 : 0 ≤ q 0)
    (hx : ∀ i, 0 ≤ x i)
    (hb : ∀ i, 0 < b i)
    (hgap : ∀ i, x i.castSucc - x i.succ = b i * (q i.succ - q i.castSucc))
    (hlast : x (Fin.last n) = 1 - q (Fin.last n)) :
    ‖q 0 • G + (∑ i : Fin n, (b i)⁻¹ • (T (x i.castSucc) - T (x i.succ))) +
      T (x (Fin.last n))‖ ≤ C := by
  have hqstep (i : Fin n) : 0 ≤ q i.succ - q i.castSucc :=
    sub_nonneg.mpr (hq (Fin.castSucc_le_succ i))
  have hstep (i : Fin n) :
      ‖(b i)⁻¹ • (T (x i.castSucc) - T (x i.succ))‖ ≤ C * (q i.succ - q i.castSucc) := by
    have horder : x i.succ ≤ x i.castSucc := by
      have := mul_nonneg (hb i).le (hqstep i)
      linarith [hgap i]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hb i))]
    calc
      _ ≤ (b i)⁻¹ * (C * (x i.castSucc - x i.succ)) :=
        mul_le_mul_of_nonneg_left (hT _ _ (hx i.succ) horder) (inv_pos.mpr (hb i)).le
      _ = C * (q i.succ - q i.castSucc) := by rw [hgap i]; field_simp [(hb i).ne']
  have hroot : ‖q 0 • G‖ ≤ C * q 0 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hq0]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hG hq0
  have htail : ‖T (x (Fin.last n))‖ ≤ C * (1 - q (Fin.last n)) := by
    simpa only [hT0, sub_zero, hlast] using hT 0 (x (Fin.last n)) le_rfl (hx _)
  have htel : (∑ i : Fin n, (q i.succ - q i.castSucc)) = q (Fin.last n) - q 0 := by
    rw [Finset.sum_sub_distrib]
    have h0 := Fin.sum_univ_succ q
    have h1 := Fin.sum_univ_castSucc q
    linarith
  calc
    _ ≤ ‖q 0 • G‖ + ‖∑ i : Fin n, (b i)⁻¹ • (T (x i.castSucc) - T (x i.succ))‖ +
        ‖T (x (Fin.last n))‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C * q 0 + (∑ i : Fin n, C * (q i.succ - q i.castSucc)) + C * (1 - q (Fin.last n)) := by
      exact add_le_add (add_le_add hroot ((norm_sum_le _ _).trans
        (Finset.sum_le_sum (fun i _ => hstep i)))) htail
    _ = C := by rw [← Finset.mul_sum, htel]; ring

theorem cavity_spectral_covariance_partition_bound {ι : Type*} [Fintype ι] {d n : ℕ}
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a)
    (q x : Fin (n + 1) → ℝ) (b : Fin n → ℝ)
    (hq : Monotone q) (hq0 : 0 ≤ q 0) (hx : ∀ i, 0 ≤ x i) (hx0 : 0 < x 0)
    (hb : ∀ i, 0 < b i)
    (hgap : ∀ i, x i.castSucc - x i.succ = b i * (q i.succ - q i.castSucc))
    (hlast : x (Fin.last n) = 1 - q (Fin.last n)) :
    let T := cavitySpectralMatrixPath ρ eig hρ hsum A hA
    ‖q 0 • cavitySpectralMatrixDensity ρ eig hρ hsum A hA (x 0) +
      (∑ i : Fin n, (b i)⁻¹ • (T (x i.castSucc) - T (x i.succ))) +
      T (x (Fin.last n))‖ ≤ (ρ a)⁻¹ := by
  intro T
  exact cavity_covariance_partition_bound T
    (cavitySpectralMatrixDensity ρ eig hρ hsum A hA (x 0)) q x b
    (cavitySpectralMatrixPath_zero ρ eig hρ hsum A hA)
    (fun _ _ hu huv => cavitySpectralMatrixPath_lipschitz ρ eig hρ hsum A hA a heig hu huv)
    (cavitySpectralMatrixDensity_norm_le ρ eig hρ hsum A hA a heig hx0)
    hq hq0 hx hb hgap hlast

end InvariantIsing

end

end OAI
