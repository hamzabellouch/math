import Mathlib

namespace OAI

universe u

noncomputable section
open scoped BigOperators
namespace Problem313

/-- Weighted finite Hölder inequality with conjugate exponents `4/3` and `4`.
Weights need not be normalized. -/
theorem weighted_holder_four_thirds {ι : Type u} [Fintype ι]
    (w v u : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    |∑ i, w i * v i * u i| ≤
      (∑ i, w i * |v i| ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) *
        (∑ i, w i * u i ^ 4) ^ (1 / 4 : ℝ) := by
  classical
  have hpq : Real.HolderConjugate (4 / 3 : ℝ) 4 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ
    (f := fun i => w i ^ (3 / 4 : ℝ) * |v i|)
    (g := fun i => w i ^ (1 / 4 : ℝ) * |u i|) hpq
    (fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (abs_nonneg _))
    (fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (abs_nonneg _))
  have hleft : (∑ i, (w i ^ (3 / 4 : ℝ) * |v i|) *
      (w i ^ (1 / 4 : ℝ) * |u i|)) = ∑ i, w i * |v i| * |u i| := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (w i ^ (3 / 4 : ℝ) * w i ^ (1 / 4 : ℝ)) * |v i| * |u i| := by ring
      _ = w i * |v i| * |u i| := by
        rw [← Real.rpow_add' (hw i) (by norm_num : (3 / 4 : ℝ) + 1 / 4 ≠ 0)]
        norm_num
  have hfirst : (∑ i, (w i ^ (3 / 4 : ℝ) * |v i|) ^ (4 / 3 : ℝ)) =
      ∑ i, w i * |v i| ^ (4 / 3 : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i) _) (abs_nonneg _),
      ← Real.rpow_mul (hw i)]
    norm_num
  have hsecond : (∑ i, (w i ^ (1 / 4 : ℝ) * |u i|) ^ (4 : ℝ)) =
      ∑ i, w i * u i ^ 4 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i) _) (abs_nonneg _),
      ← Real.rpow_mul (hw i)]
    have habs : |u i| ^ (4 : ℕ) = u i ^ 4 := by
      rcases le_total 0 (u i) with hi | hi
      · rw [abs_of_nonneg hi]
      · rw [abs_of_nonpos hi]
        ring
    norm_num [Real.rpow_natCast, habs]
  rw [hleft, hfirst, hsecond] at h
  norm_num at h
  refine (Finset.abs_sum_le_sum_abs (fun i => w i * v i * u i) Finset.univ).trans ?_
  simpa only [abs_mul, abs_of_nonneg (hw _)] using h

/-- The scalar cancellation behind the `L⁴` duality argument. -/
theorem projection_moment_bound {M V H A : ℝ}
    (hM : 0 ≤ M) (hV : 0 ≤ V) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hdual : M ≤ V ^ (3 / 4 : ℝ) * H ^ (1 / 4 : ℝ))
    (hfour : H ≤ A ^ 4 * M ^ 2) :
    M ≤ A ^ 2 * V ^ (3 / 2 : ℝ) := by
  have hroot : H ^ (1 / 4 : ℝ) ≤ A * M ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ (A ^ 4 * M ^ 2) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow hH hfour (by norm_num)
      _ = A * M ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (pow_nonneg hA _) (sq_nonneg M),
          ← Real.rpow_natCast_mul hA, ← Real.rpow_natCast_mul hM]
        norm_num
  have hv : 0 ≤ V ^ (3 / 4 : ℝ) := Real.rpow_nonneg hV _
  have hs : 0 ≤ M ^ (1 / 2 : ℝ) := Real.rpow_nonneg hM _
  have hs2 : (M ^ (1 / 2 : ℝ)) ^ 2 = M := by
    rw [← Real.rpow_mul_natCast hM]
    norm_num
  have hbound : M ≤ (A * V ^ (3 / 4 : ℝ)) * M ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ V ^ (3 / 4 : ℝ) * H ^ (1 / 4 : ℝ) := hdual
      _ ≤ V ^ (3 / 4 : ℝ) * (A * M ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hroot hv
      _ = _ := by ring
  have hsbound : M ^ (1 / 2 : ℝ) ≤ A * V ^ (3 / 4 : ℝ) := by
    nlinarith [mul_nonneg hA hv]
  have hsq := pow_le_pow_left₀ hs hsbound 2
  have hv2 : (V ^ (3 / 4 : ℝ)) ^ 2 = V ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hV]
    norm_num
  simpa only [hs2, mul_pow, hv2] using hsq

/-- A low-degree fourth-moment bound implies the dual projection estimate.
The hypothesis `hproj` is the usual orthogonal-projection identity
`⟨v,u⟩ = ⟨u,u⟩`; this formulation avoids choosing a normalized dual vector. -/
theorem weighted_projection_bound {ι : Type u} [Fintype ι]
    (w v u : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (A : ℝ) (hA : 0 ≤ A)
    (hproj : (∑ i, w i * v i * u i) = ∑ i, w i * u i ^ 2)
    (hfour : (∑ i, w i * u i ^ 4) ≤ A ^ 4 * (∑ i, w i * u i ^ 2) ^ 2) :
    (∑ i, w i * u i ^ 2) ≤
      A ^ 2 * (∑ i, w i * |v i| ^ (4 / 3 : ℝ)) ^ (3 / 2 : ℝ) := by
  have hM : 0 ≤ ∑ i, w i * u i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  have hV : 0 ≤ ∑ i, w i * |v i| ^ (4 / 3 : ℝ) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.rpow_nonneg (abs_nonneg _) _)
  have hH : 0 ≤ ∑ i, w i * u i ^ 4 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (by positivity)
  apply projection_moment_bound hM hV hH hA _ hfour
  have h := weighted_holder_four_thirds w v u hw
  simpa only [hproj, abs_of_nonneg hM] using h

/-- Dual projection estimate for functions taking their values in `{-1,0,1}`,
as Boolean coordinate differences do. -/
theorem weighted_projection_pivotal_bound {ι : Type u} [Fintype ι]
    (w v u : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hv : ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hproj : (∑ i, w i * v i * u i) = ∑ i, w i * u i ^ 2)
    (hfour : (∑ i, w i * u i ^ 4) ≤ A ^ 4 * (∑ i, w i * u i ^ 2) ^ 2) :
    (∑ i, w i * u i ^ 2) ≤
      A ^ 2 * (∑ i, if v i ≠ 0 then w i else 0) ^ (3 / 2 : ℝ) := by
  classical
  have hnorm : (∑ i, w i * |v i| ^ (4 / 3 : ℝ)) =
      ∑ i, if v i ≠ 0 then w i else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    rcases hv i with hi | hi | hi <;> simp [hi]
  simpa only [hnorm] using weighted_projection_bound w v u hw A hA hproj hfour

/-- The exponent form used for low-degree projections of Boolean derivatives. -/
theorem weighted_projection_noise_bound {ι : Type u} [Fintype ι]
    (w v u : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hv : ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (ρ d : ℝ) (hρ : 0 ≤ ρ)
    (hproj : (∑ i, w i * v i * u i) = ∑ i, w i * u i ^ 2)
    (hfour : (∑ i, w i * u i ^ 4) ≤
      ρ ^ (-4 * d) * (∑ i, w i * u i ^ 2) ^ 2) :
    (∑ i, w i * u i ^ 2) ≤
      ρ ^ (-2 * d) * (∑ i, if v i ≠ 0 then w i else 0) ^ (3 / 2 : ℝ) := by
  have hfourpow : (ρ ^ (-d)) ^ (4 : ℕ) = ρ ^ (-4 * d) := by
    rw [← Real.rpow_mul_natCast hρ]
    congr 1
    ring
  have htwopow : (ρ ^ (-d)) ^ (2 : ℕ) = ρ ^ (-2 * d) := by
    rw [← Real.rpow_mul_natCast hρ]
    congr 1
    ring
  have h := weighted_projection_pivotal_bound w v u hw hv (ρ ^ (-d))
    (Real.rpow_nonneg hρ _) hproj (by simpa only [hfourpow] using hfour)
  simpa only [htwopow] using h

end Problem313

end

end OAI
