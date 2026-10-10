import OAI.Combinatorics.ContingencyTables.Dense.DenseCoefficients
import OAI.Combinatorics.ContingencyTables.Dense.DenseScales

namespace OAI

/-!
# Regularity of the dense sampler's actual penalty

The natural margins, maximum pivots, integer quotient widths, and actual
parameters A=d⁴, B=d⁸ determine the penalty. Its regularity and scaled
change bounds follow from the normalized affine coefficients.
-/

namespace ContingencyTables.DenseAffine

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def denseWidth (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ) (i : I) (j : J) : ℝ :=
  ((min (R (some i)) (P (some j)) / d ^ 8 : ℕ) : ℝ)

noncomputable def densePenalty (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ) :
    (I × J → ℝ) → ℝ :=
  AffinePenalty.penalty
    (fun g => entryOffset (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g /
      cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
    (fun g p => entryCoeff (denseWidth R P d) g p /
      cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
    ((d : ℝ) / (d : ℝ) ^ 8)

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
private theorem dense_cellScale_pos (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (g : Option I × Option J) :
    0 < cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g := by
  change 0 < min (R g.1 : ℝ) (P g.2 : ℝ)
  apply lt_min
  · exact_mod_cast (lt_of_lt_of_le (pow_pos (show 0 < d by omega) _) (hR g.1))
  · exact_mod_cast (lt_of_lt_of_le (pow_pos (show 0 < d by omega) _) (hP g.2))

omit [Fintype I] [Fintype J] in
theorem dense_normalized_coeff_bound (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (g : Option I × Option J) (p : I × J) :
    |entryCoeff (denseWidth R P d) g p /
      cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g| ≤ 1 / (d : ℝ) ^ 8 := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  apply normalized_coeff_bound _ _ _ _ (by positivity)
    (fun i => by exact_mod_cast hRmax i) (fun j => by exact_mod_cast hPmax j)
    (fun i j => Nat.cast_nonneg _)
    (fun i j => ?_) (dense_cellScale_pos R P d hd hR hP) g p
  have hmin : d ^ 12 ≤ min (R (some i)) (P (some j)) := le_min (hR _) (hP _)
  simpa only [denseWidth, cellScale, Nat.cast_min] using
    (dense_width_bounds d _ hd hmin).2

theorem densePenalty_continuous (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ) :
    Continuous (densePenalty R P d) := AffinePenalty.penalty_continuous _ _ _

theorem densePenalty_convex (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (K : Set (I × J → ℝ)) (hK : Convex ℝ K) : ConvexOn ℝ K (densePenalty R P d) :=
  AffinePenalty.penalty_convex _ _ _ K hK

/-- A coordinate displacement at most `r` changes the actual scaled
penalty A*p by at most `r`. In particular this is at most one in a bin
and at most two in the cut-face tubes. -/
theorem densePenalty_scaled_change (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (x y : I × J → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hxy : ∀ p, |x p - y p| ≤ r) :
    |(d : ℝ) ^ 4 * densePenalty R P d x - (d : ℝ) ^ 4 * densePenalty R P d y| ≤ r := by
  have hbase := AffinePenalty.penalty_change
    (fun g => entryOffset (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g /
      cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
    (fun g p => entryCoeff (denseWidth R P d) g p /
      cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
    ((d : ℝ) / (d : ℝ) ^ 8) x y (1 / (d : ℝ) ^ 8) r (by positivity) hr
    (dense_normalized_coeff_bound R P d hd hR hP hRmax hPmax) hxy
  have hcard : (Fintype.card (I × J) : ℝ) ≤ d := by exact_mod_cast hfree
  have hscale : (d : ℝ) ^ 4 * Fintype.card (I × J) / (d : ℝ) ^ 8 ≤ 1 := by
    calc
      _ ≤ (d : ℝ) ^ 4 * d / (d : ℝ) ^ 8 := by gcongr
      _ ≤ 1 := dense_exponent_change_scale d hd
  calc
    _ = (d : ℝ) ^ 4 * |densePenalty R P d x - densePenalty R P d y| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 4)]
    _ ≤ (d : ℝ) ^ 4 * (Fintype.card (I × J) * (1 / (d : ℝ) ^ 8) * r) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = ((d : ℝ) ^ 4 * Fintype.card (I × J) / (d : ℝ) ^ 8) * r := by ring
    _ ≤ r := by simpa using mul_le_mul_of_nonneg_right hscale hr

end ContingencyTables.DenseAffine

end OAI
