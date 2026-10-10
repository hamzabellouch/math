import OAI.Analysis.KadisonSimilarity.OperatorAlgebra

namespace OAI

/-!
# The three-block free-compression norm estimate

The reduced-word construction in `lem:free-compression` supplies a projection
`p` with a zero fourth block, a small overlap with the corner `e`, and `L²`
bounds on the two off-diagonal blocks. These bounds imply the compressed
operator norm estimate.
-/

noncomputable section

namespace KadisonSimilarity

variable {R : Type*} [NormedRing R]

/-- The creation, annihilation, and diagonal blocks exhaust an operator when
its fourth block is zero. -/
theorem three_block_decomposition (p T : R) (hzero : (1 - p) * T * (1 - p) = 0) :
    T = p * T * (1 - p) + (1 - p) * T * p + p * T * p := by
  have hid : p * T * (1 - p) + (1 - p) * T * p + p * T * p =
      T - (1 - p) * T * (1 - p) := by noncomm_ring
  rw [hid, hzero, sub_zero]

/-- Abstract form of the free-compression bound. The parameter `b₂` is the
tracial `L²` norm in the intended application. -/
theorem norm_free_compression_le (e p T : R) (hp : p * p = p)
    {u b₂ : ℝ} (hu : 0 ≤ u) (hb₂ : 0 ≤ b₂)
    (he : ‖e‖ ≤ 1) (hep : ‖e * p‖ ≤ Real.sqrt u) (hpe : ‖p * e‖ ≤ Real.sqrt u)
    (hzero : (1 - p) * T * (1 - p) = 0)
    (hcreate : ‖p * T * (1 - p)‖ ≤ b₂)
    (hannihilate : ‖(1 - p) * T * p‖ ≤ b₂) :
    ‖e * T * e‖ ≤ 2 * Real.sqrt u * b₂ + u * ‖T‖ := by
  have hleft : ‖e * (p * T * (1 - p)) * e‖ ≤ Real.sqrt u * b₂ := by
    have hid : e * (p * T * (1 - p)) * e =
        (e * p) * (p * T * (1 - p)) * e := by
      symm
      calc
        (e * p) * (p * T * (1 - p)) * e = e * (p * p) * T * (1 - p) * e := by
          noncomm_ring
        _ = e * (p * T * (1 - p)) * e := by rw [hp]; noncomm_ring
    rw [hid]
    calc
      _ ≤ (‖e * p‖ * ‖p * T * (1 - p)‖) * ‖e‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (Real.sqrt u * b₂) * 1 := by gcongr
      _ = Real.sqrt u * b₂ := mul_one _
  have hright : ‖e * ((1 - p) * T * p) * e‖ ≤ Real.sqrt u * b₂ := by
    have hid : e * ((1 - p) * T * p) * e =
        e * ((1 - p) * T * p) * (p * e) := by
      symm
      calc
        e * ((1 - p) * T * p) * (p * e) = e * ((1 - p) * T * (p * p)) * e := by
          noncomm_ring
        _ = e * ((1 - p) * T * p) * e := by rw [hp]
    rw [hid]
    calc
      _ ≤ (‖e‖ * ‖(1 - p) * T * p‖) * ‖p * e‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1 * b₂) * Real.sqrt u := by gcongr
      _ = Real.sqrt u * b₂ := by ring
  have hdiag : ‖e * (p * T * p) * e‖ ≤ u * ‖T‖ := by
    have hid : e * (p * T * p) * e = (e * p) * T * (p * e) := by
      simp only [mul_assoc]
    rw [hid]
    calc
      _ ≤ (‖e * p‖ * ‖T‖) * ‖p * e‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (Real.sqrt u * ‖T‖) * Real.sqrt u := by gcongr
      _ = (Real.sqrt u) ^ 2 * ‖T‖ := by ring
      _ = u * ‖T‖ := by rw [Real.sq_sqrt hu]
  have hsplit : e * T * e = e * (p * T * (1 - p)) * e +
      e * ((1 - p) * T * p) * e + e * (p * T * p) * e := by
    conv_lhs => rw [three_block_decomposition p T hzero]
    simp only [mul_add, add_mul]
  rw [hsplit]
  calc
    _ ≤ (‖e * (p * T * (1 - p)) * e‖ + ‖e * ((1 - p) * T * p) * e‖) +
        ‖e * (p * T * p) * e‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (Real.sqrt u * b₂ + Real.sqrt u * b₂) + u * ‖T‖ :=
      add_le_add (add_le_add hleft hright) hdiag
    _ = 2 * Real.sqrt u * b₂ + u * ‖T‖ := by ring

/-- For the narrow arc used in the paper, the compression has norm at most
three times the corner trace. -/
theorem norm_narrow_arc_compression_le (e p T : R) (hp : p * p = p)
    {u b₂ : ℝ} (hu : 0 ≤ u) (hb₂ : 0 ≤ b₂)
    (he : ‖e‖ ≤ 1) (hep : ‖e * p‖ ≤ Real.sqrt u) (hpe : ‖p * e‖ ≤ Real.sqrt u)
    (hzero : (1 - p) * T * (1 - p) = 0)
    (hcreate : ‖p * T * (1 - p)‖ ≤ b₂)
    (hannihilate : ‖(1 - p) * T * p‖ ≤ b₂)
    (h₂ : b₂ ^ 2 ≤ u) (hnorm : ‖T‖ ≤ 1) : ‖e * T * e‖ ≤ 3 * u := by
  have hs := Real.sqrt_nonneg u
  have hsq := Real.sq_sqrt hu
  have hb : b₂ ≤ Real.sqrt u := by nlinarith
  calc
    ‖e * T * e‖ ≤ 2 * Real.sqrt u * b₂ + u * ‖T‖ :=
      norm_free_compression_le e p T hp hu hb₂ he hep hpe hzero hcreate hannihilate
    _ ≤ 2 * Real.sqrt u * Real.sqrt u + u * 1 := by gcongr
    _ = 3 * u := by nlinarith

end KadisonSimilarity

end

end OAI
