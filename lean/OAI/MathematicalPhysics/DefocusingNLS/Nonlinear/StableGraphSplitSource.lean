import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphWeightedSource

namespace OAI

/-! # Splitting a nonlinear endpoint remainder into graph coordinates

These operator estimates implement the two source terms in the forward and
backward graph equations.  The unstable coordinate is weighted by `K`; the
small linear defect and nonlinear remainder remain explicit quantities.
-/

namespace DefocusingNLS

variable {V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem stableGraph_split_source_lipschitz
    (S : V →L[ℝ] E) (P : E →L[ℝ] E) (π e : E →L[ℝ] F)
    (h : E → E) (J cP cπ τ κ K ρ R : ℝ)
    (hJ : 0 ≤ J) (hcP : 0 ≤ cP) (hcπ : 0 ≤ cπ) (hτ : 0 ≤ τ)
    (hκ : 0 ≤ κ) (hK : 0 ≤ K)
    (hS : ‖S‖ ≤ J) (hP : ‖P‖ ≤ cP) (hπ : ‖π‖ ≤ cπ) (he : ‖e‖ ≤ τ)
    (hball : J * ρ ≤ R)
    (hh : ∀ x y, ‖x‖ ≤ R → ‖y‖ ≤ R → ‖h x - h y‖ ≤ κ * ‖x - y‖)
    (x y : V) (hx : ‖x‖ ≤ ρ) (hy : ‖y‖ ≤ ρ) :
    ‖P (h (S x)) - P (h (S y))‖ ≤ cP * κ * J * ‖x - y‖ ∧
      ‖K • (e (S x) + π (h (S x))) - K • (e (S y) + π (h (S y)))‖ ≤
        K * (τ + cπ * κ) * J * ‖x - y‖ := by
  have hsx : ‖S x‖ ≤ R := ((S.le_opNorm x).trans
    (mul_le_mul hS hx (norm_nonneg _) hJ)).trans hball
  have hsy : ‖S y‖ ≤ R := ((S.le_opNorm y).trans
    (mul_le_mul hS hy (norm_nonneg _) hJ)).trans hball
  have hsdiff : ‖S x - S y‖ ≤ J * ‖x - y‖ := by
    rw [← map_sub]
    exact (S.le_opNorm _).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
  have hhdiff : ‖h (S x) - h (S y)‖ ≤ (κ * J) * ‖x - y‖ := by
    calc
      _ ≤ κ * ‖S x - S y‖ := hh _ _ hsx hsy
      _ ≤ κ * (J * ‖x - y‖) := mul_le_mul_of_nonneg_left hsdiff hκ
      _ = _ := by ring
  have hp : ‖P (h (S x)) - P (h (S y))‖ ≤ cP * κ * J * ‖x - y‖ := by
    rw [← map_sub]
    calc
      _ ≤ ‖P‖ * ‖h (S x) - h (S y)‖ := P.le_opNorm _
      _ ≤ cP * ((κ * J) * ‖x - y‖) :=
        mul_le_mul hP hhdiff (norm_nonneg _) hcP
      _ = _ := by ring
  have hediff : ‖e (S x) - e (S y)‖ ≤ (τ * J) * ‖x - y‖ := by
    rw [← map_sub]
    calc
      _ ≤ ‖e‖ * ‖S x - S y‖ := e.le_opNorm _
      _ ≤ τ * (J * ‖x - y‖) := mul_le_mul he hsdiff (norm_nonneg _) hτ
      _ = _ := by ring
  have hπdiff : ‖π (h (S x)) - π (h (S y))‖ ≤ (cπ * κ * J) * ‖x - y‖ := by
    rw [← map_sub]
    calc
      _ ≤ ‖π‖ * ‖h (S x) - h (S y)‖ := π.le_opNorm _
      _ ≤ cπ * ((κ * J) * ‖x - y‖) :=
        mul_le_mul hπ hhdiff (norm_nonneg _) hcπ
      _ = _ := by ring
  refine ⟨hp, ?_⟩
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hK]
  have hid : e (S x) + π (h (S x)) - (e (S y) + π (h (S y))) =
      (e (S x) - e (S y)) + (π (h (S x)) - π (h (S y))) := by abel
  rw [hid]
  calc
    _ ≤ K * (‖e (S x) - e (S y)‖ + ‖π (h (S x)) - π (h (S y))‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hK
    _ ≤ K * ((τ * J) * ‖x - y‖ + (cπ * κ * J) * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (add_le_add hediff hπdiff) hK
    _ = _ := by ring

theorem stableGraph_split_source_zero
    (S : V →L[ℝ] E) (P : E →L[ℝ] E) (π e : E →L[ℝ] F)
    (h : E → E) (cP cπ K ε : ℝ)
    (hcP : 0 ≤ cP) (hcπ : 0 ≤ cπ) (hK : 0 ≤ K)
    (hP : ‖P‖ ≤ cP) (hπ : ‖π‖ ≤ cπ) (hh : ‖h 0‖ ≤ ε) :
    ‖P (h (S 0))‖ ≤ cP * ε ∧
      ‖K • (e (S 0) + π (h (S 0)))‖ ≤ K * cπ * ε := by
  simp only [map_zero, zero_add]
  constructor
  · exact (P.le_opNorm _).trans (mul_le_mul hP hh (norm_nonneg _) hcP)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hK]
    exact ((mul_le_mul_of_nonneg_left
      ((π.le_opNorm _).trans (mul_le_mul hπ hh (norm_nonneg _) hcπ)) hK).trans_eq (by ring))

end DefocusingNLS

end OAI
