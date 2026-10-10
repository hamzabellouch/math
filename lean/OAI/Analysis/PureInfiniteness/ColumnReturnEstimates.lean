import OAI.Analysis.PureInfiniteness.RectangularReturnDefect

namespace OAI

/-! Quantitative commutator control for a finite return column. These estimates
use its square defect, not just centrality of the input map. -/

noncomputable section

namespace WeakPureInfiniteness

variable {A J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Fintype J]

lemma columnReturn_norm_le (G : CStarMatrix J (Fin 1) A) (hG : ‖G‖ ≤ 1)
    (X : CStarMatrix J J A) : ‖columnReturn G X‖ ≤ ‖X‖ := by
  calc
    _ ≤ ‖G.conjTranspose * X‖ * ‖G‖ := rectangular_norm_mul_le _ _
    _ ≤ (‖G.conjTranspose‖ * ‖X‖) * ‖G‖ :=
      mul_le_mul_of_nonneg_right (rectangular_norm_mul_le _ _) (norm_nonneg G)
    _ = (‖G‖ * ‖X‖) * ‖G‖ := by rw [rectangular_norm_conjTranspose]
    _ ≤ (1 * ‖X‖) * 1 := by gcongr
    _ = _ := by ring

omit [PartialOrder A] [StarOrderedRing A] in
lemma columnReturn_conjTranspose (G : CStarMatrix J (Fin 1) A)
    (X : CStarMatrix J J A) :
    (columnReturn G X).conjTranspose = columnReturn G X.conjTranspose := by
  simp only [columnReturn, rectangular_conjTranspose_mul,
    rectangular_conjTranspose_conjTranspose, rectangular_mul_assoc]

lemma columnReturn_commutator_le (G : CStarMatrix J (Fin 1) A) (hG : ‖G‖ ≤ 1)
    (X Y : CStarMatrix J J A) (hX : X.conjTranspose = X)
    (hY : Y.conjTranspose = Y) (hXY : X * Y = Y * X) :
    ‖columnReturn G X * columnReturn G Y - columnReturn G Y * columnReturn G X‖ ≤
      2 * Real.sqrt ‖columnReturn G (X * X) - columnReturn G X * columnReturn G X‖ * ‖Y‖ := by
  have hb := columnReturn_multiplicative_defect G hG X Y hX
  have he : (columnReturn G (X * Y) - columnReturn G X * columnReturn G Y).conjTranspose =
      columnReturn G (X * Y) - columnReturn G Y * columnReturn G X := by
    simp only [rectangular_star_sub, rectangular_conjTranspose_mul,
      columnReturn_conjTranspose, hX, hY, hXY]
  have hb' : ‖columnReturn G (X * Y) - columnReturn G Y * columnReturn G X‖ ≤
      Real.sqrt ‖columnReturn G (X * X) - columnReturn G X * columnReturn G X‖ * ‖Y‖ := by
    rw [← he, rectangular_norm_conjTranspose]
    exact hb
  calc
    _ = ‖(columnReturn G (X * Y) - columnReturn G Y * columnReturn G X) -
        (columnReturn G (X * Y) - columnReturn G X * columnReturn G Y)‖ := by congr 1; abel
    _ ≤ ‖columnReturn G (X * Y) - columnReturn G Y * columnReturn G X‖ +
        ‖columnReturn G (X * Y) - columnReturn G X * columnReturn G Y‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

lemma columnReturn_approximate_commutator_le (G : CStarMatrix J (Fin 1) A)
    (hG : ‖G‖ ≤ 1) (X Y : CStarMatrix J J A) (hX : X.conjTranspose = X)
    (hY : Y.conjTranspose = Y) (hXY : X * Y = Y * X)
    (a : CStarMatrix (Fin 1) (Fin 1) A) (ε : ℝ) (ha : ‖a - columnReturn G X‖ ≤ ε) :
    ‖a * columnReturn G Y - columnReturn G Y * a‖ ≤
      2 * ε * ‖Y‖ +
        2 * Real.sqrt ‖columnReturn G (X * X) - columnReturn G X * columnReturn G X‖ * ‖Y‖ := by
  have hb := columnReturn_commutator_le G hG X Y hX hY hXY
  have hYnorm := columnReturn_norm_le G hG Y
  have hleft : ‖(a - columnReturn G X) * columnReturn G Y‖ ≤ ε * ‖Y‖ :=
    (norm_mul_le _ _).trans (mul_le_mul ha hYnorm (norm_nonneg _) (le_trans (norm_nonneg _) ha))
  have hright : ‖columnReturn G Y * (a - columnReturn G X)‖ ≤ ε * ‖Y‖ := by
    calc
      _ ≤ ‖columnReturn G Y‖ * ‖a - columnReturn G X‖ := norm_mul_le _ _
      _ ≤ ‖Y‖ * ε := mul_le_mul hYnorm ha (norm_nonneg _) (norm_nonneg _)
      _ = _ := mul_comm _ _
  calc
    _ = ‖((a - columnReturn G X) * columnReturn G Y -
        columnReturn G Y * (a - columnReturn G X)) +
        (columnReturn G X * columnReturn G Y - columnReturn G Y * columnReturn G X)‖ := by
      congr 1
      noncomm_ring
    _ ≤ ‖(a - columnReturn G X) * columnReturn G Y -
        columnReturn G Y * (a - columnReturn G X)‖ +
        ‖columnReturn G X * columnReturn G Y - columnReturn G Y * columnReturn G X‖ := norm_add_le _ _
    _ ≤ (‖(a - columnReturn G X) * columnReturn G Y‖ +
        ‖columnReturn G Y * (a - columnReturn G X)‖) +
        ‖columnReturn G X * columnReturn G Y - columnReturn G Y * columnReturn G X‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ _ := by linarith

end WeakPureInfiniteness
namespace WeakPureInfiniteness

lemma norm_square_difference_le {B : Type*} [NormedRing B] (x y : B)
    (ε : ℝ) (hxy : ‖x - y‖ ≤ ε) :
    ‖x * x - y * y‖ ≤ ε * (2 * ‖y‖ + ε) := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hxy
  have hx : ‖x‖ ≤ ‖y‖ + ε := by
    have h := norm_le_norm_sub_add x y
    linarith
  have he : x * x - y * y = (x - y) * x + y * (x - y) := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(x - y) * x‖ + ‖y * (x - y)‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ * ‖x‖ + ‖y‖ * ‖x - y‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ε * (‖y‖ + ε) + ‖y‖ * ε := by gcongr
    _ = _ := by ring

variable {A J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Fintype J]

lemma columnReturn_schwarz_defect_le_of_moments (G : CStarMatrix J (Fin 1) A)
    (X : CStarMatrix J J A) (a : CStarMatrix (Fin 1) (Fin 1) A) (ε q : ℝ)
    (hfirst : ‖columnReturn G X - a‖ ≤ ε)
    (hsecond : ‖columnReturn G (X * X) - a * a‖ ≤ q) :
    ‖columnReturn G (X * X) - columnReturn G X * columnReturn G X‖ ≤
      q + ε * (2 * ‖a‖ + ε) := by
  calc
    _ ≤ ‖columnReturn G (X * X) - a * a‖ +
        ‖a * a - columnReturn G X * columnReturn G X‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖columnReturn G (X * X) - a * a‖ +
        ‖columnReturn G X * columnReturn G X - a * a‖ := by rw [norm_sub_rev (a * a)]
    _ ≤ _ := add_le_add hsecond (norm_square_difference_le _ _ ε hfirst)

end WeakPureInfiniteness

end

end OAI
