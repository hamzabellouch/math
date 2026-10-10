import OAI.Analysis.KadisonKastler.CompleteLinearLimits

namespace OAI

/-! # Elementary operations on complete bounds -/

namespace KadisonKastler

noncomputable section

variable {A B C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem matrix_map_add (F G : A →ₗ[ℂ] B) {p q : ℕ}
    (X : CStarMatrix (Fin p) (Fin q) A) :
    CStarMatrix.mapₗ (F + G) X = CStarMatrix.mapₗ F X + CStarMatrix.mapₗ G X := by
  ext i j
  rfl

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem matrix_map_zero {p q : ℕ} (X : CStarMatrix (Fin p) (Fin q) A) :
    CStarMatrix.mapₗ (0 : A →ₗ[ℂ] B) X = 0 := by
  ext i j
  rfl

theorem CompletelyBoundedBy.mono {F : A →ₗ[ℂ] B} {c d : ℝ}
    (hF : CompletelyBoundedBy F c) (hcd : c ≤ d) : CompletelyBoundedBy F d := by
  intro p q X
  exact (hF p q X).trans (mul_le_mul_of_nonneg_right hcd (norm_nonneg X))

theorem CompletelyBoundedBy.add {F G : A →ₗ[ℂ] B} {c d : ℝ}
    (hF : CompletelyBoundedBy F c) (hG : CompletelyBoundedBy G d) :
    CompletelyBoundedBy (F + G) (c + d) := by
  intro p q X
  rw [matrix_map_add, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hF p q X) (hG p q X))

theorem CompletelyBoundedBy.sub {F G : A →ₗ[ℂ] B} {c d : ℝ}
    (hF : CompletelyBoundedBy F c) (hG : CompletelyBoundedBy G d) :
    CompletelyBoundedBy (F - G) (c + d) := by
  intro p q X
  rw [matrix_map_sub, add_mul]
  exact (norm_sub_le _ _).trans (add_le_add (hF p q X) (hG p q X))

theorem completelyBoundedBy_id : CompletelyBoundedBy (LinearMap.id : A →ₗ[ℂ] A) 1 := by
  intro p q X
  rw [matrix_map_id, one_mul]

theorem CompletelyBoundedBy.comp {F : A →ₗ[ℂ] B} {G : B →ₗ[ℂ] C} {c d : ℝ}
    (hG : CompletelyBoundedBy G d) (hF : CompletelyBoundedBy F c) (hd : 0 ≤ d) :
    CompletelyBoundedBy (G.comp F) (d * c) := by
  intro p q X
  rw [matrix_map_comp, mul_assoc]
  exact (hG p q _).trans (mul_le_mul_of_nonneg_left (hF p q X) hd)

theorem CompletelyBoundedBy.opNorm_le {F : A →ₗ[ℂ] B} {c : ℝ}
    (hF : CompletelyBoundedBy F c) (hc : 0 ≤ c) :
    ‖hF.toContinuousLinearMap‖ ≤ c :=
  ContinuousLinearMap.opNorm_le_bound _ hc hF.apply_norm_le

end

end KadisonKastler

end OAI
