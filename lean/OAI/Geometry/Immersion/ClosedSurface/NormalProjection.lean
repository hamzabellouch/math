import OAI.Geometry.Immersion.ClosedSurface.RealModes

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.NormalFrame

lemma gramDet_change_basis (X Y : RVec 4) (a b c d : ℝ) :
    NormalFrame.gramDet (a • X + b • Y) (c • X + d • Y) =
      (a*d-b*c)^2 * NormalFrame.gramDet X Y := by
  simp only [NormalFrame.gramDet, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, dotProduct_comm Y X]
  ring

lemma realNormalPart_linear (X Y : RVec 4) :
    IsLinearMap ℝ (realNormalPart X Y) := by
  constructor
  · intro W Z
    ext i
    simp [realNormalPart, dotProduct_add, Pi.add_apply]
    ring
  · intro s W
    ext i
    simp [realNormalPart, dotProduct_smul, Pi.smul_apply]
    ring

lemma realNormalPart_of_perp (X Y W : RVec 4) (hX : X ⬝ᵥ W = 0) (hY : Y ⬝ᵥ W = 0) :
    realNormalPart X Y W = W := by simp [realNormalPart, hX, hY]

lemma realNormalPart_self_left (X Y : RVec 4) (hD : NormalFrame.gramDet X Y ≠ 0) :
    realNormalPart X Y X = 0 := by
  have hxy : Y ⬝ᵥ X = X ⬝ᵥ Y := dotProduct_comm _ _
  have ha : ((Y ⬝ᵥ Y) * (X ⬝ᵥ X) - (X ⬝ᵥ Y) * (Y ⬝ᵥ X)) /
      NormalFrame.gramDet X Y = 1 := by
    rw [hxy]
    convert div_self hD using 1
    unfold NormalFrame.gramDet
    ring
  have hb : (X ⬝ᵥ X) * (Y ⬝ᵥ X) - (X ⬝ᵥ Y) * (X ⬝ᵥ X) = 0 := by rw [hxy]; ring
  simp [realNormalPart, ha, hb]

lemma realNormalPart_self_right (X Y : RVec 4) (hD : NormalFrame.gramDet X Y ≠ 0) :
    realNormalPart X Y Y = 0 := by
  have ha : (Y ⬝ᵥ Y) * (X ⬝ᵥ Y) - (X ⬝ᵥ Y) * (Y ⬝ᵥ Y) = 0 := by ring
  have hb : ((X ⬝ᵥ X) * (Y ⬝ᵥ Y) - (X ⬝ᵥ Y) * (X ⬝ᵥ Y)) /
      NormalFrame.gramDet X Y = 1 := by
    convert div_self hD using 1
    unfold NormalFrame.gramDet
    ring
  simp [realNormalPart, ha, hb]



lemma realNormalPart_change_basis (X Y W : RVec 4) (a b c d : ℝ)
    (hD : NormalFrame.gramDet X Y ≠ 0) (hdet : a*d-b*c ≠ 0) :
    realNormalPart (a • X + b • Y) (c • X + d • Y) W = realNormalPart X Y W := by
  let Z := realNormalPart (a • X + b • Y) (c • X + d • Y) W
  have hD' : NormalFrame.gramDet (a • X + b • Y) (c • X + d • Y) ≠ 0 := by
    rw [gramDet_change_basis]
    exact mul_ne_zero (pow_ne_zero 2 hdet) hD
  obtain ⟨hAZ, hBZ⟩ := realNormalPart_perp (a • X + b • Y) (c • X + d • Y) W hD'
  change (a • X + b • Y) ⬝ᵥ Z = 0 at hAZ
  change (c • X + d • Y) ⬝ᵥ Z = 0 at hBZ
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at hAZ hBZ
  have hXZ : X ⬝ᵥ Z = 0 := by
    apply (mul_eq_zero.mp (show (a*d-b*c) * (X ⬝ᵥ Z) = 0 by
      linear_combination d * hAZ - b * hBZ)).resolve_left hdet
  have hYZ : Y ⬝ᵥ Z = 0 := by
    apply (mul_eq_zero.mp (show (a*d-b*c) * (Y ⬝ᵥ Z) = 0 by
      linear_combination a * hBZ - c * hAZ)).resolve_left hdet
  have hlin := realNormalPart_linear X Y
  have hA : realNormalPart X Y (a • X + b • Y) = 0 := by
    rw [hlin.map_add, hlin.map_smul, hlin.map_smul, realNormalPart_self_left _ _ hD,
      realNormalPart_self_right _ _ hD, smul_zero, smul_zero, add_zero]
  have hB : realNormalPart X Y (c • X + d • Y) = 0 := by
    rw [hlin.map_add, hlin.map_smul, hlin.map_smul, realNormalPart_self_left _ _ hD,
      realNormalPart_self_right _ _ hD, smul_zero, smul_zero, add_zero]
  have he : realNormalPart X Y Z = realNormalPart X Y W := by
    dsimp [Z]
    conv_lhs => arg 3; unfold realNormalPart
    rw [hlin.map_sub, hlin.map_sub, hlin.map_smul, hlin.map_smul, hA, hB]
    simp
  exact (realNormalPart_of_perp X Y Z hXZ hYZ).symm.trans he

end ClosedSurfaceR4.RealModes

end

end OAI
