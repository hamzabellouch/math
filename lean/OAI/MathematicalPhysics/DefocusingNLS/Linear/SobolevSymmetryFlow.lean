import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevPhase
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.MaximalStrongSolution

namespace OAI

/-! # Spatial and phase covariance of the maximal physical flow -/

open Set

namespace DefocusingNLS

private def mapInteractionPatch (k : ℝ) (hk : 6 < k) (m : ℕ)
    (L : FourierL2 →L[ℝ] FourierL2)
    (hL : ∀ t f, schrodingerInteractionField k hk m t (L f) =
      L (schrodingerInteractionField k hk m t f))
    {f : FourierL2} (P : SobolevInteractionPatch k hk m f) :
    SobolevInteractionPatch k hk m (L f) where
  left := P.left
  right := P.right
  left_neg := P.left_neg
  right_pos := P.right_pos
  curve := fun t => L (P.curve t)
  initial := by rw [P.initial]
  solves t ht := by
    rw [hL]
    exact L.hasFDerivAt.comp_hasDerivAt t (P.solves t ht)

private theorem maximalInteractionFlow_map (k : ℝ) (hk : 6 < k) (m : ℕ)
    (L : FourierL2 →L[ℝ] FourierL2)
    (hL : ∀ t f, schrodingerInteractionField k hk m t (L f) =
      L (schrodingerInteractionField k hk m t f))
    (f : FourierL2) (t : ℝ) (ht : t ∈ maximalSobolevInteractionDomain k hk m f) :
    t ∈ maximalSobolevInteractionDomain k hk m (L f) ∧
      maximalSobolevInteractionFlow k hk m (L f) t =
        L (maximalSobolevInteractionFlow k hk m f t) := by
  obtain ⟨P, hP⟩ := mem_iUnion.mp ht
  let Q := mapInteractionPatch k hk m L hL P
  have hQ : t ∈ Ioo Q.left Q.right := hP
  refine ⟨mem_iUnion.mpr ⟨Q, hQ⟩, ?_⟩
  rw [maximalSobolevInteractionFlow_eq_patch Q hQ,
    maximalSobolevInteractionFlow_eq_patch P hP]
  rfl

theorem schrodingerInteractionField_translation (k : ℝ) (hk : 6 < k) (m : ℕ)
    (x : SchrodingerTorus) (t : ℝ) (f : FourierL2) :
    schrodingerInteractionField k hk m t (sobolevTranslation x f) =
      sobolevTranslation x (schrodingerInteractionField k hk m t f) := by
  simp only [schrodingerInteractionField, schrodingerFlow_translation,
    sobolevOddPower_translation, map_smul]

theorem maximalSobolevInteractionDomain_translation (k : ℝ) (hk : 6 < k) (m : ℕ)
    (x : SchrodingerTorus) (f : FourierL2) :
    maximalSobolevInteractionDomain k hk m (sobolevTranslation x f) =
      maximalSobolevInteractionDomain k hk m f := by
  ext t
  constructor
  · intro ht
    have h := (maximalInteractionFlow_map k hk m
      ((sobolevTranslation (-x)).toContinuousLinearMap.restrictScalars ℝ)
      (schrodingerInteractionField_translation k hk m (-x)) (sobolevTranslation x f) t ht).1
    change t ∈ maximalSobolevInteractionDomain k hk m
      (sobolevTranslation (-x) (sobolevTranslation x f)) at h
    simpa only [← sobolevTranslation_add, neg_add_cancel, sobolevTranslation_zero] using h
  · intro ht
    exact (maximalInteractionFlow_map k hk m
      ((sobolevTranslation x).toContinuousLinearMap.restrictScalars ℝ)
      (schrodingerInteractionField_translation k hk m x) f t ht).1

/-- Translating the initial datum translates the maximal physical solution at every time. -/
theorem maximalSobolevSchrodingerFlow_translation (k : ℝ) (hk : 6 < k) (m : ℕ)
    (x : SchrodingerTorus) (f : FourierL2) (t : ℝ)
    (ht : t ∈ maximalSobolevInteractionDomain k hk m f) :
    maximalSobolevSchrodingerFlow k hk m (sobolevTranslation x f) t =
      sobolevTranslation x (maximalSobolevSchrodingerFlow k hk m f t) := by
  have h := (maximalInteractionFlow_map k hk m
    ((sobolevTranslation x).toContinuousLinearMap.restrictScalars ℝ)
    (schrodingerInteractionField_translation k hk m x) f t ht).2
  change maximalSobolevInteractionFlow k hk m (sobolevTranslation x f) t =
    sobolevTranslation x (maximalSobolevInteractionFlow k hk m f t) at h
  change schrodingerFlow t (maximalSobolevInteractionFlow k hk m (sobolevTranslation x f) t) = _
  rw [h, schrodingerFlow_translation]
  rfl

theorem schrodingerInteractionField_phase (k : ℝ) (hk : 6 < k) (m : ℕ)
    (c : Circle) (t : ℝ) (f : FourierL2) :
    schrodingerInteractionField k hk m t (sobolevPhase c f) =
      sobolevPhase c (schrodingerInteractionField k hk m t f) := by
  simp only [schrodingerInteractionField, sobolevPhase_apply, map_smul]
  rw [← sobolevPhase_apply, sobolevOddPower_phase, sobolevPhase_apply, map_smul]

@[simp] theorem sobolevPhase_inv_apply (c : Circle) (f : FourierL2) :
    sobolevPhase c⁻¹ (sobolevPhase c f) = f := by
  simp only [sobolevPhase_apply, smul_smul, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one,
    one_smul]

theorem maximalSobolevInteractionDomain_phase (k : ℝ) (hk : 6 < k) (m : ℕ)
    (c : Circle) (f : FourierL2) :
    maximalSobolevInteractionDomain k hk m (sobolevPhase c f) =
      maximalSobolevInteractionDomain k hk m f := by
  ext t
  constructor
  · intro ht
    have h := (maximalInteractionFlow_map k hk m
      ((sobolevPhase c⁻¹).toContinuousLinearMap.restrictScalars ℝ)
      (schrodingerInteractionField_phase k hk m c⁻¹) (sobolevPhase c f) t ht).1
    change t ∈ maximalSobolevInteractionDomain k hk m (sobolevPhase c⁻¹ (sobolevPhase c f)) at h
    simpa only [sobolevPhase_inv_apply] using h
  · intro ht
    exact (maximalInteractionFlow_map k hk m
      ((sobolevPhase c).toContinuousLinearMap.restrictScalars ℝ)
      (schrodingerInteractionField_phase k hk m c) f t ht).1

/-- Unit phase commutes with the maximal physical flow and preserves its lifespan. -/
theorem maximalSobolevSchrodingerFlow_phase (k : ℝ) (hk : 6 < k) (m : ℕ)
    (c : Circle) (f : FourierL2) (t : ℝ)
    (ht : t ∈ maximalSobolevInteractionDomain k hk m f) :
    maximalSobolevSchrodingerFlow k hk m (sobolevPhase c f) t =
      sobolevPhase c (maximalSobolevSchrodingerFlow k hk m f t) := by
  have h := (maximalInteractionFlow_map k hk m
    ((sobolevPhase c).toContinuousLinearMap.restrictScalars ℝ)
    (schrodingerInteractionField_phase k hk m c) f t ht).2
  change maximalSobolevInteractionFlow k hk m (sobolevPhase c f) t =
    sobolevPhase c (maximalSobolevInteractionFlow k hk m f t) at h
  change schrodingerFlow t (maximalSobolevInteractionFlow k hk m (sobolevPhase c f) t) = _
  rw [h]
  exact (schrodingerFlow t).map_smul _ _

end DefocusingNLS

end OAI
