import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDilationContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLocalizationPhysical
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalInjective
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingBlowupObservation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCoordinateMap

namespace OAI

/-! # Strong continuity of the actual radius-dependent localization

Localization at radius L factors through the fixed radius-one localization,
the exact inverse weight transfer, and physical homogeneous dilation.
-/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

attribute [local irreducible] homogeneousLocalizationCLM homogeneousDilation expandingInverseTransfer

theorem homogeneousLocalization_dilation (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) (f : FourierL2) :
    homogeneousLocalizationCLM a k L ha ha1 hk hL χ f =
      ((L ^ (2 * a) : ℝ) : ℂ) • homogeneousDilation a k L ha ha1 hk hL
        (homogeneousLocalizationCLM a k 1 ha ha1 hk le_rfl χ
          (expandingInverseTransfer a k L ha hk hL f)) := by
  apply homogeneousPhysicalCLM_injective a k ha ha1 hk
  ext y
  rw [map_smul]
  change homogeneousPhysicalCLM a k ha ha1 hk
    (homogeneousLocalizationCLM a k L ha ha1 hk hL χ f) y =
      ((L ^ (2 * a) : ℝ) : ℂ) * homogeneousPhysicalCLM a k ha ha1 hk
        (homogeneousDilation a k L ha ha1 hk hL
          (homogeneousLocalizationCLM a k 1 ha ha1 hk le_rfl χ
            (expandingInverseTransfer a k L ha hk hL f))) y
  rw [homogeneousDilation_physical, homogeneousLocalization_physical,
    homogeneousLocalization_physical]
  simp only [expandingPhysicalLocalization, inv_one, one_smul]
  rw [expandingInverseTransfer_function a k L ha ha1 hk hL]
  have hc : L ^ (2 * a) * L ^ (-2 * a) = 1 := by
    rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hL)]
    simp
  rw [← mul_assoc, ← Complex.ofReal_mul, hc, Complex.ofReal_one, one_mul]

theorem continuous_homogeneousLocalization (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (χ : 𝓢(E, ℂ)) :
    Continuous (fun p : Radius × FourierL2 =>
      homogeneousLocalizationCLM a k p.1.1 ha ha1 hk p.1.2 χ p.2) := by
  have he : (fun p : Radius × FourierL2 =>
      homogeneousLocalizationCLM a k p.1.1 ha ha1 hk p.1.2 χ p.2) =
      (fun p : Radius × FourierL2 => ((p.1.1 ^ (2 * a) : ℝ) : ℂ) •
        homogeneousDilation a k p.1.1 ha ha1 hk p.1.2
          (homogeneousLocalizationCLM a k 1 ha ha1 hk le_rfl χ
            (expandingInverseTransfer a k p.1.1 ha hk p.1.2 p.2))) :=
    funext (fun p => homogeneousLocalization_dilation a k p.1.1 ha ha1 hk p.1.2 χ p.2)
  rw [he]
  have hi := ((continuous_expandingInverseTransfer a k ha hk).comp continuous_fst).clm_apply
    (continuous_snd : Continuous (fun p : Radius × FourierL2 => p.2))
  have hj := (homogeneousLocalizationCLM a k 1 ha ha1 hk le_rfl χ).continuous.comp hi
  have hd := (continuous_homogeneousDilation_uncurry a k ha ha1 hk).comp
    (continuous_fst.prodMk hj)
  exact (Complex.continuous_ofReal.comp
    ((continuous_subtype_val.comp continuous_fst).rpow_const
      (fun p => Or.inl (lt_of_lt_of_le zero_lt_one p.1.2).ne'))).smul hd

theorem continuous_expandingCoordinates_apply {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (π : HomogeneousY a k →L[ℝ] F) :
    Continuous (fun p : Radius × FourierL2 => expandingCoordinates a k ha ha1 hk χ π p.1 p.2) :=
  π.continuous.comp (continuous_homogeneousLocalization a k ha ha1 hk χ)

end DefocusingNLS

end OAI
