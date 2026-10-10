import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDerivativeBounded

namespace OAI

/-! The radial symbol estimate on both signed rays. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialMatchedEvenProfile_signed_symbol (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (j : ℕ) :
    ∃ D : ℝ, 0≤D ∧ ∀ r : ℝ, 1≤|r| →
      ‖iteratedDeriv j (radialMatchedEvenProfile n z) r‖ ≤
        D*|r|^(-2*radialShootingA n-(j : ℝ)) := by
  let e : E := (EuclideanSpace.basisFun (Fin 12) ℝ) 0
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight e
  have he : ‖e‖=1 := (EuclideanSpace.basisFun (Fin 12) ℝ).norm_eq_one 0
  have hL (r : ℝ) : L r=r • e := rfl
  have hQ := radialMatchedCartesian_contDiff n z hX hz
  obtain ⟨D,hD,hb⟩ := radialMatchedCartesian_symbol n z hX hz j
  refine ⟨D,hD,?_⟩
  intro r hr
  have hj : iteratedDeriv j (radialMatchedEvenProfile n z) r =
      iteratedFDeriv ℝ j (radialMatchedCartesian n z) (L r) (fun _ => e) := by
    change iteratedDeriv j (radialMatchedCartesian n z ∘ L) r = _
    rw [iteratedDeriv,L.iteratedFDeriv_comp_right hQ r (by simp)]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,hL,one_smul]
  have hn : ‖L r‖=|r| := by rw [hL,norm_smul,Real.norm_eq_abs,he,mul_one]
  rw [hj]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (radialMatchedCartesian n z) (L r)‖ := by
      simpa only [he,Finset.prod_const_one,mul_one] using
        (iteratedFDeriv ℝ j (radialMatchedCartesian n z) (L r)).le_opNorm (fun _ => e)
    _ ≤ _ := by simpa only [hn] using hb (L r) (by rwa [hn])

end DefocusingNLS

end OAI
