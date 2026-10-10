import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialProfileDerivativeBounds

namespace OAI

/-! Every radial derivative of the matched profile is globally bounded.
The Cartesian symbol bound applies on both halves of the chosen unit ray. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialMatchedEvenProfile_iteratedDeriv_bounded (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (j : ℕ) :
    ∃ B : ℝ, 0≤B ∧ ∀ r, ‖iteratedDeriv j (radialMatchedEvenProfile n z) r‖≤B := by
  let e : E := (EuclideanSpace.basisFun (Fin 12) ℝ) 0
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight e
  have he : ‖e‖=1 := (EuclideanSpace.basisFun (Fin 12) ℝ).norm_eq_one 0
  have hL (r : ℝ) : L r=r • e := rfl
  have hQ := radialMatchedCartesian_contDiff n z hX hz
  have hQr := radialMatchedEvenProfile_contDiff n z hX hz
  have hj (r : ℝ) : iteratedDeriv j (radialMatchedEvenProfile n z) r =
      iteratedFDeriv ℝ j (radialMatchedCartesian n z) (L r) (fun _ => e) := by
    change iteratedDeriv j (radialMatchedCartesian n z ∘ L) r = _
    rw [iteratedDeriv,L.iteratedFDeriv_comp_right hQ r (by simp)]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,hL,one_smul]
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) 1) (hQr.continuous_iteratedDeriv j (by simp)).continuousOn
  obtain ⟨D,hD,hb⟩ := radialMatchedCartesian_symbol n z hX hz j
  have ha : 0<radialShootingA n := by
    unfold radialShootingA
    exact one_div_pos.mpr (mul_pos (by norm_num)
      (Nat.cast_pos.mpr (radialShootingInner_power_pos n (profileMatchingParameter z))))
  refine ⟨max (max C 0) D,(le_max_right C 0).trans (le_max_left _ _),?_⟩
  intro r
  by_cases hr : |r|≤1
  · exact (hC r (abs_le.mp hr)).trans ((le_max_left C 0).trans (le_max_left _ _))
  · have har : 1≤|r| := (lt_of_not_ge hr).le
    have hn : ‖L r‖=|r| := by rw [hL,norm_smul,Real.norm_eq_abs,he,mul_one]
    have hp : |r|^(-2*radialShootingA n-(j : ℝ))≤1 :=
      Real.rpow_le_one_of_one_le_of_nonpos har (by have hj0 : (0 : ℝ)≤j := Nat.cast_nonneg j; linarith)
    rw [hj]
    calc
      _ ≤ ‖iteratedFDeriv ℝ j (radialMatchedCartesian n z) (L r)‖ := by
        simpa only [he,Finset.prod_const_one,mul_one] using
          (iteratedFDeriv ℝ j (radialMatchedCartesian n z) (L r)).le_opNorm (fun _ => e)
      _ ≤ D*|r|^(-2*radialShootingA n-(j : ℝ)) := by
        simpa only [hn] using hb (L r) (by rwa [hn])
      _ ≤ D := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hD
      _ ≤ _ := le_max_right _ _

end DefocusingNLS

end OAI
