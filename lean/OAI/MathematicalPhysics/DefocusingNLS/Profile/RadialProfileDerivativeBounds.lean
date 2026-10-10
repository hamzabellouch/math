import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedEvenProfile
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! Radial top-derivative bounds for the actual smooth profile, obtained by
restricting its already proved Cartesian symbol estimates to a unit ray. -/

open Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialMatchedEvenProfile_derivative_bound (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (j : ℕ) :
    ∃ D : ℝ, 0≤D ∧ ∀ r : ℝ, 1≤r →
      ‖iteratedDeriv j (radialMatchedEvenProfile n z) r‖ ≤
        D*r^(-2*radialShootingA n-(j : ℝ)) := by
  let e : E := (EuclideanSpace.basisFun (Fin 12) ℝ) 0
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight e
  have hL (r : ℝ) : L r=r • e := rfl
  have he : ‖e‖=1 := (EuclideanSpace.basisFun (Fin 12) ℝ).norm_eq_one 0
  have heq : radialMatchedEvenProfile n z=radialMatchedCartesian n z ∘ L := rfl
  have hQ := radialMatchedCartesian_contDiff n z hX hz
  obtain ⟨D,hD,hb⟩ := radialMatchedCartesian_symbol n z hX hz j
  refine ⟨D,hD,?_⟩
  intro r hr
  have hLj : iteratedDeriv j (radialMatchedEvenProfile n z) r =
      iteratedFDeriv ℝ j (radialMatchedCartesian n z) (L r) (fun _ => e) := by
    rw [heq,iteratedDeriv,L.iteratedFDeriv_comp_right hQ r (by simp)]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,hL,one_smul]
  have hnorm : ‖L r‖=r := by rw [hL,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith),he,mul_one]
  rw [hLj]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (radialMatchedCartesian n z) (L r)‖ := by
      simpa only [he,Finset.prod_const_one,mul_one] using
        (iteratedFDeriv ℝ j (radialMatchedCartesian n z) (L r)).le_opNorm (fun _ => e)
    _ ≤ _ := by simpa only [hnorm] using hb (L r) (by rwa [hnorm])

theorem radialMatchedEvenProfile_top_integrable (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (N : ℕ) (hN : 7≤N) :
    IntegrableOn (fun r : ℝ => r^11*‖iteratedDeriv N (radialMatchedEvenProfile n z) r‖^2)
      (Ioi 0) := by
  let Q := radialMatchedEvenProfile n z
  let s : ℝ := -2*radialShootingA n-(N : ℝ)
  have hQ := radialMatchedEvenProfile_contDiff n z hX hz
  have hC : Continuous (fun r : ℝ => r^11*‖iteratedDeriv N Q r‖^2) :=
    (continuous_id.pow 11).mul (((hQ.continuous_iteratedDeriv N (by simp)).norm).pow 2)
  have ha : 0<radialShootingA n := by
    unfold radialShootingA
    exact one_div_pos.mpr (mul_pos (by norm_num)
      (Nat.cast_pos.mpr (radialShootingInner_power_pos n (profileMatchingParameter z))))
  have hs : 11+2*s < -1 := by
    have hNr : (7 : ℝ)≤N := by exact_mod_cast hN
    dsimp [s]
    linarith
  obtain ⟨D,hD,hb⟩ := radialMatchedEvenProfile_derivative_bound n z hX hz N
  have hi := (integrableOn_Ioi_rpow_of_lt hs (by norm_num : (0 : ℝ)<1)).const_mul (D^2)
  have ht : IntegrableOn (fun r : ℝ => r^11*‖iteratedDeriv N Q r‖^2) (Ioi 1) := by
    apply hi.mono' hC.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0<r := lt_trans zero_lt_one hr
    have hpow : r^(11+2*s)=r^11*(r^s)^2 := by
      rw [Real.rpow_add hr0,show (2 : ℝ)*s=s*2 by ring,Real.rpow_mul hr0.le]
      simpa only [Nat.cast_ofNat] using congrArg₂ (fun x y : ℝ => x*y)
        (Real.rpow_natCast r 11) (Real.rpow_natCast (r^s) 2)
    have hsq := pow_le_pow_left₀ (norm_nonneg (iteratedDeriv N Q r)) (hb r hr.le) 2
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),hpow]
    calc
      _ ≤ r^11*(D*r^s)^2 := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := by ring
  have hnear : IntegrableOn (fun r : ℝ => r^11*‖iteratedDeriv N Q r‖^2) (Icc 0 1) :=
    hC.continuousOn.integrableOn_Icc
  apply (hnear.union ht).mono_set
  intro r hr
  by_cases h : r≤1
  · exact Or.inl ⟨hr.le,h⟩
  · exact Or.inr (lt_of_not_ge h)

theorem radialMatchedEvenProfile_bounded (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) :
    ∃ B : ℝ, 0≤B ∧ ∀ r, ‖radialMatchedEvenProfile n z r‖≤B := by
  have hQ := radialMatchedEvenProfile_contDiff n z hX hz
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) 1) hQ.continuous.continuousOn
  obtain ⟨D,hD,hb⟩ := radialMatchedEvenProfile_derivative_bound n z hX hz 0
  have ha : 0<radialShootingA n := by
    unfold radialShootingA
    exact one_div_pos.mpr (mul_pos (by norm_num)
      (Nat.cast_pos.mpr (radialShootingInner_power_pos n (profileMatchingParameter z))))
  refine ⟨max (max C 0) D,(le_max_right C 0).trans (le_max_left _ _),?_⟩
  intro r
  by_cases hr : |r|≤1
  · exact (hC r (abs_le.mp hr)).trans ((le_max_left C 0).trans (le_max_left _ _))
  · have har : 1≤|r| := (lt_of_not_ge hr).le
    have h := hb |r| har
    simp only [iteratedDeriv_zero,Nat.cast_zero,sub_zero] at h
    have hp : |r|^(-2*radialShootingA n)≤1 :=
      Real.rpow_le_one_of_one_le_of_nonpos har (by linarith)
    have he : radialMatchedEvenProfile n z r=radialMatchedEvenProfile n z |r| := by
      simp only [radialMatchedEvenProfile_eq,abs_abs]
    rw [he]
    exact (h.trans ((mul_le_mul_of_nonneg_left hp hD).trans_eq (mul_one D))).trans
      (le_max_right _ _)

end DefocusingNLS

end OAI
