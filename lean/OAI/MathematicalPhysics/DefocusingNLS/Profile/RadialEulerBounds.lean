import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialEulerJet
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSignedSymbol

namespace OAI

/-! The time generator preserves every radial symbol order. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedEuler_signed_symbol (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (c : ℂ) (j : ℕ) :
    ∃ D : ℝ, 0≤D ∧ ∀ r : ℝ, 1≤(abs r) →
      ‖iteratedDeriv j (radialAffineEuler c (radialMatchedEvenProfile n z)) r‖ ≤
        D*(abs r)^(-2*radialShootingA n-(j : ℝ)) := by
  let Q := radialMatchedEvenProfile n z
  obtain ⟨D0,hD0,hb0⟩ := radialMatchedEvenProfile_signed_symbol n z hX hz j
  obtain ⟨D1,hD1,hb1⟩ := radialMatchedEvenProfile_signed_symbol n z hX hz (j+1)
  refine ⟨‖c+(j : ℂ)/2‖*D0+D1/2,by positivity,?_⟩
  intro r hr
  have hr0 : 0 < (abs r) := by linarith
  have hp : (abs r)*(abs r)^(-2*radialShootingA n-((j+1 : ℕ) : ℝ))=
      (abs r)^(-2*radialShootingA n-(j : ℝ)) := by
    calc
      _ = (abs r)^(1 : ℝ)*(abs r)^(-2*radialShootingA n-((j+1 : ℕ) : ℝ)) := by
        rw [Real.rpow_one]
      _ = (abs r)^(1+(-2*radialShootingA n-((j+1 : ℕ) : ℝ))) :=
        (Real.rpow_add hr0 _ _).symm
      _ = _ := by congr 1; push_cast; ring
  rw [radialAffineEuler_iteratedDeriv c Q (radialMatchedEvenProfile_contDiff n z hX hz),
    radialAffineEuler,← iteratedDeriv_succ]
  calc
    _ ≤ ‖(c+(j : ℂ)/2)*iteratedDeriv j Q r‖+
        ‖(r : ℂ)/2*iteratedDeriv (j+1) Q r‖ := norm_add_le _ _
    _ = ‖c+(j : ℂ)/2‖*‖iteratedDeriv j Q r‖+
        ((abs r)/2)*‖iteratedDeriv (j+1) Q r‖ := by
      rw [norm_mul,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs]
      norm_num
    _ ≤ ‖c+(j : ℂ)/2‖*(D0*(abs r)^(-2*radialShootingA n-(j : ℝ)))+
        ((abs r)/2)*(D1*(abs r)^(-2*radialShootingA n-((j+1 : ℕ) : ℝ))) :=
      add_le_add (mul_le_mul_of_nonneg_left (hb0 r hr) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hb1 r hr) (by positivity))
    _ = ‖c+(j : ℂ)/2‖*D0*(abs r)^(-2*radialShootingA n-(j : ℝ))+
        (D1/2)*((abs r)*(abs r)^(-2*radialShootingA n-((j+1 : ℕ) : ℝ))) := by ring
    _ = _ := by rw [hp]; ring

end DefocusingNLS

end OAI
