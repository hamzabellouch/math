import OAI.Analysis.Mahler.ShellRegularity
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

/-- Ordered coordinate basis for dx_0 wedge ... wedge dx_n. -/
def coordinateBasis (n : ℕ) (i : Fin n) : Fin n → ℝ := Pi.single i 1

/-- Ball Stokes for alternating differential forms. The
boundary is written as explicit oriented hemisphere-coordinate integrals. -/
theorem integral_extDeriv_coordBall {n : ℕ} (R : ℝ)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : Differentiable ℝ ω)
    (hD : ∀ i : Fin (n+1), Continuous (fun x =>
      fderiv ℝ (fun z => ω z (i.removeNth (coordinateBasis (n+1)))) x (coordinateBasis (n+1) i))) :
    (∫ x in coordBall (n+1) R, extDeriv ω x (coordinateBasis (n+1))) =
      ∑ i : Fin (n+1), (-1 : ℝ)^i.val *
        ∫ y in coordBall n R,
          ω (i.insertNth (chord R y) y) (i.removeNth (coordinateBasis (n+1))) -
          ω (i.insertNth (-chord R y) y) (i.removeNth (coordinateBasis (n+1))) := by
  have he (x : Fin (n+1) → ℝ) := extDeriv_apply (hω x) (coordinateBasis (n+1))
  simp_rw [he, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [integral_finsetSum _ (fun i _ => (integrableOn_coordBall (hD i) R).const_mul _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul]
  congr 1
  exact integral_partial_coordBall i R _ (hω.continuousAlternatingMap_apply_const _) (hD i)

/-- Punctured-ball Stokes for actual differential forms, with no regularity
assumption in the interior of the removed inner ball. -/
theorem integral_extDeriv_coordAnnulus {n : ℕ} {a R : ℝ} (haR : a^2 ≤ R^2)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ∀ x ∈ closedShell (n+1) a R, DifferentiableAt ℝ ω x)
    (hD : ∀ i : Fin (n+1), ContinuousOn (fun x =>
      fderiv ℝ (fun z => ω z (i.removeNth (coordinateBasis (n+1)))) x (coordinateBasis (n+1) i))
      (closedShell (n+1) a R)) :
    (∫ x in coordAnnulus (n+1) a R, extDeriv ω x (coordinateBasis (n+1))) =
      (∑ i : Fin (n+1), (-1 : ℝ)^i.val *
        ∫ y in coordBall n R,
          ω (i.insertNth (chord R y) y) (i.removeNth (coordinateBasis (n+1))) -
          ω (i.insertNth (-chord R y) y) (i.removeNth (coordinateBasis (n+1)))) -
      ∑ i : Fin (n+1), (-1 : ℝ)^i.val *
        ∫ y in coordBall n a,
          ω (i.insertNth (chord a y) y) (i.removeNth (coordinateBasis (n+1))) -
          ω (i.insertNth (-chord a y) y) (i.removeNth (coordinateBasis (n+1))) := by
  have he : (∫ x in coordAnnulus (n+1) a R, extDeriv ω x (coordinateBasis (n+1))) =
      ∫ x in coordAnnulus (n+1) a R, ∑ i : Fin (n+1), (-1 : ℝ)^i.val *
        fderiv ℝ (fun z => ω z (i.removeNth (coordinateBasis (n+1)))) x (coordinateBasis (n+1) i) := by
    apply setIntegral_congr_fun ((measurableSet_coordBall _ _).diff (measurableSet_coordBall _ _))
    intro x hx
    simpa only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] using
      extDeriv_apply (hω x (coordAnnulus_subset_shell _ _ _ hx)) (coordinateBasis (n+1))
  rw [he, integral_finsetSum _ (fun i _ => (integrableOn_shell_annulus (hD i)).const_mul _),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [coordinateBasis] at *
  rw [integral_const_mul, integral_partial_annulus_of_C1 i haR _
    (fun x hx => (hω x hx).continuousAlternatingMap_apply_const _) (hD i), mul_sub]

end MahlerStokes

end

end OAI
