import OAI.Analysis.Mahler.FormStokes
import OAI.Analysis.Mahler.CoordinateSphere

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

/-- Exact closed-ball puncture. The sign of the inner boundary is negative,
while its displayed flux is outward from the inner ball itself. -/
theorem integral_extDeriv_punctured_ball {n : ℕ} {a R : ℝ} (haR : a^2 ≤ R^2)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ∀ x ∈ closedShell (n+1) a R, DifferentiableAt ℝ ω x)
    (hD : ∀ i : Fin (n+1), ContinuousOn (fun x =>
      fderiv ℝ (fun z => ω z (i.removeNth (coordinateBasis (n+1)))) x (coordinateBasis (n+1) i))
      (closedShell (n+1) a R)) :
    (∫ x in coordBall (n+1) R \ coordClosedBall (n+1) a, extDeriv ω x (coordinateBasis (n+1))) =
      (∑ i : Fin (n+1), (-1 : ℝ)^i.val *
        ∫ y in coordBall n R,
          ω (i.insertNth (chord R y) y) (i.removeNth (coordinateBasis (n+1))) -
          ω (i.insertNth (-chord R y) y) (i.removeNth (coordinateBasis (n+1)))) -
      ∑ i : Fin (n+1), (-1 : ℝ)^i.val *
        ∫ y in coordBall n a,
          ω (i.insertNth (chord a y) y) (i.removeNth (coordinateBasis (n+1))) -
          ω (i.insertNth (-chord a y) y) (i.removeNth (coordinateBasis (n+1))) := by
  calc
    _ = ∫ x in coordAnnulus (n+1) a R, extDeriv ω x (coordinateBasis (n+1)) := by
      exact (setIntegral_congr_set (f := fun x => extDeriv ω x (coordinateBasis (n+1)))
        (coordAnnulus_ae_eq_puncture (n := n) a R)).symm
    _ = _ := integral_extDeriv_coordAnnulus haR ω hω hD

lemma radiusSq_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ radiusSq x :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

lemma coordBall_zero (n : ℕ) : coordBall n 0 = ∅ := by
  ext x
  simp only [coordBall, mem_ofPred_eq, zero_pow (by decide : 2 ≠ 0), mem_empty_iff_false, iff_false]
  exact not_lt_of_ge (radiusSq_nonneg x)

lemma closedShell_zero (n : ℕ) (R : ℝ) : closedShell n 0 R = coordClosedBall n R := by
  ext x
  simp [closedShell, coordClosedBall, radiusSq_nonneg]

/-- Ball Stokes needs C1 regularity only near the closed ball, not globally. -/
theorem integral_extDeriv_ball_of_C1 {n : ℕ} (R : ℝ)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ∀ x ∈ coordClosedBall (n+1) R, DifferentiableAt ℝ ω x)
    (hD : ∀ i : Fin (n+1), ContinuousOn (fun x =>
      fderiv ℝ (fun z => ω z (i.removeNth (coordinateBasis (n+1)))) x (coordinateBasis (n+1) i)) (coordClosedBall (n+1) R)) :
    (∫ x in coordBall (n+1) R, extDeriv ω x (coordinateBasis (n+1))) =
      ∑ i : Fin (n+1), (-1 : ℝ)^i.val *
        ∫ y in coordBall n R,
          ω (i.insertNth (chord R y) y) (i.removeNth (coordinateBasis (n+1))) -
          ω (i.insertNth (-chord R y) y) (i.removeNth (coordinateBasis (n+1))) := by
  have hw : ∀ x ∈ closedShell (n+1) 0 R, DifferentiableAt ℝ ω x := by
    simpa only [closedShell_zero] using hω
  have hd : ∀ i : Fin (n+1), ContinuousOn (fun x =>
      fderiv ℝ (fun z => ω z (i.removeNth (coordinateBasis (n+1)))) x (coordinateBasis (n+1) i))
      (closedShell (n+1) 0 R) := by
    simpa only [closedShell_zero] using hD
  simpa [coordAnnulus, coordBall_zero] using
    integral_extDeriv_coordAnnulus (a := 0) (R := R) (by simpa using sq_nonneg R) ω hw hd

end MahlerStokes

end

end OAI
