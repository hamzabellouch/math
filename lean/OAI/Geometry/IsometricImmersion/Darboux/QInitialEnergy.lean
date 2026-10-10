import OAI.Geometry.IsometricImmersion.Darboux.QFirstJetEnergy

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology Interval NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

def initialCutEnergyBudget (width M : ℝ) (A : ℝ≥0) : ℝ≥0 :=
  ⟨Real.sqrt (width * (1 + M) / 2) * (A : ℝ), mul_nonneg (Real.sqrt_nonneg _) A.2⟩

theorem initial_energy_bound_of_cut_jets
    {z S : Coord → ℝ} {U : Set Coord} {left right theta M : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hS : ContDiffOn ℝ ∞ S U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlr : left ≤ right) (hM : 0 ≤ M)
    (hSupper : ∀ x ∈ Icc left right, S (coordinatePoint x theta) ≤ M)
    (ell : ℕ) (A : ℝ≥0)
    (hcut : ∀ ds : List (Fin 2), ds.length ≤ ell + 1 → ∀ x ∈ Icc left right,
      |iteratedCoordPartial ds z (coordinatePoint x theta)| ≤ (A : ℝ)) :
    Real.sqrt (∫ x in left..right,
      energyDensity S (horizontalJet z ell) (coordinatePoint x theta)) ≤
        (initialCutEnergyBudget (right - left) M A : ℝ) := by
  let u := horizontalJet z ell
  have hu := horizontalJet_contDiffOn hU hz ell
  have hd (i : Fin 2) := partial_contDiffOn hu hU i
  have hb (i : Fin 2) (x : ℝ) (hx : x ∈ Icc left right) :
      |coordPartial i u (coordinatePoint x theta)| ≤ (A : ℝ) := by
    have he : coordPartial i u (coordinatePoint x theta) =
        iteratedCoordPartial (List.replicate ell 0 ++ [i]) z (coordinatePoint x theta) := by
      rw [← horizontalJet_coordPartial hU hz i ell _ (hseg x hx), horizontalJet_eq_spatialJet]
      exact congrFun (spatialJet_firstJet_eq_word z ell i) _
    rw [he]
    apply hcut _ _ x hx
    simp only [List.length_append, List.length_replicate, List.length_singleton, le_refl]
  have hpoint (x : ℝ) (hx : x ∈ Icc left right) :
      energyDensity S u (coordinatePoint x theta) ≤ (1 + M) * (A : ℝ)^2 / 2 := by
    have h0 : coordPartial 0 u (coordinatePoint x theta)^2 ≤ (A : ℝ)^2 := by
      exact sq_le_sq.mpr ((hb 0 x hx).trans (le_abs_self _))
    have h1 : coordPartial 1 u (coordinatePoint x theta)^2 ≤ (A : ℝ)^2 := by
      exact sq_le_sq.mpr ((hb 1 x hx).trans (le_abs_self _))
    have hm := mul_le_mul (hSupper x hx) h0 (sq_nonneg _) hM
    unfold energyDensity
    nlinarith
  have he : ContDiffOn ℝ ∞ (energyDensity S u) U :=
    (((hd 1).pow 2).add (hS.mul ((hd 0).pow 2))).div_const 2
  have hcont : ContinuousOn (fun x => energyDensity S u (coordinatePoint x theta)) (Icc left right) :=
    he.continuousOn.comp (horizontalPoint_contDiff theta).continuous.continuousOn hseg
  have hi : (∫ x in left..right, energyDensity S u (coordinatePoint x theta)) ≤
      ∫ x in left..right, (1 + M) * (A : ℝ)^2 / 2 :=
    intervalIntegral.integral_mono_on hlr (hcont.intervalIntegrable_of_Icc hlr)
    intervalIntegrable_const hpoint
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  apply (Real.sqrt_le_left (initialCutEnergyBudget (right - left) M A).2).mpr
  change _ ≤ (Real.sqrt ((right - left) * (1 + M) / 2) * (A : ℝ))^2
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (right - left) * (1 + M) / 2)]
  nlinarith

end SmoothLocal.HighEquation

end

end OAI
