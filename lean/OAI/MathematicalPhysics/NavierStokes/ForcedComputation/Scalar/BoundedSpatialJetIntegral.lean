import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetBilinear
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

/-! Integrating time-dependent sources in the finite spatial jet Banach space. -/

noncomputable section
namespace ForcedComputation.BoundedSpatialJets

open MeasureTheory
open scoped Topology BoundedContinuousFunction

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Time integration commutes with pointwise evaluation of the represented function. -/
theorem function_intervalIntegral (k : ℕ) (J : ℝ → Space E F k) (a b : ℝ)
    (hJ : IntervalIntegrable J volume a b) (x : E) :
    function E F k (∫ t in a..b, J t) x =
      ∫ t in a..b, function E F k (J t) x := by
  let L : Space E F k →L[ℝ] F :=
    (BoundedContinuousFunction.evalCLM ℝ x).comp (functionMap E F k)
  exact (L.intervalIntegral_comp_comm hJ).symm

/-- Every recorded spatial jet commutes with time integration. -/
theorem jet_intervalIntegral (k : ℕ) (J : ℝ → Space E F k) (a b : ℝ)
    (hJ : IntervalIntegrable J volume a b) (i : Fin (k + 1)) (x : E) :
    (∫ t in a..b, J t).val i x = ∫ t in a..b, (J t).val i x := by
  let L : Space E F k →L[ℝ] Value E F i.val :=
    (BoundedContinuousFunction.evalCLM ℝ x).comp (projection E F k i)
  exact (L.intervalIntegral_comp_comm hJ).symm

/-- Time integration preserves all spatial derivatives through the selected finite order. -/
theorem iteratedFDeriv_intervalIntegral (k : ℕ) (J : ℝ → Space E F k) (a b : ℝ)
    (hJ : IntervalIntegrable J volume a b) (n : ℕ) (hn : n ≤ k) (x : E) :
    iteratedFDeriv ℝ n (function E F k (∫ t in a..b, J t)) x =
      ∫ t in a..b, iteratedFDeriv ℝ n (function E F k (J t)) x := by
  simp only [iteratedFDeriv_function E F k _ n hn]
  exact jet_intervalIntegral E F k J a b hJ ⟨n, by omega⟩ x

omit [CompleteSpace F] in
/-- A uniform source bound gives the exact interval-length bound in the jet norm. -/
theorem norm_intervalIntegral_le (k : ℕ) (J : ℝ → Space E F k) (a b C : ℝ)
    (hJ : ∀ t ∈ Set.uIoc a b, ‖J t‖ ≤ C) :
    ‖∫ t in a..b, J t‖ ≤ C * |b - a| :=
  intervalIntegral.norm_integral_le_of_norm_le_const hJ

variable (G H : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace F] [CompleteSpace H] in
/-- A time-dependent coefficient and unknown yield an integrable jet-valued source. -/
theorem intervalIntegrable_bilinear (k : ℕ) (B : F →L[ℝ] G →L[ℝ] H)
    (J : ℝ → Space E F k) (K : ℝ → Space E G k) (a b : ℝ)
    (hJ : ContinuousOn J (Set.uIcc a b)) (hK : ContinuousOn K (Set.uIcc a b)) :
    IntervalIntegrable (fun t => bilinear E F G H k B (J t) (K t)) volume a b :=
  (continuousOn_bilinear E F G H (Set.uIcc a b) k B J K hJ hK).intervalIntegrable

omit [CompleteSpace F] [CompleteSpace H] in
/-- Explicit finite-time source bound, with the finite-order Leibniz constant. -/
theorem norm_intervalIntegral_bilinear_le (k : ℕ) (B : F →L[ℝ] G →L[ℝ] H)
    (J : ℝ → Space E F k) (K : ℝ → Space E G k) (a b A C : ℝ)
    (hC : 0 ≤ C) (hJ : ∀ t ∈ Set.uIoc a b, ‖J t‖ ≤ A)
    (hK : ∀ t ∈ Set.uIoc a b, ‖K t‖ ≤ C) :
    ‖∫ t in a..b, bilinear E F G H k B (J t) (K t)‖ ≤
      (‖B‖ * (2 : ℝ) ^ k * A * C) * |b - a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  calc
    _ ≤ ‖B‖ * (2 : ℝ) ^ k * ‖J t‖ * ‖K t‖ :=
      norm_bilinear_le E F G H k B (J t) (K t)
    _ ≤ ‖B‖ * (2 : ℝ) ^ k * ‖J t‖ * C :=
      mul_le_mul_of_nonneg_left (hK t ht) (by positivity)
    _ ≤ ‖B‖ * (2 : ℝ) ^ k * A * C :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hJ t ht) (by positivity)) hC

end ForcedComputation.BoundedSpatialJets

end

end OAI
