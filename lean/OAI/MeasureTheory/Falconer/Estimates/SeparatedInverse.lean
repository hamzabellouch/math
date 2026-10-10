import OAI.MeasureTheory.Falconer.Fourier.SeparatedJets
import OAI.MeasureTheory.Falconer.Fourier.SafeStationaryChart
import OAI.MeasureTheory.Falconer.Estimates.LocalInverse

namespace OAI

/-! # Finite endpoint separation of the actual inverse amplitudes

The finite expansion is constructed from product rules and chart pullbacks.
Every factor is globally smooth and depends on one endpoint only. This is
an identity for the original masked inverse, with no extra analytic input.
-/

namespace Falconer
open scoped ContDiff

variable {X Y : Type*}

namespace SmoothSeparation

noncomputable def stationaryJetMultiplier (m j : ℕ) (e : Space (m+3)) : ℂ :=
  (stationaryPatchMask m e : ℂ)*
    (sphereStationaryConstant (m+2)/((2*Complex.I)^j*(j.factorial : ℂ)))

theorem stationaryJetMultiplier_contDiff (m j : ℕ) :
    ContDiff ℝ ∞ (stationaryJetMultiplier m j) := by
  exact (Complex.ofRealCLM.contDiff.comp (stationaryPatchMask_contDiff m)).mul contDiff_const

noncomputable def stationaryJointDensity (m : ℕ) (z : Space (m+3) × Space (m+2)) : ℂ :=
  safeStationaryDensity m z.2

theorem stationaryJointDensity_contDiff (m : ℕ) :
    ContDiff ℝ ∞ (stationaryJointDensity m) :=
  (safeStationaryDensity_contDiff m).comp contDiff_snd

noncomputable def stationaryJet (m j : ℕ) (S : SmoothSeparation X Y (Space (m+3))) :
    SmoothSeparation X Y (Space (m+3)) :=
  let T := (S.pullback (safeStationaryChart m) (safeStationaryChart_contDiff m)).mulLeft
    (stationaryJointDensity m) (stationaryJointDensity_contDiff m)
  let U := (T.iteratedLaplacian (verticalDirections (m+2)) j).pullback
    (fun e => (e,(0 : Space (m+2)))) (contDiff_id.prodMk contDiff_const)
  U.mulLeft (stationaryJetMultiplier m j) (stationaryJetMultiplier_contDiff m j)

theorem stationaryJet_value (m j : ℕ) (S : SmoothSeparation X Y (Space (m+3)))
    (x : X) (y : Y) (e : Space (m+3)) :
    (S.stationaryJet m j).value x y e = maskedStationaryCoefficient m j (S.value x y) e := by
  rw [maskedStationaryCoefficient_safe]
  rw [stationaryJet,mulLeft_value,pullback_value,iteratedLaplacian_value]
  rw [iteratedDirectionalLaplacian_vertical]
  · simp only [mulLeft_value,pullback_value,quadraticJetCoefficient,
      stationaryJetMultiplier,stationaryJointDensity]
    ring
  · exact value_contDiff _ x y

noncomputable def inverse (m : ℕ) (S : SmoothSeparation X Y (Space (m+3))) :
    ℕ → SmoothSeparation X Y (Space (m+3))
  | 0 => S.mulLeft (fun e => (sphereStationaryConstant (m+2))⁻¹*(stationaryPatchMask m e : ℂ))
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (stationaryPatchMask_contDiff m)))
  | j+1 => (sum (fun h : Fin (j+1) => (inverse m S (j-h)).stationaryJet m (h+1))).mulLeft
      (fun _ => -(sphereStationaryConstant (m+2))⁻¹) contDiff_const
termination_by j => j
decreasing_by omega

theorem inverse_value (m j : ℕ) (S : SmoothSeparation X Y (Space (m+3)))
    (x : X) (y : Y) (e : Space (m+3)) :
    (S.inverse m j).value x y e = localInverseAmplitude m (S.value x y) j e := by
  induction j using Nat.strong_induction_on generalizing e with
  | h j ih =>
    cases j with
    | zero =>
      rw [inverse,mulLeft_value,localInverseAmplitude]
    | succ j =>
      rw [inverse,mulLeft_value,sum_value,localInverseAmplitude]
      congr 1
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro h _
      rw [stationaryJet_value]
      have he : (S.inverse m (j-h)).value x y = localInverseAmplitude m (S.value x y) (j-h) := by
        funext z
        exact ih (j-h) (by have hh := h.isLt; omega) z
      rw [he]

end SmoothSeparation

/-- The exact finite endpoint expansion used in weighted-shell conversion.
No endpoint parameter occurs in the opposite factor, and all angular
factors are globally smooth. -/
theorem localInverseAmplitude_product_separated (m j : ℕ)
    (B : X → Space (m+3) → ℂ) (C : Y → Space (m+3) → ℂ)
    (hB : ∀ x, ContDiff ℝ ∞ (B x)) (hC : ∀ y, ContDiff ℝ ∞ (C y)) :
    ∃ S : SmoothSeparation X Y (Space (m+3)), ∀ x y e,
      localInverseAmplitude m (fun w => B x w*C y w) j e = S.value x y e := by
  let P := SmoothSeparation.product B C hB hC
  refine ⟨P.inverse m j,?_⟩
  intro x y e
  rw [SmoothSeparation.inverse_value]
  have hp : P.value x y = fun w => B x w*C y w := by
    funext w
    exact SmoothSeparation.product_value B C hB hC x y w
  rw [hp]

end Falconer

end OAI
