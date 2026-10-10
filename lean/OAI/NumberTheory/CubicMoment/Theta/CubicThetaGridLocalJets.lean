import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGridJets
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalBudget

namespace OAI

/-! Summable bounds for both derivatives on an actual coordinate
neighborhood. No derivative or normal-convergence assertion is assumed. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaCoordinateLine_jetBound (k : CubicThetaAxis)
    (cd : Eisenstein × Eisenstein) (s : ℂ) (x y v t : ℝ)
    (ht : 0<(cubicThetaCoordinateLine k x y v t).2) :
    ‖deriv (fun w => cubicThetaEisensteinGridTerm cd
        (cubicThetaCoordinateLine k x y v w) s) t‖ ≤
      ‖cubicThetaEisensteinGridTerm cd (cubicThetaCoordinateLine k x y v t) s‖*
        (cubicThetaFirstJetConstant s/(cubicThetaCoordinateLine k x y v t).2) ∧
    ‖deriv (deriv (fun w => cubicThetaEisensteinGridTerm cd
        (cubicThetaCoordinateLine k x y v w) s)) t‖ ≤
      ‖cubicThetaEisensteinGridTerm cd (cubicThetaCoordinateLine k x y v t) s‖*
        (cubicThetaSecondJetConstant s/(cubicThetaCoordinateLine k x y v t).2^2) := by
  cases k with
  | x => exact cubicThetaEisensteinGrid_jetBound cd.1 cd.2 s t y ht .x
  | y => exact cubicThetaEisensteinGrid_jetBound cd.1 cd.2 s x t ht .y
  | height => exact cubicThetaEisensteinGrid_jetBound cd.1 cd.2 s x y ht .height

private lemma uniform_ratio_bound {D F U K h a : ℝ} (hD : D ≤ F*(K/h))
    (hF : F ≤ U) (hF0 : 0 ≤ F) (hK : 0 ≤ K) (ha : 0<a) (hah : a ≤ h) :
    D ≤ U*(K/a) := by
  apply hD.trans
  exact mul_le_mul hF (div_le_div_of_nonneg_left hK ha hah)
    (div_nonneg hK (ha.trans_le hah).le) (hF0.trans hF)

theorem cubicThetaCoordinate_local_jets (k : CubicThetaAxis) (s : ℂ)
    (hs : 2<s.re) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ∃ r : ℝ, 0<r ∧ ∃ u₁ u₂ : (Eisenstein × Eisenstein) → ℝ,
      Summable u₁ ∧ Summable u₂ ∧
      ∀ cd t, t ∈ Set.Ioo (cubicThetaCoordinateCenter k x y v-r)
        (cubicThetaCoordinateCenter k x y v+r) →
      0<(cubicThetaCoordinateLine k x y v t).2 ∧
      ‖deriv (fun w => cubicThetaEisensteinGridTerm cd
          (cubicThetaCoordinateLine k x y v w) s) t‖ ≤ u₁ cd ∧
      ‖deriv (deriv (fun w => cubicThetaEisensteinGridTerm cd
          (cubicThetaCoordinateLine k x y v w) s)) t‖ ≤ u₂ cd := by
  obtain ⟨r,hr,hbudget⟩ := cubicThetaCoordinate_local_budget k x y hv
  let a := v/2
  let H := v*cubicThetaHeightConstant (cubicThetaCartesianPoint x y v)+1
  let u₁ := fun cd => (H^s.re*(cubicThetaFirstJetConstant s/a))*cubicThetaGridDecay s cd
  let u₂ := fun cd => (H^s.re*(cubicThetaSecondJetConstant s/a^2))*cubicThetaGridDecay s cd
  refine ⟨r,hr,u₁,u₂,(cubicThetaGridDecay_summable hs).mul_left _,
    (cubicThetaGridDecay_summable hs).mul_left _,?_⟩
  intro cd t ht
  obtain ⟨ha,hH⟩ := hbudget t ht
  have ha0 : 0<a := by dsimp [a]; positivity
  have hp : 0<(cubicThetaCoordinateLine k x y v t).2 := ha0.trans ha
  have hbound := cubicThetaEisensteinGridTerm_uniform_bound cd hp hs hH.le
  have hj := cubicThetaCoordinateLine_jetBound k cd s x y v t hp
  have hn := cubicThetaJetConstants_nonneg s
  refine ⟨hp,?_,?_⟩
  · have h := uniform_ratio_bound hj.1 hbound (_root_.norm_nonneg _) hn.1 ha0 ha.le
    convert h using 1
    dsimp [u₁,H]
    ring
  · have hasq : a^2 ≤ (cubicThetaCoordinateLine k x y v t).2^2 :=
      (sq_le_sq₀ ha0.le hp.le).mpr ha.le
    have h := uniform_ratio_bound hj.2 hbound (_root_.norm_nonneg _) hn.2
      (sq_pos_of_pos ha0) hasq
    convert h using 1
    dsimp [u₂,H]
    ring

end CubicFirstMoment

end

end OAI
