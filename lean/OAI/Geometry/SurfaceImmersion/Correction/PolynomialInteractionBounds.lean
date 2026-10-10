import OAI.Geometry.SurfaceImmersion.Geometry.ScaledNonlinearBounds

namespace OAI

/-! Only the polynomial part of the mixed free/forced quadratic error. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

def coordinatePolynomialInteraction {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (X Y : RealModes.RField 4) : SmallModes.Base → PhaseMean.Tensor :=
  (tensorQuadraticCross P ε G (X ∘ planeCoordinateIsometry)
    (Y ∘ planeCoordinateIsometry) 0 ∘ planeCoordinateIsometry.symm)+
    coordinateQuadraticPolynomial P ε G Y 0

lemma coordinatePolynomialInteraction_smooth {n : ℕ}
    {P : Fin 3 → Fin n → Expression} (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    {G : Base → Space} {X Y : RealModes.RField 4}
    (hG : ContDiff ℝ ∞ G) (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) (ε : ℝ) :
    ContDiff ℝ ∞ (coordinatePolynomialInteraction P ε G X Y) :=
  ((tensorQuadraticCross_smooth hP hG (hX.comp planeCoordinateIsometry.contDiff)
    (hY.comp planeCoordinateIsometry.contDiff) ε 0).comp planeCoordinateIsometry.symm.contDiff).add
    (coordinateQuadraticPolynomial_smooth hP hG hY ε 0)

lemma coordinate_quadratic_add {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {X Y : RealModes.RField 4} (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) :
    coordinateQuadraticPolynomial P ε G (X+Y) 0 =
      coordinateQuadraticPolynomial P ε G X 0+coordinatePolynomialInteraction P ε G X Y := by
  have hh := coordinateFullQuadratic_add P ε G hX hY
  funext x k
  have he := congrArg (fun f => f x k) hh
  have hm := congrFun (RealModes.realMetricTensor_add
    (hX.differentiable (by simp) x) (hY.differentiable (by simp) x)) k
  have hc := congrArg (fun f => f x k) (coordinateQuadraticInteraction_eq_cross P ε G X Y)
  change RealModes.realMetricTensor (X+Y) x k+_ =
    (RealModes.realMetricTensor X x k+_)+coordinateQuadraticInteraction P ε G X Y x k at he
  change coordinateQuadraticPolynomial P ε G (X+Y) 0 x k =
    coordinateQuadraticPolynomial P ε G X 0 x k+
      (tensorQuadraticCross P ε G (X ∘ planeCoordinateIsometry) (Y ∘ planeCoordinateIsometry) 0
        (planeCoordinateIsometry.symm x) k+coordinateQuadraticPolynomial P ε G Y 0 x k)
  simp only [Pi.add_apply] at hm hc
  change RealModes.realMetricTensor (X+Y) x k =
    RealModes.realMetricTensor X x k+RealModes.realLinearizedTensor X Y x k+
      RealModes.realMetricTensor Y x k at hm
  linarith only [he,hm,hc]

theorem scaled_polynomial_interaction_bound {n : ℕ} {U : Set Base} {Q : Set LowJet}
    (hU : IsOpen U) (hQ : IsCompact Q)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    (m : ℕ) (B₀ : ℝ) (hB₀ : 1 ≤ B₀) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (X Y : RealModes.RField 4)
      (τ ε δ A B : ℝ), 0 < τ → τ ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < δ → δ ≤ τ →
      0 < A → 0 < B → ε/τ^tensorLoss P ≤ 1 →
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ X → ContDiff ℝ ∞ Y →
      Set.MapsTo (lowJet G) U Q → WeightedBound U τ (m+tensorOrder P) B₀ (lowJet G) →
      WeightedBound Set.univ τ (m+tensorOrder P+1) (A*δ*τ) X →
      WeightedBound Set.univ τ (m+tensorOrder P+1) (B*δ^2) Y →
      WeightedBound (planeCoordinateIsometry.symm ⁻¹' U) τ m
        (E*(A*B+B^2)*(δ^3/τ)) (coordinatePolynomialInteraction P ε G X Y) := by
  obtain ⟨E,hE,he⟩ := coordinateCross_bound hU hQ P hP m B₀ hB₀
  refine ⟨E,hE,?_⟩
  intro G X Y τ ε δ A B hτ hτ1 hε hε1 hδ hδτ hA hB hsmall hG hX hY hGQ hGb hXb hYb
  let V := planeCoordinateIsometry.symm ⁻¹' U
  have hV : IsOpen V := hU.preimage planeCoordinateIsometry.symm.continuous
  have hX0 := hXb.mono_order (show m + tensorOrder P ≤ m + tensorOrder P + 1 by omega)
  have hY0 := hYb.mono_order (show m + tensorOrder P ≤ m + tensorOrder P + 1 by omega)
  have hc := he G X Y τ ε (A * δ * τ) (B * δ ^ 2) hτ hτ1 hε hε1
    (by positivity) (by positivity) hG hX hY hGQ hGb hX0 hY0
  have hcc := hc.mono_const (polynomial_mixed_scale hE hε hA.le hB.le hδ.le hτ hτ1 hsmall)
  have hy := he G Y Y τ ε (B * δ ^ 2) (B * δ ^ 2) hτ hτ1 hε hε1
    (by positivity) (by positivity) hG hY hY hGQ hGb hY0 hY0
  have hyy := hy.mono_const (polynomial_self_scale hE hε hB.le hδ.le hτ hτ1 hδτ hsmall)
  have hsYY : ContDiffOn ℝ ∞ (tensorQuadraticCross P ε G (Y ∘ planeCoordinateIsometry)
      (Y ∘ planeCoordinateIsometry) 0 ∘ planeCoordinateIsometry.symm) V := ((tensorQuadraticCross_smooth hP hG (hY.comp planeCoordinateIsometry.contDiff)
    (hY.comp planeCoordinateIsometry.contDiff) ε 0).comp planeCoordinateIsometry.symm.contDiff).contDiffOn
  have hyhalf := hyy.const_smul hV.uniqueDiffOn hsYY (1 / 2 : ℝ)
  have hys : WeightedBound V τ m (E * B ^ 2 * (δ ^ 3 / τ))
      (coordinateQuadraticPolynomial P ε G Y 0) := by
    rw [coordinateQuadraticPolynomial_eq_cross]
    apply hyhalf.mono_const
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_of_le_one_left (by positivity) (by norm_num)
  have hscross : ContDiffOn ℝ ∞ (tensorQuadraticCross P ε G (X ∘ planeCoordinateIsometry)
      (Y ∘ planeCoordinateIsometry) 0 ∘ planeCoordinateIsometry.symm) V :=
    ((tensorQuadraticCross_smooth hP hG (hX.comp planeCoordinateIsometry.contDiff)
      (hY.comp planeCoordinateIsometry.contDiff) ε 0).comp planeCoordinateIsometry.symm.contDiff).contDiffOn
  have hadd := hcc.add hV.uniqueDiffOn hτ.le hscross
    (coordinateQuadraticPolynomial_smooth hP hG hY ε 0).contDiffOn hys
  convert hadd using 1 <;> first | rfl | ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
