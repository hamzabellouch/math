import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateNonlinearBounds
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialNonlinearScales
import OAI.Geometry.Immersion.ClosedSurface.TensorBounds

namespace OAI

/-! The actual mixed and cubic nonlinear errors at the scales of the small
increment construction. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma coordinateQuadraticPolynomial_smooth {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ) {G : Base → Space}
    {X : RealModes.RField 4} (hG : ContDiff ℝ ∞ G) (hX : ContDiff ℝ ∞ X) (ε t : ℝ) :
    ContDiff ℝ ∞ (coordinateQuadraticPolynomial P ε G X t) := by
  rw [coordinateQuadraticPolynomial_eq_cross]
  exact ((tensorQuadraticCross_smooth hP hG (hX.comp planeCoordinateIsometry.contDiff)
    (hX.comp planeCoordinateIsometry.contDiff) ε t).comp
    planeCoordinateIsometry.symm.contDiff).const_smul (1 / 2 : ℝ)

theorem scaled_coordinate_interaction_bound {n : ℕ} {U : Set Base} {Q : Set LowJet}
    (hU : IsOpen U) (hQ : IsCompact Q)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    (m : ℕ) (B₀ : ℝ) (hB₀ : 1 ≤ B₀) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (X Y : RealModes.RField 4)
      (τ ε δ A B : ℝ), 0 < τ → τ ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < δ → δ ≤ τ →
      0 < A → 0 < B → ε / τ ^ tensorLoss P ≤ 1 →
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ X → ContDiff ℝ ∞ Y →
      Set.MapsTo (lowJet G) U Q → WeightedBound U τ (m + tensorOrder P) B₀ (lowJet G) →
      WeightedBound Set.univ τ (m + tensorOrder P + 1) (A * δ * τ) X →
      WeightedBound Set.univ τ (m + tensorOrder P + 1) (B * δ ^ 2) Y →
      WeightedBound (planeCoordinateIsometry.symm ⁻¹' U) τ m
        ((4 * 2 ^ m * (2 * A * B + B ^ 2) + E * (A * B + B ^ 2)) * (δ ^ 3 / τ))
        (coordinateQuadraticInteraction P ε G X Y) := by
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
  have hm := RealModes.weighted_cubic_remainder (n := 4) (m := m) isOpen_univ hτ hδ.le hδτ hA.le hB.le
    hX.contDiffOn hY.contDiffOn (hXb.mono_order (by omega)) (hYb.mono_order (by omega))
  have hsmetric : ContDiffOn ℝ ∞ (fun p => RealModes.realLinearizedTensor X Y p +
      RealModes.realMetricTensor Y p) V :=
    (RealModes.contDiffOn_realLinearizedTensor hV hX.contDiffOn hY.contDiffOn).add
      (RealModes.contDiffOn_realMetricTensor hV hY.contDiffOn)
  have hscross : ContDiffOn ℝ ∞ (tensorQuadraticCross P ε G (X ∘ planeCoordinateIsometry)
      (Y ∘ planeCoordinateIsometry) 0 ∘ planeCoordinateIsometry.symm) V := ((tensorQuadraticCross_smooth hP hG (hX.comp planeCoordinateIsometry.contDiff)
    (hY.comp planeCoordinateIsometry.contDiff) ε 0).comp planeCoordinateIsometry.symm.contDiff).contDiffOn
  have hmV := hm.restrict_open hV
  have hadd := (hmV.add hV.uniqueDiffOn hτ.le hsmetric hscross hcc).add hV.uniqueDiffOn hτ.le
    (hsmetric.add hscross) (coordinateQuadraticPolynomial_smooth hP hG hY ε 0).contDiffOn hys
  rw [coordinateQuadraticInteraction_eq_cross]
  convert hadd using 1 <;> first | rfl | ring

theorem scaled_coordinate_taylor_bound {n : ℕ} {U : Set Base} {Q : Set LowJet}
    (hU : IsOpen U) (hQ : IsCompact Q)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    (m : ℕ) (B₀ : ℝ) (hB₀ : 1 ≤ B₀) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (X : RealModes.RField 4)
      (τ ε δ A : ℝ), 0 < τ → τ ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < δ → 0 < A →
      ε / τ ^ tensorLoss P ≤ 1 → ContDiff ℝ ∞ G → ContDiff ℝ ∞ X →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Set.MapsTo
        (lowJet (fun p => G p + t • X (planeCoordinateIsometry p))) U Q) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, WeightedBound U τ (m + tensorOrder P) B₀
        (lowJet (fun p => G p + t • X (planeCoordinateIsometry p)))) →
      WeightedBound Set.univ τ (m + tensorOrder P) (A * δ * τ) X →
      WeightedBound (planeCoordinateIsometry.symm ⁻¹' U) τ m
        (E * A ^ 3 * (δ ^ 3 / τ)) (coordinateTaylorRemainder P ε G X) := by
  obtain ⟨E,hE,he⟩ := coordinateTaylorRemainder_bound hU hQ P hP m B₀ hB₀
  refine ⟨E,hE,?_⟩
  intro G X τ ε δ A hτ hτ1 hε hε1 hδ hA hsmall hG hX hGQ hGb hXb
  exact (he G X τ ε (A * δ * τ) hτ hτ1 hε hε1 (by positivity) hG hX hGQ hGb hXb).mono_const
    (polynomial_cubic_scale hE hε hA.le hδ.le hτ hτ1 hsmall)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
