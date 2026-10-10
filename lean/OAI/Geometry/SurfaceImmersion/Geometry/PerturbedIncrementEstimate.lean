import OAI.Geometry.SurfaceImmersion.Correction.FreeForcedIncrementIdentity
import OAI.Geometry.SurfaceImmersion.Correction.FreeForcedSegment
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanCoefficient

namespace OAI

/-! Combine the actual polynomial metric expansion and its finite free and
forced cancellations. The polynomial loss is fixed before the accuracy order. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes

lemma coordinateFullLinearized_smooth_global {n : ℕ}
    {P : Fin 3 → Fin n → Expression} (hP : ∀ k l, (P k l).SmoothCoeffs univ)
    {G : Base → Space} {X : RField 4} (hG : ContDiff ℝ ∞ G)
    (hX : ContDiff ℝ ∞ X) (ε : ℝ) :
    ContDiff ℝ ∞ (coordinateFullLinearized P ε G X) := by
  apply (contDiffOn_univ.mp (contDiffOn_realLinearizedTensor isOpen_univ
    (hG.comp planeCoordinateIsometry.symm.contDiff).contDiffOn hX.contDiffOn)).add
  apply contDiff_pi.mpr
  intro k
  change ContDiff ℝ ∞ (fun p => ∑ l, ε^(l.val+1) *
    (P k l).variation G (X ∘ planeCoordinateIsometry) (planeCoordinateIsometry.symm p,0))
  apply ContDiff.sum
  intro l _
  apply contDiff_const.mul
  have hs := (P k l).variation_smooth (U := univ) isOpen_univ hG
    (hX.comp planeCoordinateIsometry.contDiff) (fun _ _ => mem_univ _) (hP k l)
  have hs' : ContDiff ℝ ∞ ((P k l).variation G (X ∘ planeCoordinateIsometry)) := by
    apply contDiffOn_univ.mp
    simpa only [univ_prod_univ] using hs
  exact hs'.comp (planeCoordinateIsometry.symm.contDiff.prodMk contDiff_const)

lemma combinedQuadraticMean_smooth_global {n : ℕ} {ι : Type*} [Fintype ι]
    {P : Fin 3 → Fin n → Expression} (hP : ∀ k l, (P k l).SmoothCoeffs univ)
    {G : Base → Space} {φ : ι → Base → ℝ} {H : ι → Base → Fin 4 → ℂ}
    (hG : ContDiff ℝ ∞ G) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (hH : ∀ i, ContDiff ℝ ∞ (H i)) (ε τ : ℝ) :
    ContDiff ℝ ∞ (combinedQuadraticMean P ε G φ H τ 0) := by
  have hs : ContDiff ℝ ∞ (RealModes.zeroPhaseSum τ
      (fun i => coordinatePhase (φ i)) (fun i => coordinateAmplitude (H i))) := by
    apply contDiffOn_univ.mp
    apply ContDiffOn.sum
    intro i _
    apply contDiffOn_pi.mpr
    intro k
    exact QuadraticMean.contDiffOn_zeroPair
      (QuadraticMean.contDiffOn_derivativeAmplitude isOpen_univ
        ((hφ i).comp planeCoordinateIsometry.symm.contDiff).contDiffOn
        ((hH i).comp planeCoordinateIsometry.symm.contDiff).contDiffOn τ _)
      (QuadraticMean.contDiffOn_derivativeAmplitude isOpen_univ
        ((hφ i).comp planeCoordinateIsometry.symm.contDiff).contDiffOn
        ((hH i).comp planeCoordinateIsometry.symm.contDiff).contDiffOn τ _)
  apply hs.add
  apply contDiff_pi.mpr
  intro k
  apply ContDiff.sum
  intro i _
  exact (contDiffOn_univ.mp (quadraticMeanCoefficient_smooth isOpen_univ (hP k)
    hG (hφ i) (hH i) (fun _ _ => mem_univ _) ε τ 0)).comp
      planeCoordinateIsometry.symm.contDiff

lemma coordinateQuadraticInteraction_smooth_global {n : ℕ}
    {P : Fin 3 → Fin n → Expression} (hP : ∀ k l, (P k l).SmoothCoeffs univ)
    {G : Base → Space} {X Y : RField 4} (hG : ContDiff ℝ ∞ G)
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) (ε : ℝ) :
    ContDiff ℝ ∞ (coordinateQuadraticInteraction P ε G X Y) := by
  rw [coordinateQuadraticInteraction_eq_cross]
  exact (((contDiffOn_univ.mp (contDiffOn_realLinearizedTensor isOpen_univ
    hX.contDiffOn hY.contDiffOn)).add
    (contDiffOn_univ.mp (contDiffOn_realMetricTensor isOpen_univ hY.contDiffOn))).add
    ((tensorQuadraticCross_smooth hP hG (hX.comp planeCoordinateIsometry.contDiff)
      (hY.comp planeCoordinateIsometry.contDiff) ε 0).comp
      planeCoordinateIsometry.symm.contDiff)).add
    (coordinateQuadraticPolynomial_smooth hP hG hY ε 0)

/-- The three finite cancellation errors and the nonlinear error control the
same metric operator. The constants for the cubic part precede the map and
scales; no existence of an improved map is assumed. -/
theorem perturbed_increment_estimate {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D : Set Base} {Q : Set LowJet} (hD : IsOpen D) (hQ : IsCompact Q)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs univ)
    (m : ℕ) (B₀ A B : ℝ) (hB₀ : 1 ≤ B₀) (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : Base → Space) (φ : ι → Base → ℝ)
      (H : ι → Base → Fin 4 → ℂ) (Y : RField 4) (T : SmallModes.Base → PhaseMean.Tensor),
      ContDiff ℝ ∞ G → (∀ i, ContDiff ℝ ∞ (φ i)) →
      (∀ i, ContDiff ℝ ∞ (H i)) → ContDiff ℝ ∞ Y → ContDiff ℝ ∞ T →
      ∀ (τ ε δ η F E M : ℝ) (q : ℕ),
      0 < τ → τ ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < δ → δ ≤ τ → 0 ≤ η →
      0 ≤ F → 0 ≤ E → 0 ≤ M → ε/τ^tensorLoss P ≤ 1 →
      let X := QuadraticMean.sumDisplacement τ (fun i => coordinatePhase (φ i))
        (fun i => coordinateAmplitude (H i))
      MapsTo (lowJet G) D Q → WeightedBound D τ (m+tensorOrder P) B₀ (lowJet G) →
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo
        (lowJet (fun p => G p+t • (X+Y) (planeCoordinateIsometry p))) D Q) →
      (∀ t ∈ Icc (0 : ℝ) 1, WeightedBound D τ (m+tensorOrder P) B₀
        (lowJet (fun p => G p+t • (X+Y) (planeCoordinateIsometry p)))) →
      WeightedBound univ τ (m+tensorOrder P+1) (A*δ*τ) X →
      WeightedBound univ τ (m+tensorOrder P+1) (B*δ^2) Y →
      WeightedBound (planeCoordinateIsometry.symm ⁻¹' D) τ m
        (F*(δ*τ)*η^(q+1)) (coordinateFullLinearized P ε G X) →
      WeightedBound (planeCoordinateIsometry.symm ⁻¹' D) τ m
        (E*δ^2*η^(q+1))
        (coordinateFullLinearized P ε G Y+combinedNonzeroQuadratic P ε G φ H τ) →
      WeightedBound (planeCoordinateIsometry.symm ⁻¹' D) τ m
        (M*δ^2*η^(q+1)) (combinedQuadraticMean P ε G φ H τ 0-T) →
      WeightedBound (planeCoordinateIsometry.symm ⁻¹' D) τ m
        ((F+E+M+C)*(δ*η^(q+1)+δ^3/τ))
        (coordinateMetricMap P ε (fun p => G p+(X+Y) (planeCoordinateIsometry p))-
          coordinateMetricMap P ε G-T) := by
  obtain ⟨C₁,hC₁,h₁⟩ := scaled_coordinate_interaction_bound hD hQ P hP m B₀ hB₀
  obtain ⟨C₂,hC₂,h₂⟩ := scaled_coordinate_taylor_bound hD hQ P hP m B₀ hB₀
  let C := 4*2^m*(2*A*B+B^2)+C₁*(A*B+B^2)+C₂*(A+B)^3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro G φ H Y T hG hφ hH hY hT τ ε δ η F E M q
    hτ hτ1 hε hε1 hδ hδτ hη hF hE hM hsmall X hGQ hGb hseg hsegb hXb hYb hlin hforced hmean
  have hX : ContDiff ℝ ∞ X := by
    apply ContDiff.sum
    intro i _
    exact contDiffOn_univ.mp (contDiffOn_displacement
      ((hφ i).comp planeCoordinateIsometry.symm.contDiff).contDiffOn
      ((hH i).comp planeCoordinateIsometry.symm.contDiff).contDiffOn τ)
  let V := planeCoordinateIsometry.symm ⁻¹' D
  have hV : IsOpen V := hD.preimage planeCoordinateIsometry.symm.continuous
  have hsmX := coordinateFullLinearized_smooth_global hP hG hX ε
  have hsmY := coordinateFullLinearized_smooth_global hP hG hY ε
  have hsmMean := combinedQuadraticMean_smooth_global hP hG hφ hH ε τ
  have hsmNonzero : ContDiff ℝ ∞ (combinedNonzeroQuadratic P ε G φ H τ) := by
    have he := combined_quadratic_expansion P ε G φ H hφ hH τ 0
    have hs := ((contDiffOn_univ.mp (contDiffOn_realMetricTensor isOpen_univ hX.contDiffOn)).add
      (coordinateQuadraticPolynomial_smooth hP hG hX ε 0)).sub hsmMean
    have heq : combinedNonzeroQuadratic P ε G φ H τ =
        (realMetricTensor X + coordinateQuadraticPolynomial P ε G X 0) -
          combinedQuadraticMean P ε G φ H τ 0 := by
      ext p k
      have hh := congrArg (fun f => f p k) he
      change realMetricTensor X p k + coordinateQuadraticPolynomial P ε G X 0 p k =
        combinedQuadraticMean P ε G φ H τ 0 p k +
          combinedNonzeroQuadratic P ε G φ H τ p k at hh
      change combinedNonzeroQuadratic P ε G φ H τ p k =
        realMetricTensor X p k + coordinateQuadraticPolynomial P ε G X 0 p k -
          combinedQuadraticMean P ε G φ H τ 0 p k
      linarith only [hh]
    rw [heq]
    exact hs
  have hint := h₁ G X Y τ ε δ A B hτ hτ1 hε hε1 hδ hδτ hA hB hsmall
    hG hX hY hGQ hGb hXb hYb
  have hsum := free_forced_size hX hY hτ hδ.le hδτ hB.le hXb hYb
  have htaylor := h₂ G (X+Y) τ ε δ (A+B) hτ hτ1 hε hε1 hδ
    (add_pos hA hB) hsmall hG (hX.add hY) hseg hsegb (hsum.mono_order (by omega))
  have hsInt := coordinateQuadraticInteraction_smooth_global hP hG hX hY ε
  have hsTaylor : ContDiff ℝ ∞ (coordinateTaylorRemainder P ε G (X+Y)) :=
    (tensorTaylorRemainder_smooth hP hG
      ((hX.add hY).comp planeCoordinateIsometry.contDiff) ε 0).comp
      planeCoordinateIsometry.symm.contDiff
  have hb := (((hlin.add hV.uniqueDiffOn hτ.le hsmX.contDiffOn
    (hsmY.add hsmNonzero).contDiffOn hforced).add hV.uniqueDiffOn hτ.le
      (hsmX.add (hsmY.add hsmNonzero)).contDiffOn (hsmMean.sub hT).contDiffOn hmean).add
      hV.uniqueDiffOn hτ.le ((hsmX.add (hsmY.add hsmNonzero)).add (hsmMean.sub hT)).contDiffOn
      hsInt.contDiffOn hint).add hV.uniqueDiffOn hτ.le
      (((hsmX.add (hsmY.add hsmNonzero)).add (hsmMean.sub hT)).add hsInt).contDiffOn
      hsTaylor.contDiffOn htaylor
  have hi := free_forced_metric_increment_identity P ε hG φ H hφ hH τ hY T
  have hb' := hb.congr (fun p _ => congrFun hi p)
  apply hb'.mono_const
  have hd1 : δ ≤ 1 := hδτ.trans hτ1
  have hdt : δ*τ ≤ δ := mul_le_of_le_one_right hδ.le hτ1
  have hd2 : δ^2 ≤ δ := by nlinarith
  have hp : 0 ≤ η^(q+1) := pow_nonneg hη _
  have hx : 0 ≤ δ^3/τ := by positivity
  have hf := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdt hF) hp
  have he := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd2 hE) hp
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd2 hM) hp
  change _ ≤ (F+E+M+C)*(δ*η^(q+1)+δ^3/τ)
  dsimp [C]
  nlinarith [mul_nonneg (add_nonneg (add_nonneg hF hE) hM) hx,
    mul_nonneg hC (mul_nonneg hδ.le hp)]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
