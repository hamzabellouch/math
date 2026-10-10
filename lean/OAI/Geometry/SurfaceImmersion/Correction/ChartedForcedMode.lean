import OAI.Geometry.SurfaceImmersion.Atlas.ChartDisplacement
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseChartBounds
import OAI.Geometry.SurfaceImmersion.Geometry.PerturbedForcedSize

namespace OAI

/-! The finite perturbed correction algorithm applied to an actual local
phase chart, with real displacement, support, size and residual estimates. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean

variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

theorem charted_forced_mode
    (hO : IsOpen O) (hU : IsOpen U) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ k l, (P k l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε : ℝ)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source)
    (hphase : ∀ x ∈ e.source, (e x).1 = coordinatePhase φ x)
    (hFc : ContDiff ℝ ∞ ((G ∘ planeCoordinateIsometry.symm) ∘ e.symm))
    (hM : SmallModes.ModeDomain (fun p => RealModes.complexify
      (G (planeCoordinateIsometry.symm (e.symm p)))) e.target)
    {s : ℝ≥0} (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hε : 0 ≤ ε) (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1)
    (C D J : ℕ → ℝ) (hC : ∀ m, 0 ≤ C m) (hD : ∀ m, 0 ≤ D m) (hJ : ∀ m, 1 ≤ J m)
    (hcoords : ∀ m j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J m)
    (hc : ∀ m, SmallModes.ReconstructionCoefficientBound
      (fun p => RealModes.complexify (G (planeCoordinateIsometry.symm (e.symm p))))
      e.target s (m + 1) (C m))
    (hR : ∀ m Z, supportedWeightedSeminorm (chartSupport e (modeSupport K) hKe) s m
      (phaseChartPolynomialOperator hO hU P hP hG hQ K hKU hφ τ ε e he hi hKe Z) ≤
      ε / τ ^ tensorLoss P * D m *
        supportedWeightedSeminorm (chartSupport e (modeSupport K) hKe) s (m + tensorOrder P) Z)
    (f : SupportedField (F := ComplexTensor) (modeSupport K)) (q : ℕ) :
    let Kc := chartSupport e (modeSupport K) hKe
    let fc := tensorChartPush e hi (modeSupport K) hKe f
    let κ := fun m => max (SmallModes.errorConstant m (C m))
      (D m * SmallModes.initialConstant 4 (m + tensorOrder P) (C (m + tensorOrder P)))
    ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ (modeSupport K : Set SmallModes.Base) ∧
      ContDiffOn ℝ ∞ (fun y => pullbackField e.symm y
        (coordinateFullLinearized P ε G X (e.symm y) +
          QuadraticMean.displacement τ (coordinatePhase φ) f (e.symm y))) e.target ∧
      (∀ m, WeightedBound Set.univ τ m
        ((m.factorial : ℝ) * (2 ^ m * (SmallModes.forcedModeBudget 4 (tensorOrder P) C D q m *
          supportedWeightedSeminorm Kc s (m + (q + 1) * (tensorOrder P + 1)) fc)) * J m ^ m) X) ∧
      (∀ m, WeightedBound e.target τ m
        (2 ^ m * ((τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) *
          FiniteParametrix.boundProfile (tensorOrder P + 1) κ
            (fun r => κ r * supportedWeightedSeminorm Kc s (r + (tensorOrder P + 1)) fc) q m))
        (fun y => pullbackField e.symm y
          (coordinateFullLinearized P ε G X (e.symm y) +
            QuadraticMean.displacement τ (coordinatePhase φ) f (e.symm y)))) := by
  let Kc := chartSupport e (modeSupport K) hKe
  let fc := tensorChartPush e hi (modeSupport K) hKe f
  let Fc := (G ∘ planeCoordinateIsometry.symm) ∘ e.symm
  let Gc := fun p => RealModes.complexify (Fc p)
  have hGc : ContDiff ℝ ∞ Gc := (RealModes.complexifyCLM 4).contDiff.comp hFc
  let R := phaseChartPolynomialOperator hO hU P hP hG hQ K hKU hφ τ ε e he hi hKe
  let Z := SmallModes.perturbedMode τ hGc hM Kc (chartSupport_subset e (modeSupport K) hKe) R (-fc) q
  let A := (SmallModes.conjugatedDLM τ hGc Kc).restrictScalars ℝ + R
  let W := A Z + fc
  let X := QuadraticMean.displacement τ (coordinatePhase φ) (chartPull e he (modeSupport K) hKe Z)
  have hx := chart_displacement_smooth_support e he (modeSupport K) hKe (coordinatePhase φ)
    (hφ.comp planeCoordinateIsometry.symm.contDiff) τ Z
  have hid (y : SmallModes.Base) (hy : y ∈ e.target) :
      pullbackField e.symm y (coordinateFullLinearized P ε G X (e.symm y) +
        QuadraticMean.displacement τ (coordinatePhase φ) f (e.symm y)) = RealModes.realOsc τ W y := by
    rw [map_add, phaseChartFullLinearization hO hU P hP hG hQ K hKU hφ τ ε e he hi hKe hphase Z hy,
      chart_forcing_realization e hi (modeSupport K) hKe (coordinatePhase φ) hphase τ f hy]
    change RealModes.realOsc τ _ y + RealModes.realOsc τ fc y = RealModes.realOsc τ W y
    rw [← RealModes.realOsc_add_value]
    rfl
  dsimp only
  refine ⟨X,hx.1,hx.2,?_,?_,?_⟩
  · exact (RealModes.contDiffOn_realOsc W.contDiff.contDiffOn τ).congr hid
  · intro m
    have hb := SmallModes.perturbedMode_size τ hGc hM Kc (chartSupport_subset e (modeSupport K) hKe)
      hτ hs hτs hs1 hε hsmall C D hC hD hc R hR (-fc) q m
    simp only [map_neg_eq_map] at hb
    exact chart_displacement_bound e he (modeSupport K) hKe (coordinatePhase φ) hphase
      hs hτ hτs (hτs.trans (show (s : ℝ) ≤ 1 from hs1))
      (mul_nonneg (SmallModes.forcedModeBudget_nonneg 4 (tensorOrder P) C D hC q m) (apply_nonneg _ _))
      (hJ m) (hcoords m) Z hb
  · intro m
    let κ := fun r => max (SmallModes.errorConstant r (C r))
      (D r * SmallModes.initialConstant 4 (r + tensorOrder P) (C (r + tensorOrder P)))
    let E := (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) *
      FiniteParametrix.boundProfile (tensorOrder P + 1) κ
        (fun r => κ r * supportedWeightedSeminorm Kc s (r + (tensorOrder P + 1)) fc) q m
    have hr := SmallModes.perturbedMode_residual_bound τ hGc hM Kc (chartSupport_subset e (modeSupport K) hKe)
      hτ hs hτs hs1 hε C D hC hD hc R hR (-fc) q m
    have hb : supportedWeightedSeminorm Kc s m W ≤ E := by
      dsimp only at hr
      simp only [map_neg_eq_map, sub_neg_eq_add, mul_assoc] at hr
      rw [FiniteParametrix.boundProfile_const_mul] at hr
      simpa only [W,Z,A,E,κ,pow_succ,mul_assoc] using hr
    have hE : 0 ≤ E := (apply_nonneg _ _).trans hb
    have hw := RealModes.weighted_realOsc isOpen_univ hτ hτs hE W.contDiff.contDiffOn
      ((weightedBound_of_supportedSeminorm s m W).mono_const hb)
    apply (hw.restrict_open e.open_target).congr
    intro y hy
    exact hid y hy

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
