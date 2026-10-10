import OAI.Geometry.SurfaceImmersion.Correction.ChartedForcedMode
import OAI.Geometry.SurfaceImmersion.Correction.ChartResidualBounds
import OAI.Geometry.SurfaceImmersion.Correction.CoordinateLinearizedSupport

namespace OAI

/-! Global residual estimates for the actual forced correction constructed
in a local phase chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean
variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

theorem global_charted_forced_mode
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
      (∀ m, WeightedBound Set.univ τ m
        ((m.factorial : ℝ) * (2 ^ m * (SmallModes.forcedModeBudget 4 (tensorOrder P) C D q m *
          supportedWeightedSeminorm Kc s (m + (q + 1) * (tensorOrder P + 1)) fc)) * J m ^ m) X) ∧
      (∀ m, WeightedBound Set.univ τ m
        (tensorChartBudget m (J m) (J (m + 1)) *
          (2 ^ m * ((τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) *
            FiniteParametrix.boundProfile (tensorOrder P + 1) κ
              (fun r => κ r * supportedWeightedSeminorm Kc s (r + (tensorOrder P + 1)) fc) q m)))
        (fun x => coordinateFullLinearized P ε G X x + QuadraticMean.displacement τ (coordinatePhase φ) f x)) := by
  obtain ⟨X,hX,hsp,hsm,hsize,hres⟩ := charted_forced_mode hO hU P hP hG hQ K hKU hφ τ ε e he hi hKe
    hphase hFc hM hτ hs hτs hs1 hε hsmall C D J hC hD hJ hcoords hc hR f q
  dsimp only
  refine ⟨X,hX,hsp,hsize,?_⟩
  intro m
  let Kc := chartSupport e (modeSupport K) hKe
  let fc := tensorChartPush e hi (modeSupport K) hKe f
  let κ := fun r => max (SmallModes.errorConstant r (C r))
    (D r * SmallModes.initialConstant 4 (r + tensorOrder P) (C (r + tensorOrder P)))
  have hκ (r : ℕ) : 0 ≤ κ r := (SmallModes.errorConstant_nonneg r (hC r)).trans (le_max_left _ _)
  have hη : 0 ≤ τ / s + ε / τ ^ tensorLoss P :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have herror : 0 ≤ 2 ^ m * ((τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) *
      FiniteParametrix.boundProfile (tensorOrder P + 1) κ
        (fun r => κ r * supportedWeightedSeminorm Kc s (r + (tensorOrder P + 1)) fc) q m) :=
    mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hη _)
      (FiniteParametrix.boundProfile_nonneg hκ (fun r => mul_nonneg (hκ r) (apply_nonneg _ _)) q m))
  have hsupp := (fullLinearized_residual_tsupport P ε G (modeSupport K).isCompact.isClosed hsp
    f.tsupport_subset τ (coordinatePhase φ)).trans hKe
  have hτ1 : τ ≤ 1 := hτs.trans (show (s : ℝ) ≤ 1 from hs1)
  have hfield := RealModes.weighted_coordDeriv_of_jets e.open_source he hτ.le hτ1
    (zero_le_one.trans (hJ (m + 1))) (hcoords (m + 1))
  exact weighted_residual_from_chart e he hi hsupp hτ hτ1 herror (hJ m)
    (zero_le_one.trans (hJ (m + 1))) (hcoords m) hfield hsm (hres m)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
