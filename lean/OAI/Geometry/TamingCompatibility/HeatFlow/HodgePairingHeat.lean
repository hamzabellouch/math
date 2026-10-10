import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGammaTailPairing

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source}
namespace HodgeSmoothingCover
variable {ρ : ℝ} {hρ : 0 < ρ} (C : HodgeSmoothingCover A J α hs ht D hD ρ hρ)

def pairingHeatEvaluation (b : PreL2 A J α hs ht true) (x : X) :
    L2 A J α hs ht true →L[ℝ] ℝ :=
  (C.pairingEvaluation b x).comp (hodgeHeatBoost A J α hs ht D hD ρ)

lemma pairingHeatEvaluation_continuous (b : PreL2 A J α hs ht true) :
    Continuous (C.pairingHeatEvaluation b) :=
  (C.pairingEvaluation_continuous b).clm_comp continuous_const

def pairingHeatVector (b : PreL2 A J α hs ht true) (x : X) : L2 A J α hs ht true :=
  (C.pairingHeatEvaluation b x).adjoint 1

lemma pairingHeatVector_continuous (b : PreL2 A J α hs ht true) :
    Continuous (C.pairingHeatVector b) :=
  ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := L2 A J α hs ht true) (F := ℝ)).continuous.comp
    (C.pairingHeatEvaluation_continuous b)).clm_apply continuous_const

lemma pairingHeatVector_integrable (b : PreL2 A J α hs ht true) :
    Integrable (C.pairingHeatVector b) (geometricVolume A J α) := by
  let := geometricVolume_finite A J α hs ht
  exact (C.pairingHeatVector_continuous b).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma pairingHeatVector_integral (b : PreL2 A J α hs ht true) :
    ∫ x, C.pairingHeatVector b x ∂geometricVolume A J α =
      hodgeSpectralHeat A J α hs ht D hD (ρ^2) (smoothL2 A J α hs ht true b) := by
  apply ext_inner_right ℝ
  intro f
  have h := HilbertKernel.regularize_pair (geometricVolume A J α) (C.pairingHeatEvaluation b)
    (fun _ => (1:ℝ)) (C.pairingHeatVector_integrable b) f
  have hp : ⟪∫ x, C.pairingHeatVector b x ∂geometricVolume A J α,f⟫ =
      ∫ x, C.pairingEvaluation b x (hodgeHeatBoost A J α hs ht D hD ρ f)
        ∂geometricVolume A J α := by
    simpa only [HilbertKernel.regularize,pairingHeatVector,pairingHeatEvaluation,
      ContinuousLinearMap.comp_apply,Real.inner_apply,one_mul] using h
  rw [hp,← C.pairingEvaluationVector_pair,C.pairingEvaluationVector_integral,
    hodgeRegularization_symmetric]
  have he := congrArg (fun T : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true => T f)
    (hodgeSpectralHeat_factor A J α hs ht D hD ρ hρ)
  change hodgeSpectralHeat A J α hs ht D hD (ρ^2) f =
    hodgeRegularization A J α hs ht ρ (hodgeHeatBoost A J α hs ht D hD ρ f) at he
  rw [← he]
  exact (hodgeSpectralHeat_symmetric A J α hs ht D hD (ρ^2) _ _).symm

def pairingGammaTail (T : ℝ) (hT : 0 ≤ T) (r : ℝ)
    (a b : PreL2 A J α hs ht true) (x y : X) : ℝ :=
  ⟪C.pairingHeatVector b x,
    hodgeGammaShift A J α hs ht D hD T hT r (2*ρ^2) (C.pairingHeatVector a y)⟫

lemma pairingGammaTail_continuous (T : ℝ) (hT : 0 ≤ T) (r : ℝ)
    (a b : PreL2 A J α hs ht true) :
    Continuous (fun p : X × X => C.pairingGammaTail T hT r a b p.1 p.2) :=
  ((C.pairingHeatVector_continuous b).comp continuous_fst).inner
    ((hodgeGammaShift A J α hs ht D hD T hT r (2*ρ^2)).continuous.comp
      ((C.pairingHeatVector_continuous a).comp continuous_snd))

lemma pairingGammaTail_integral (T : ℝ) (hT : 0 ≤ T) (r : ℝ) (hr : 0 < r)
    (hρT : 2*ρ^2 ≤ T) (a b : PreL2 A J α hs ht true) :
    (∫ x, ∫ y, C.pairingGammaTail T hT r a b x y
      ∂geometricVolume A J α ∂geometricVolume A J α) =
      ⟪hodgeGammaTailAction A J α hs ht D hD T r (smoothL2 A J α hs ht true a),
        smoothL2 A J α hs ht true b⟫ := by
  let K := hodgeGammaShift A J α hs ht D hD T hT r (2*ρ^2)
  have ha := C.pairingHeatVector_integrable a
  have hb := C.pairingHeatVector_integrable b
  have hi := K.integrable_comp ha
  have hp := (innerSL ℝ (∫ y, K (C.pairingHeatVector a y) ∂geometricVolume A J α)).integral_comp_comm hb
  simp only [innerSL_apply_apply] at hp
  have he : (∫ x, ∫ y, C.pairingGammaTail T hT r a b x y
      ∂geometricVolume A J α ∂geometricVolume A J α) =
      ⟪∫ x, C.pairingHeatVector b x ∂geometricVolume A J α,
        K (∫ y, C.pairingHeatVector a y ∂geometricVolume A J α)⟫ := by
    rw [← K.integral_comp_comm ha,real_inner_comm,← hp]
    apply integral_congr_ae
    filter_upwards [] with x
    have h := (innerSL ℝ (C.pairingHeatVector b x)).integral_comp_comm hi
    simpa only [innerSL_apply_apply,pairingGammaTail,real_inner_comm,K] using h
  rw [he,C.pairingHeatVector_integral,C.pairingHeatVector_integral,
    ← hodgeGammaTailAction_factor_pair A J α hs ht D hD hT hr hρT,real_inner_comm]

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
