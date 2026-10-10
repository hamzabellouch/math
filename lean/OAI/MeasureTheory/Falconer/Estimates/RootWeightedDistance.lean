import OAI.MeasureTheory.Falconer.Fourier.RootPairSymbols
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal

noncomputable def rootWeightedPair (d e : RootEndpointData) (N : ℕ) (sig : ℝ) :
    Measure (Plane × Plane) :=
  (d.ρ.prod e.ρ).withDensity (fun z => ENNReal.ofReal (rootSpatialWeight d e N sig z))

noncomputable def rootWeightedDistance (d e : RootEndpointData) (N : ℕ) (sig : ℝ) : Measure ℝ :=
  Measure.map (fun z : Plane × Plane => dist z.1 z.2) (rootWeightedPair d e N sig)

theorem rootWeightedPair_le (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ᵐ z ∂d.ρ.prod e.ρ, δ ≤ dist z.1 z.2) :
    rootWeightedPair d e N sig ≤ ENNReal.ofReal (δ^(-(1/2:ℝ))) • d.ρ.prod e.ρ := by
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards [hsep] with z hz
  exact ENNReal.ofReal_le_ofReal (rootSpatialWeight_le d e hd he N sig hδ hz)

theorem rootWeightedPair_isFinite (d e : RootEndpointData) [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (N : ℕ) (sig : ℝ) (hd : 0 < d.Q.side) (he : 0 < e.Q.side) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ᵐ z ∂d.ρ.prod e.ρ, δ ≤ dist z.1 z.2) :
    IsFiniteMeasure (rootWeightedPair d e N sig) := by
  constructor
  apply (Measure.le_iff.mp (rootWeightedPair_le d e N sig hd he hδ hsep) univ MeasurableSet.univ).trans_lt
  rw [Measure.smul_apply,smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem rootWeightedDistance_isFinite (d e : RootEndpointData) [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (N : ℕ) (sig : ℝ) (hd : 0 < d.Q.side) (he : 0 < e.Q.side) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ᵐ z ∂d.ρ.prod e.ρ, δ ≤ dist z.1 z.2) :
    IsFiniteMeasure (rootWeightedDistance d e N sig) := by
  let := rootWeightedPair_isFinite d e N sig hd he hδ hsep
  unfold rootWeightedDistance
  infer_instance

theorem integral_rootWeightedDistance (d e : RootEndpointData)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (N : ℕ) (sig : ℝ)
    (F : ℝ → ℂ) (hF : AEStronglyMeasurable F (rootWeightedDistance d e N sig)) :
    (∫ t, F t ∂rootWeightedDistance d e N sig) =
      ∫ z, rootSpatialWeight d e N sig z • F (dist z.1 z.2) ∂d.ρ.prod e.ρ := by
  rw [rootWeightedDistance,integral_map (by fun_prop) hF,rootWeightedPair]
  calc
    _ = ∫ z, (ENNReal.ofReal (rootSpatialWeight d e N sig z)).toReal • F (dist z.1 z.2) ∂d.ρ.prod e.ρ :=
      integral_withDensity_eq_integral_toReal_smul
        (rootSpatialWeight_measurable d e N sig).ennreal_ofReal
        (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      rw [ENNReal.toReal_ofReal (rootSpatialWeight_nonneg d e hd he N sig z)]

theorem rootWeightedDistance_fourier (d e : RootEndpointData)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (N : ℕ) (sig r : ℝ) :
    charFun (rootWeightedDistance d e N sig) r =
      ∫ z, (rootSpatialWeight d e N sig z : ℂ)*Complex.exp (Complex.I*((r*dist z.1 z.2:ℝ):ℂ))
        ∂d.ρ.prod e.ρ := by
  rw [charFun_apply_real,integral_rootWeightedDistance d e hd he N sig _ (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with z
  simp only [Complex.real_smul,Complex.ofReal_mul]
  ring_nf

theorem rootWeightedDistance_ofOuter (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (m₁ m₂ : ℝ → ℝ) (N : ℕ) (lam₁ lam₂ sig kap : ℝ) (c : ℕ) :
    rootWeightedDistance (RootEndpointData.ofOuter Q₁ ρ m₁ N lam₁ sig kap c)
      (RootEndpointData.ofOuter Q₂ ν m₂ N lam₂ sig kap c) N sig =
      Measure.map (fun z : Plane × Plane => dist z.1 z.2)
        ((ρ.prod ν).withDensity (fun z => ENNReal.ofReal
          ((dist z.1 z.2)^(-(1/2:ℝ)) *
            (outerEndpointMask Q₁ ρ m₁ N lam₁ sig kap c z.1 (sourceRadialUnit z.2 z.1) *
             outerEndpointMask Q₂ ν m₂ N lam₂ sig kap c z.2 (sourceRadialUnit z.2 z.1))))) := rfl

end PlanarFalconer

end OAI
