import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialCoreInverse
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactWeak

namespace OAI

/-! The constrained inverse has strongly convergent observations for weakly varying inputs. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralRadialCoreInverse_weak_input (R l : ℝ) (hR : 0 < R)
    (F : ℕ → StrongDual ℝ (SpectralRadialPairEnergy R))
    (F₀ : StrongDual ℝ (SpectralRadialPairEnergy R)) (M : ℝ)
    (hF : ∀ n, ‖F n‖ ≤ M)
    (hweak : ∀ L : StrongDual ℝ (SpectralRadialPairEnergy R) →L[ℝ] ℝ,
      Tendsto (fun n => L (F n)) atTop (𝓝 (L F₀))) :
    Tendsto (fun n => spectralRadialObservation R hR (spectralRadialCoreInverse R l (F n)))
      atTop (𝓝 (spectralRadialObservation R hR (spectralRadialCoreInverse R l F₀))) := by
  let J := ((spectralRadialObservation R hR).restrictScalars ℝ).comp
    (spectralRadialCoreSubspace R l).starProjection
  let A : StrongDual ℝ (SpectralRadialPairEnergy R) →L[ℝ] SpectralRadialPairEnergy R :=
    (InnerProductSpace.toDual ℝ (SpectralRadialPairEnergy R)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  change Tendsto (fun n => J (A (F n))) atTop (𝓝 (J (A F₀)))
  have hA (n : ℕ) : ‖A (F n)‖ ≤ M := by
    change ‖(InnerProductSpace.toDual ℝ (SpectralRadialPairEnergy R)).symm (F n)‖ ≤ M
    exact ((InnerProductSpace.toDual ℝ (SpectralRadialPairEnergy R)).symm.norm_map (F n)).le.trans (hF n)
  have hu (n : ℕ) : ‖A (F n)-A F₀‖ ≤ M+‖A F₀‖ := by
    calc
      _ ≤ ‖A (F n)‖+‖A F₀‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add (hA n) le_rfl
  have hw (L : SpectralRadialPairEnergy R →L[ℝ] ℝ) :
      Tendsto (fun n => L (A (F n)-A F₀)) atTop (𝓝 0) := by
    simpa only [map_sub,sub_self,ContinuousLinearMap.comp_apply] using
      (hweak (L.comp A)).sub_const (L (A F₀))
  have hJ : IsCompactOperator J := (spectralRadialObservation_compact R hR).comp_clm
    (spectralRadialCoreSubspace R l).starProjection
  have h := spectralCompact_weakNull (E := SpectralRadialPairEnergy R)
    (F := SpectralRadialObservationSpace R) J hJ
    (fun n => A (F n)-A F₀) (M+‖A F₀‖) hu hw
  have h' := h.add_const (J (A F₀))
  simpa only [map_sub,sub_add_cancel,zero_add] using h'

end DefocusingNLS

end OAI
