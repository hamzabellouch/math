import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedCollisionBlocks
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianLocalExistence
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyDissipationAverage
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyRegularizationLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticEntropyErrorLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalDissipationBridge

namespace OAI

section

/-! # Entropy with dissipation for a bounded mild cutoff solution -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem bounded_mild_entropy_dissipation (hcarleman : Published.GPV2009CarlemanInput)
    {T q A δ b p : ℝ} (hT : 0 < T) (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hb : 0 ≤ b)
    (hp : 1 < p) (hpi : Integrable (fun v : Velocity => H q v^p))
    {F : Evolution} {a : Density}
    (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t z, 0 ≤ F t z) (hFb : ∀ t z, F t z ≤ A*H q z.2)
    (ham : Measurable a) (han : ∀ z, 0 ≤ a z) (hab : ∀ z, a z ≤ A*H q z.2)
    (hchar : (fun z : ℝ × Phase => F z.1 (TorusFlight.flight z.1 z.2)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod volume]
        (fun z => entropyPath a (TorusFlight.along (cutoffPhysicalSource b F)) z.1 z.2))
    (hcharT : (fun z => F T (TorusFlight.flight T z)) =ᵐ[volume]
      entropyPath a (TorusFlight.along (cutoffPhysicalSource b F)) T) :
    (∫ z, regularizedRelativeEntropyDensity δ (F T) z)-
      (∫ z, regularizedRelativeEntropyDensity δ a z)+regularizedKineticDissipation T b δ F ≤
      (δ*entropyErrorCoefficient q A b)*∫ z : (ℝ × Position) × Velocity,
        logarithmicMajorant q (A+tiltConstant) p δ z.2
        ∂(AnnularEnvelope.timePositionVolume T).prod volume := by
  have hbal := bounded_mild_entropy_balance hcarleman hT hq₁ hq₂ hA hδ hδone hb
    hFm hFn hFb ham han hab hchar hcharT
  have hprod := physical_regularized_entropy_dissipation_bound (T := T) hcarleman hq₁ hq₂ hA
    hδ hδone hb hp hpi hFm hFn hFb
  exact (congrArg (fun x => x+regularizedKineticDissipation T b δ F) hbal).trans_le hprod

end BoltzmannNonuniqueness

end

end

section

/-! # Removing Gaussian regularization from a bounded mild entropy balance -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem bounded_mild_entropy_dissipation_limit (hcarleman : Published.GPV2009CarlemanInput)
    {q b R T : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 < T)
    {E : Evolution} {a : Density}
    (hEm : Measurable (fun z : ℝ × Phase => E z.1 z.2))
    (hEn : ∀ t z, 0 ≤ E t z) (hEb : ∀ t z, E t z ≤ R*H q z.2)
    (ham : Measurable a) (han : ∀ z, 0 ≤ a z) (hab : ∀ z, a z ≤ R*H q z.2)
    (hc : (fun z : ℝ × Phase => E z.1 (TorusFlight.flight z.1 z.2)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod volume]
      (fun z => entropyPath a (TorusFlight.along (cutoffPhysicalSource b E)) z.1 z.2))
    (hcT : (fun z => E T (TorusFlight.flight T z)) =ᵐ[volume]
      entropyPath a (TorusFlight.along (cutoffPhysicalSource b E)) T) :
    ENNReal.ofReal (relativeEntropy (E T))+
      CollisionCompactness.cutoffExtendedDissipation (AnnularEnvelope.timePositionVolume T) b
        (kineticDensity E) ≤ ENNReal.ofReal (relativeEntropy a) := by
  obtain ⟨p,hp,hpi⟩ := exists_integrable_rpow_H hq₁ hq₂
  let μ := AnnularEnvelope.timePositionVolume T
  let g := kineticDensity E
  have hgm : Measurable g := hEm.comp MeasurableEquiv.prodAssoc.measurable
  have hgn : ∀ z, 0 ≤ g z := fun z => hEn _ _
  have hgb : ∀ z, g z ≤ R*H q z.2 := fun z => hEb _ _
  have hHt := regularizedRelativeEntropyDensity_tendsto hq₂ hR hp hpi
    (hEm.comp (measurable_const.prodMk measurable_id)) (hEn T) (hEb T)
  have hAt := regularizedRelativeEntropyDensity_tendsto hq₂ hR hp hpi ham han hab
  have he (f : Density) : (∫ z, scalarRelativeEntropy (maxwellian z.2) (f z)) = relativeEntropy f := by
    unfold relativeEntropy
    apply integral_congr_ae
    filter_upwards [] with z
    exact scalarRelativeEntropy_eq (maxwellian_pos z.2) (f z)
  rw [he] at hHt hAt
  have hnonneg : 0 ≤ relativeEntropy (E T) := by
    rw [← he]
    exact integral_nonneg (fun z => scalarRelativeEntropy_nonneg (maxwellian_pos z.2) (hEn T z))
  have herr := (kinetic_entropy_error_tendsto μ (B := R+tiltConstant)
    (entropyErrorCoefficient q R b) hq₂ hpi).mono_left
      (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hfatou := CollisionCompactness.cutoffExtendedDissipation_regularization_le_liminf μ b hgm hgn
  have heq : (fun δ : ℝ => ENNReal.ofReal (regularizedKineticDissipation T b δ E)) =ᶠ[𝓝[>] 0]
      (fun δ => CollisionCompactness.cutoffExtendedDissipation μ b (gaussianRegularizedDensity δ g)) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hδ
    have hi := (CollisionCompactness.regularized_entropy_dissipation_bound (μ := μ)
      hcarleman hq₁ hq₂ hR hδ.1 hδ.2.le hb hp hpi hgm hgn hgb).1
    have hpos : ∀ z, 0 < gaussianRegularizedDensity δ g z := fun z =>
      add_pos_of_nonneg_of_pos (hgn z) (mul_pos hδ.1 (Real.exp_pos _))
    exact CollisionCompactness.ofReal_integral_positiveCutoffProduction b _ hpos hi
  have hfatou' : CollisionCompactness.cutoffExtendedDissipation μ b g ≤
      liminf (fun δ : ℝ => ENNReal.ofReal (regularizedKineticDissipation T b δ E)) (𝓝[>] 0) := by
    rw [liminf_congr heq]
    exact hfatou
  apply entropy_dissipation_of_vanishing_error hHt hAt herr hnonneg
    (D := fun δ => regularizedKineticDissipation T b δ E)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact regularizedKineticDissipation_nonneg hδ hEn
  · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hδ
    exact bounded_mild_entropy_dissipation hcarleman hT hq₁ hq₂ hR hδ.1 hδ.2.le hb hp hpi
      hEm hEn hEb ham han hab hc hcT
  · exact hfatou'

end BoltzmannNonuniqueness

end

end

end OAI
