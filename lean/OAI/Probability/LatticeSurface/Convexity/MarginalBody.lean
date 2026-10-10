import Mathlib
import OAI.Probability.LatticeSurface.Convexity.Concentration
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.DensityOverlap
import OAI.Probability.LatticeSurface.Convexity.DensityPrekopa
import OAI.Probability.LatticeSurface.Convexity.EvenIntegral
import OAI.Probability.LatticeSurface.Convexity.MarginalOverlap
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.Survival
import OAI.Probability.LatticeSurface.Convexity.USCEnvelope
import OAI.Probability.LatticeSurface.Convexity.USCGlobal
import OAI.Probability.LatticeSurface.Convexity.USCMarginal
import OAI.Probability.LatticeSurface.Convexity.USCPrekopa
import OAI.Probability.LatticeSurface.Convexity.USCProduct
import OAI.Probability.LatticeSurface.Convexity.Unimodal
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.CompactOverlap
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

end FacetVolume

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace USCEnvelope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end USCEnvelope

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

open Set Filter

open scoped Topology

noncomputable section

namespace Overlap

end Overlap

namespace USCEnvelope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end USCEnvelope

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

namespace Density

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

end Density

namespace FacetVolume

end FacetVolume

namespace Overlap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

end Overlap

namespace FacetVolume

end FacetVolume

namespace Density

open FacetVolume

end Density

namespace Density

end Density

namespace Density

end Density

namespace Density

end Density

namespace FacetVolume

end FacetVolume

namespace FacetVolume

lemma usc_product_marginal {k m : ℕ} {p : (Fin k → ℝ) × (Fin m → ℝ) → ℝ} {R : ℝ}
    (hR : 0≤R) (hp : UpperSemicontinuous p) (hp0 : ∀ z,0≤p z)
    (hpK : ∀ z,R<‖z‖ → p z=0) :
    UpperSemicontinuous (fun r => ∫ z : Fin m → ℝ,p (r,z)) := by
  let K : Set ((Fin k → ℝ) × (Fin m → ℝ)) := Metric.closedBall 0 R
  have hK : IsCompact K := isCompact_closedBall _ _
  have hne : K.Nonempty := ⟨0,Metric.mem_closedBall_self hR⟩
  have hzero : ∀ z,z∉K → p z=0 := by
    intro z hz;apply hpK;simpa [K,Metric.mem_closedBall,dist_zero_right] using hz
  let F : ℕ → (Fin k → ℝ) → ℝ := fun j r => cubeIntegral
    (fun z => USCEnvelope.envelope K p j (r,z)) (-R) R
  have hF (j : ℕ) : Continuous (F j) := by
    change Continuous (fun r => ∫ z in cube m (-R) R,USCEnvelope.envelope K p j (r,z))
    apply continuous_parametric_integral_of_continuous (s:=cube m (-R) R)
    · exact (USCEnvelope.continuous_envelope hK hp j)
    · exact compact_cube _ _ _
  have hsliceK (r : Fin k → ℝ) : ∀ z,z∉cube m (-R) R → p (r,z)=0 := by
    intro z hz
    apply hpK
    have hn : R<‖z‖ := by
      by_contra h
      apply hz
      exact mem_cube.mpr (fun i => abs_le.mp ((norm_le_pi_norm z i).trans (le_of_not_gt h)))
    exact hn.trans_le (le_max_right ‖r‖ ‖z‖)
  have hsliceI (r : Fin k → ℝ) : Integrable (fun z => p (r,z)) :=
    integrable_usc_compact (hp.comp (continuous_const.prodMk continuous_id))
      (fun z => hp0 _) (hsliceK r)
  have hle (j : ℕ) (r : Fin k → ℝ) : (∫ z,p (r,z))≤F j r := by
    rw [integral_eq_cubeIntegral (hsliceK r)]
    apply setIntegral_mono_on (hsliceI r).integrableOn
      (((USCEnvelope.continuous_envelope hK hp j).comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact (compact_cube _ _ _))
    · exact measurable_cube _ _ _
    · intro z hz
      exact USCEnvelope.le_envelope_global hK hp hne (fun z _ => hp0 z) hzero j _
  obtain ⟨M,hM⟩ := (hp.upperSemicontinuousOn K).bddAbove_of_isCompact hK
  have hlim (r : Fin k → ℝ) : Tendsto (fun j => F j r) atTop (𝓝 (∫ z,p (r,z))) := by
    rw [integral_eq_cubeIntegral (hsliceK r)]
    exact tendsto_integral_of_dominated_convergence (μ:=volume.restrict (cube m (-R) R))
      (fun _ => M)
      (fun j => ((USCEnvelope.continuous_envelope hK hp j).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (continuous_const.continuousOn.integrableOn_compact (compact_cube _ _ _))
      (fun j => Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs,abs_of_nonneg (USCEnvelope.envelope_nonneg hK hp hne (fun z _ => hp0 z) j _)]
        exact USCEnvelope.envelope_bound hK hp hne (fun z _ => hp0 z)
          (fun z hz => hM (mem_image_of_mem p hz)) j _)
      (Eventually.of_forall fun z => USCEnvelope.tendsto_envelope_global hK hp hne hp0 hzero _)
  intro r c hc
  obtain ⟨j,hj⟩ := ((tendsto_order.1 (hlim r)).2 c hc).exists
  filter_upwards [((hF j).continuousAt).preimage_mem_nhds (isOpen_Iio.mem_nhds hj)] with y hy
  exact (hle j y).trans_lt hy

end FacetVolume

namespace RetainedDensity

def density {k m : ℕ} (K : Set ((Fin k → ℝ) × (Fin m → ℝ))) (x : Fin k → ℝ) : ℝ :=
  ∫ z : Fin m → ℝ,K.indicator (fun _ => (1:ℝ)) (x,z)

theorem compact_convex_marginal {k m : ℕ}
    (K : Set ((Fin k → ℝ) × (Fin m → ℝ))) (hK : IsCompact K)
    (hc : Convex ℝ K) (he : ∀ x,x∈K ↔ -x∈K) :
    UpperSemicontinuous (density K) ∧ (∀ x,0≤density K x) ∧
    Density.LogConcave (density K) ∧ (∀ x,density K (-x)=density K x) ∧
    (∃ R : ℝ,0<R ∧ ∀ x,R<‖x‖ → density K x=0) ∧
    (∫ x,density K x)=volume.real K := by
  obtain ⟨R,hKR⟩ := hK.isBounded.subset_closedBall (0 : (Fin k → ℝ) × (Fin m → ℝ))
  let S : ℝ := max 1 R
  have hS : 0<S := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let p : (Fin k → ℝ) × (Fin m → ℝ) → ℝ := K.indicator (fun _ => (1:ℝ))
  have hp : UpperSemicontinuous p := hK.isClosed.upperSemicontinuous_indicator (by norm_num)
  have hp0 (z) : 0≤p z := by
    by_cases hz : z∈K <;> simp [p,hz]
  have hpK (z) (hz : S<‖z‖) : p z=0 := by
    apply Set.indicator_of_notMem
    intro hzK
    have hh := hKR hzK
    have : ‖z‖≤R := by simpa [Metric.mem_closedBall,dist_zero_right] using hh
    exact (not_lt_of_ge (this.trans (le_max_right _ _))) hz
  have hsliceK (r : Fin k → ℝ) (z : Fin m → ℝ) (hz : z∉FacetVolume.cube m (-S) S) : p (r,z)=0 := by
    apply hpK
    have hn : S<‖z‖ := by
      by_contra h
      apply hz
      exact FacetVolume.mem_cube.mpr (fun i => abs_le.mp ((norm_le_pi_norm z i).trans (le_of_not_gt h)))
    exact hn.trans_le (le_max_right ‖r‖ ‖z‖)
  have hlog : Density.LogConcave p := by
    intro x y s t hs ht hst
    by_cases hx : x∈K
    · by_cases hy : y∈K
      · have hc' := hc hx hy hs.le ht.le hst
        simp [p,hx,hy,hc']
      · simp [p,hy,Real.zero_rpow (ne_of_gt ht),hp0]
    · simp [p,hx,Real.zero_rpow (ne_of_gt hs),hp0]
  refine ⟨FacetVolume.usc_product_marginal hS.le hp hp0 hpK,
    fun x => integral_nonneg (fun z => hp0 _),?_,?_,⟨S,hS,?_⟩,?_⟩
  · intro x y s t hs ht hst
    apply FacetVolume.global_usc_prekopa_leindler m
      (hp.comp (continuous_const.prodMk continuous_id))
      (hp.comp (continuous_const.prodMk continuous_id))
      (hp.comp (continuous_const.prodMk continuous_id)) (by linarith : -S<S) hs ht hst
      (fun z => hp0 _) (fun z => hp0 _) (fun z => hp0 _)
      (hsliceK x) (hsliceK y) (hsliceK (s • x+t • y))
    intro z w
    exact hlog (x,z) (y,w) s t hs ht hst
  · intro x
    dsimp [density]
    rw [← integral_neg_eq_self (fun z : Fin m → ℝ => p (-x,z)) volume]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      change K.indicator (fun _ => (1:ℝ)) (-x,-z)=K.indicator (fun _ => (1:ℝ)) (x,z)
      have h := he (x,z)
      simp only [Prod.neg_mk] at h
      by_cases hz : (x,z)∈K
      · rw [Set.indicator_of_mem (h.mp hz),Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem (by simpa only [← h] using hz),Set.indicator_of_notMem hz]
  · intro x hx
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun z => hpK (x,z) (hx.trans_le (le_max_left _ _))
  · have hi : Integrable p := by
      exact (integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet
    change (∫ x,∫ z,p (x,z))=volume.real K
    rw [← integral_prod _ hi]
    exact integral_indicator_one hK.measurableSet

end RetainedDensity

end
end
end

end OAI
