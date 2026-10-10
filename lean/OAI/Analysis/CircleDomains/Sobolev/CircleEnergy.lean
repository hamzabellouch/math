import OAI.Analysis.CircleDomains.Sobolev.CovectorMetric
import OAI.Analysis.CircleDomains.Transfer.CoreGeometry

namespace OAI

/-!
# Localized energy for periodic differentials

Agreement of circle maps near the retained core implies agreement of
their intrinsic differentials. Original L² energy controls the entire
unbounded core; smoothness on a compact tail controls the remainder.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem circleGradient_congr_of_eventuallyEq
    {f g : (ℝ × ℝ) → UnitAddCircle} {x : ℝ × ℝ} (hfg : f =ᶠ[𝓝 x] g) :
    circleGradient f x = circleGradient g x := by
  have hx : f x = g x := hfg.self_of_nhds
  have hcut : circleCut f x = circleCut g x := congrArg (fun t => circleRepresentative t - 1 / 2) hx
  have heq : circleBranch f (circleCut f x) =ᶠ[𝓝 x] circleBranch g (circleCut g x) := by
    filter_upwards [hfg] with y hy
    change (AddCircle.equivIco 1 (circleCut f x) (f y) : ℝ) =
      (AddCircle.equivIco 1 (circleCut g x) (g y) : ℝ)
    rw [hy]
    exact congrArg (fun a => (AddCircle.equivIco 1 a (g y) : ℝ)) hcut
  simp only [circleGradient, circleFDeriv, heq.fderiv_eq (𝕜 := ℝ)]

theorem fieldEnergy_spherical (v : (ℝ × ℝ) → ℝ × ℝ) (z : ℝ × ℝ) :
    fieldEnergy v (fun z => sphericalMetricFactor z • 1) z = (v z).1 ^ 2 + (v z).2 ^ 2 := by
  unfold fieldEnergy
  rw [covectorEnergy_eq_matrixEnergy,
    matrixEnergy_pos_smul _ Matrix.PosDef.one (sphericalMetricFactor_pos z),
    ← covectorEnergy_eq_matrixEnergy, covectorEnergy_identity]

theorem integrable_fieldEnergy_spherical_of_memLp
    {μ : Measure (ℝ × ℝ)} {v : (ℝ × ℝ) → ℝ × ℝ} (hv : MemLp v 2 μ) :
    Integrable (fieldEnergy v (fun z => sphericalMetricFactor z • 1)) μ := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp_memLp' hv
  have hy := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp_memLp' hv
  have hxx : MemLp (fun z => (v z).1 * (v z).1) 1 μ := hx.mul hx
  have hyy : MemLp (fun z => (v z).2 * (v z).2) 1 μ := hy.mul hy
  have hi := (memLp_one_iff_integrable.mp hxx).add (memLp_one_iff_integrable.mp hyy)
  exact hi.congr (Eventually.of_forall fun z => by
    simpa only [pow_two, Pi.add_apply] using (fieldEnergy_spherical v z).symm)

theorem integrableOn_fieldEnergy_with_cofinite_core
    {Ω Q G K : Set (ℝ × ℝ)} (hQ : IsClosed Q) (hQΩ : Q ⊆ Ω)
    (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ)) (hKG : K ⊆ G)
    {v w : (ℝ × ℝ) → ℝ × ℝ} (hv : ContinuousOn v Ω)
    (hw : IntegrableOn (fieldEnergy w (fun z => sphericalMetricFactor z • 1)) G)
    (hretain : ∀ z ∈ K, v z = w z) {g : (ℝ × ℝ) → PlanarMetric}
    (hg : Continuous g) (hPD : ∀ z, (g z).PosDef)
    (hmetric : ∀ z ∈ K, g z = sphericalMetricFactor z • 1) :
    IntegrableOn (fieldEnergy v g) Q := by
  obtain ⟨R, _, hQc, htail⟩ := exists_compact_tail_piece hQ hKc
  have ht : IntegrableOn (fieldEnergy v g) (Q \ K) := by
    rw [htail]
    exact (((continuousOn_fieldEnergy hv hg hPD).mono
      (fun z hz => hQΩ hz.1)).integrableOn_compact hQc).mono_set sdiff_subset
  have hc : IntegrableOn (fieldEnergy v g) (Q ∩ K) := by
    apply (hw.mono_set (fun z hz => hKG hz.2)).congr
    filter_upwards [ae_restrict_mem (hQ.measurableSet.inter hK.measurableSet)] with z hz
    simp only [fieldEnergy, hretain z hz.2, hmetric z hz.2]
  simpa only [inter_union_sdiff] using hc.union ht

theorem localized_circle_energy_lt
    {Ω Q G K : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsClosed Q) (hQΩ : Q ⊆ Ω)
    (hG : MeasurableSet G) (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ)) (hKG : K ⊆ G)
    {f u : (ℝ × ℝ) → UnitAddCircle} (hf : SmoothCircleOn f Ω)
    (hu : MemLp (circleGradient u) 2 (volume.restrict G))
    (hretain : f =ᶠ[𝓝ˢ K] u) {g : (ℝ × ℝ) → PlanarMetric}
    (hg : Continuous g) (hPD : ∀ z, (g z).PosDef)
    (hmetric : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1)
    {ε : ℝ} (henergy : (∫ z in Q \ K, fieldEnergy (circleGradient f) g z) < ε)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (hEK : E ⊆ K) :
    (∫ z in Q \ E, fieldEnergy (circleGradient f) g z) <
      (∫ z in G \ E, fieldEnergy (circleGradient u)
        (fun z => sphericalMetricFactor z • 1) z) + ε := by
  have hgrad (z : ℝ × ℝ) (hz : z ∈ K) : circleGradient f z = circleGradient u z :=
    circleGradient_congr_of_eventuallyEq (hretain.filter_mono (nhds_le_nhdsSet hz))
  have hmi (z : ℝ × ℝ) (hz : z ∈ K) : g z = sphericalMetricFactor z • 1 :=
    hmetric.self_of_nhdsSet z hz
  have hfc := (contDiffOn_circleGradient hΩ hf).continuousOn
  have hui := integrable_fieldEnergy_spherical_of_memLp hu
  have hfi := integrableOn_fieldEnergy_with_cofinite_core hQ hQΩ hK hKc hKG
    hfc hui hgrad hg hPD hmi
  apply localized_energy_lt_source hQ.measurableSet hG hK.measurableSet hE hEK
    (fun z hz => hKG hz.2) hfi hui (hfi.mono_set sdiff_subset)
    (fun z _ => covectorEnergy_nonneg _ (Matrix.PosDef.one.smul (sphericalMetricFactor_pos z)))
    ?_ (fun _ _ => le_rfl) henergy
  intro z hz
  simp only [fieldEnergy, hgrad z hz.2, hmi z hz.2]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
