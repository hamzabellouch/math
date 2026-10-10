import OAI.Dynamics.StandardMap.BridgeVague

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma lintegral_le_of_cc_le {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X] [RegularSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (f : X → ℝ) (hf : Continuous f)
    (h0 : ∀ x,0 ≤ f x) (C : ℝ)
    (hb : ∀ g : C_c(X,ℝ),(∀ x,0 ≤ g x) → (∀ x,g x ≤ f x) → (∫ x,g x ∂μ) ≤ C) :
    (∫⁻ x,ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
  have hcompact (K : Set X) (hK : IsCompact K) : ν K ≤ ENNReal.ofReal C := by
    obtain ⟨⟨b,hbc⟩,hbK,hbZ,hbs,hbr⟩ := exists_continuous_one_zero_of_isCompact
      hK isClosed_empty (disjoint_empty K)
    let g : C_c(X,ℝ) := ⟨⟨fun x => b x*f x,hbc.mul hf⟩,hbs.mul_right⟩
    have hg0 : ∀ x,0 ≤ g x := fun x => mul_nonneg (hbr x).1 (h0 x)
    have hgf : ∀ x,g x ≤ f x := fun x => by
      change b x*f x ≤ f x
      exact mul_le_of_le_one_left (h0 x) (hbr x).2
    have hge : ∀ x∈K,g x=f x := by intro x hx; change b x*f x=f x; have he : b x=1 := hbK hx; rw [he]; simp
    have hm : ν K ≤ ∫⁻ x,ENNReal.ofReal (g x) ∂μ := by
      rw [withDensity_apply _ hK.isClosed.measurableSet]
      rw [← lintegral_indicator hK.isClosed.measurableSet]
      apply lintegral_mono
      intro x
      by_cases hx : x∈K
      · simp only [Set.indicator_of_mem hx,hge x hx,le_refl]
      · simp only [Set.indicator_of_notMem hx]; exact bot_le
    have hi : Integrable (fun x => g x) μ := g.continuous.integrable_of_hasCompactSupport (μ := μ) g.hasCompactSupport
    rw [← ofReal_integral_eq_lintegral_ofReal (f := fun x => g x) hi (Eventually.of_forall hg0)] at hm
    exact hm.trans (ENNReal.ofReal_le_ofReal (hb g hg0 hgf))
  let : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => (hcompact K hK).trans_lt ENNReal.ofReal_lt_top⟩
  have hv : ν univ ≤ ENNReal.ofReal C := by
    rw [isOpen_univ.measure_eq_iSup_isCompact ν]
    simp only [iSup_le_iff]
    intro K hKU hK
    exact hcompact K hK
  simpa only [ν,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] using hv
lemma vague_integrable_bound {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X] [RegularSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
    (l : Filter ι) [l.NeBot] (μ : ι → Measure X) [∀ i,IsFiniteMeasureOnCompacts (μ i)]
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    (hconv : ∀ g : C_c(X,ℝ), Tendsto (fun i => ∫ x,g x ∂μ i) l (𝓝 (∫ x,g x ∂ν)))
    (f : X → ℝ) (hf : Continuous f) (h0 : ∀ x,0 ≤ f x) (C : ℝ) (hC : 0 ≤ C)
    (hi : ∀ i,Integrable f (μ i)) (hb : ∀ᶠ i in l,(∫ x,f x ∂μ i)≤C) :
    Integrable f ν ∧ (∫ x,f x ∂ν) ≤ C := by
  have hb' : ∀ g : C_c(X,ℝ),(∀ x,0 ≤ g x) → (∀ x,g x ≤ f x) → (∫ x,g x ∂ν) ≤ C := by
    intro g hg hgf
    apply le_of_tendsto (hconv g)
    filter_upwards [hb] with i hiC
    exact (integral_mono (g.continuous.integrable_of_hasCompactSupport (μ := μ i) g.hasCompactSupport)
      (hi i) hgf).trans hiC
  have hbL := lintegral_le_of_cc_le ν f hf h0 C hb'
  have hif : HasFiniteIntegral f ν := (hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)).mpr
    (hbL.trans_lt ENNReal.ofReal_lt_top)
  have hiv : Integrable f ν := ⟨hf.aestronglyMeasurable,hif⟩
  refine ⟨hiv,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hiv (Eventually.of_forall h0)] at hbL
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hbL
end StandardMapEntropy

end OAI
