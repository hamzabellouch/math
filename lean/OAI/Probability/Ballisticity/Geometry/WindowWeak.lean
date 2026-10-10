import Mathlib
import OAI.Probability.Ballisticity.Entropy.WindowEntropy
import OAI.Probability.Ballisticity.Estimates.ClosedEmbeddingWeak
import OAI.Probability.Ballisticity.Estimates.ReferenceFeller
import OAI.Probability.Ballisticity.Entropy.EntropyContinuousTests

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory TopologicalSpace Filter
open scoped ENNReal Classical Topology
namespace DirectionalTransience

instance currentDataProfiles_secondCountable {d : ℕ} (e : Direction d) :
    SecondCountableTopology (ReferenceClasses.Data (HorizontalSpace e) × CurrentProfiles e) := inferInstance
instance currentDataProfiles_compact {d : ℕ} (e : Direction d) :
    CompactSpace (ReferenceClasses.Data (HorizontalSpace e) × CurrentProfiles e) := inferInstance
instance currentFields_compact {d : ℕ} (e : Direction d) :
    CompactSpace (ReferenceClasses.AllFields (HorizontalSpace e) (Row d)) := inferInstance
instance currentWindow_compact {d : ℕ} (e : Direction d) : CompactSpace (CurrentWindow e) := inferInstance
instance currentWindow_secondCountable {d : ℕ} (e : Direction d) : SecondCountableTopology (CurrentWindow e) := inferInstance

instance currentWindow_opens {d : ℕ} (e : Direction d) : OpensMeasurableSpace (CurrentWindow e) := inferInstance
instance currentDataProfiles_borel {d : ℕ} (e : Direction d) :
    BorelSpace (ReferenceClasses.Data (HorizontalSpace e) × CurrentProfiles e) := inferInstance
instance currentDataProfiles_opens {d : ℕ} (e : Direction d) :
    OpensMeasurableSpace (ReferenceClasses.Data (HorizontalSpace e) × CurrentProfiles e) := inferInstance

lemma actualCurrentLaw_include {d : ℕ} (e : Direction d) (m : ℕ)
    (L : ProbabilityMeasure (ActualEpisodeArray e))
    (hc : ∀ᵐ Y ∂(L : Measure (ActualEpisodeArray e)), ReferenceClasses.Consistent (currentOffsets e 0 Y)) :
    (actualCurrentLaw e m L).map (currentWindowInclude e) =
      L.map (currentArrayWindow e 0 m) := by
  apply Subtype.ext
  change ((L : Measure _).map (typedCurrentArrayWindow e 0 m)).map (currentWindowInclude e) = _
  rw [Measure.map_map (currentWindowInclude_continuous e).measurable (typedCurrentArrayWindow_measurable e 0 m)]
  apply Measure.map_congr
  filter_upwards [hc] with Y hY
  exact currentWindowInclude_typed e 0 m Y hY

lemma actualCurrentLaw_tendsto {d : ℕ} (e : Direction d) (m : ℕ)
    (Ls : ℕ → ProbabilityMeasure (ActualEpisodeArray e)) (L : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto Ls atTop (𝓝 L))
    (hc : ∀ n, ∀ᵐ Y ∂(Ls n : Measure (ActualEpisodeArray e)), ∀ j, ReferenceClasses.Consistent (currentOffsets e j Y)) :
    Tendsto (fun n => actualCurrentLaw e m (Ls n)) atTop (𝓝 (actualCurrentLaw e m L)) := by
  have hL := closed_support_weak_limit Ls L hlim _ (currentOffsets_closed e) hc
  apply Entropy.tendsto_of_map_closedEmbedding (currentWindowInclude e)
    ((currentWindowInclude_continuous e).isClosedEmbedding (currentWindowInclude_injective e))
  have hi (n : ℕ) := actualCurrentLaw_include e m (Ls n) ((hc n).mono fun _ h => h 0)
  simp_rw [hi,actualCurrentLaw_include e m L (hL.mono fun _ h => h 0)]
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous Ls L hlim
    (currentArrayWindow_continuous e 0 m)

noncomputable def currentReferenceLaw {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (W : ProbabilityMeasure (CurrentWindow e)) :
    ProbabilityMeasure (CurrentWindow e) :=
  Entropy.compProdProb (W.map Prod.fst) (currentWindowReference e ν)

lemma currentReferenceLaw_tendsto {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {I : Type*} {l : Filter I} {Ws : I → ProbabilityMeasure (CurrentWindow e)} {W : ProbabilityMeasure (CurrentWindow e)}
    (h : Tendsto Ws l (𝓝 W)) :
    Tendsto (fun n => currentReferenceLaw e ν (Ws n)) l (𝓝 (currentReferenceLaw e ν W)) := by
  have hK : Continuous (Entropy.kernelProb (currentWindowReference e ν)) :=
    (ReferenceClasses.referenceProb_continuous ν).comp continuous_fst
  exact Entropy.compProdProb_tendsto (currentWindowReference e ν) hK
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous Ws W h continuous_fst)

theorem actualCurrentLaw_kl_weak_limit {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (m : ℕ)
    (Ls : ℕ → ProbabilityMeasure (ActualEpisodeArray e)) (L : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto Ls atTop (𝓝 L))
    (hc : ∀ n, ∀ᵐ Y ∂(Ls n : Measure (ActualEpisodeArray e)), ∀ j, ReferenceClasses.Consistent (currentOffsets e j Y))
    (C : ℝ) (hC : 0≤C)
    (hb : ∀ n, klDiv (actualCurrentLaw e m (Ls n) : Measure (CurrentWindow e))
      (currentReferenceLaw e ν (actualCurrentLaw e m (Ls n)) : Measure (CurrentWindow e)) ≤ ENNReal.ofReal C) :
    klDiv (actualCurrentLaw e m L : Measure (CurrentWindow e))
      (currentReferenceLaw e ν (actualCurrentLaw e m L) : Measure (CurrentWindow e)) ≤ ENNReal.ofReal C := by
  have ht := actualCurrentLaw_tendsto e m Ls L hlim hc
  exact Entropy.kl_le_of_weak_limit _ _ _ _ ht (currentReferenceLaw_tendsto e ν ht) hC (Filter.Eventually.of_forall hb)

end DirectionalTransience

end

end OAI
