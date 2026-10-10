import Mathlib
import OAI.Probability.Ballisticity.Stationary.ArrayFull
import OAI.Probability.Ballisticity.Walk.UniformFinsetKernel

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DirectionalTransience

lemma preserving_cond {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {T : A → A} (hT : MeasurePreserving T μ μ) (E : Set A) (hE : MeasurableSet E)
    (hi : ∀ᵐ a ∂μ, T a∈E ↔ a∈E) : MeasurePreserving T μ[|E] μ[|E] := by
  have he : μ.restrict (T ⁻¹' E)=μ.restrict E := Measure.restrict_congr_set (hi.mono fun a ha => propext ha)
  have h := hT.restrict_preimage hE
  rw [he] at h
  exact h.smul_measure (μ E)⁻¹

lemma preserving_marking {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) [SFinite μ] {T : A → A} (hT : MeasurePreserving T μ μ)
    (K : Kernel A B) [IsSFiniteKernel K] (f : A × B → B) (hf : Measurable f)
    (he : ∀ᵐ a ∂μ, (K a).map (fun b => f (a,b))=K (T a)) :
    MeasurePreserving (fun p : A × B => (T p.1,f p)) (μ.compProd K) (μ.compProd K) := by
  have hm : Measurable (fun p : A × B => (T p.1,f p)) := (hT.measurable.comp measurable_fst).prodMk hf
  refine ⟨hm,?_⟩
  ext s hs
  rw [Measure.map_apply hm hs,Measure.compProd_apply (hs.preimage hm),Measure.compProd_apply hs]
  calc
    (∫⁻ a, K a (Prod.mk a ⁻¹' ((fun p : A × B => (T p.1,f p)) ⁻¹' s)) ∂μ) =
        ∫⁻ a, K (T a) (Prod.mk (T a) ⁻¹' s) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [he] with a ha
      rw [←ha,Measure.map_apply (show Measurable (fun b => f (a,b)) from hf.comp measurable_prodMk_left) (hs.preimage measurable_prodMk_left)]
      rfl
    _ = _ := hT.lintegral_comp (Kernel.measurable_kernel_prodMk_left hs)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

noncomputable def currentClassKernel {d : ℕ} (e : Direction d) : Kernel (CurrentData e) ℕ :=
  uniformFinsetKernel (currentClassFinset e) (currentClassFinset_measurable e) (currentClassFinset_nonempty e)
instance currentClassKernel_markov {d : ℕ} (e : Direction d) : IsMarkovKernel (currentClassKernel e) := by
  unfold currentClassKernel; infer_instance

noncomputable def arrayClassKernel {d : ℕ} (e : Direction d) (i : ℤ) : Kernel (ActualEpisodeArray e) ℕ :=
  (currentClassKernel e).comap (arrayCurrentData e i) (arrayCurrentData_measurable e i)
instance arrayClassKernel_markov {d : ℕ} (e : Direction d) (i : ℤ) : IsMarkovKernel (arrayClassKernel e i) := by
  unfold arrayClassKernel; infer_instance

abbrev MarkedArray {d : ℕ} (e : Direction d) := ActualEpisodeArray e × ℕ
noncomputable def markedShift {d : ℕ} (e : Direction d) (p : MarkedArray e) : MarkedArray e :=
  (StationaryCompact.shift p.1,arrayTransport e 0 p.1 p.2)
lemma markedShift_measurable {d : ℕ} (e : Direction d) : Measurable (markedShift e) := by
  exact ((StationaryCompact.shift_continuous).measurable.comp measurable_fst).prodMk
    (measurable_from_prod_countable_left (arrayTransport_measurable e 0))

noncomputable def markedArrayLaw {d : ℕ} (e : Direction d) (μ : Measure (ActualEpisodeArray e))
    (E : Set (ActualEpisodeArray e)) : Measure (MarkedArray e) := μ[|E].compProd (arrayClassKernel e 0)

lemma markedArrayLaw_probability {d : ℕ} (e : Direction d) (μ : Measure (ActualEpisodeArray e))
    [IsProbabilityMeasure μ] (E : Set (ActualEpisodeArray e)) (hE : μ E≠0) :
    IsProbabilityMeasure (markedArrayLaw e μ E) := by
  have := cond_isProbabilityMeasure hE
  unfold markedArrayLaw
  infer_instance

lemma markedArrayLaw_fst {d : ℕ} (e : Direction d) (μ : Measure (ActualEpisodeArray e))
    [IsProbabilityMeasure μ] (E : Set (ActualEpisodeArray e)) :
    (markedArrayLaw e μ E).fst=μ[|E] := Measure.fst_compProd _ _

lemma markedArrayLaw_ae {d : ℕ} (e : Direction d) (μ : Measure (ActualEpisodeArray e))
    [IsProbabilityMeasure μ] (E : Set (ActualEpisodeArray e)) (hE : MeasurableSet E)
    {P : ActualEpisodeArray e → Prop} (hP : ∀ᵐ Y ∂μ, Y∈E → P Y) :
    ∀ᵐ p ∂markedArrayLaw e μ E, P p.1 := by
  have h : ∀ᵐ Y ∂μ[|E], P Y := by
    filter_upwards [(show μ[|E]≪μ from cond_absolutelyContinuous).ae_le hP,ae_cond_mem hE] with Y hY hy
    exact hY hy
  have hp : MeasurePreserving Prod.fst (markedArrayLaw e μ E) μ[|E] :=
    ⟨measurable_fst,markedArrayLaw_fst e μ E⟩
  exact hp.quasiMeasurePreserving.ae h

lemma markedArrayLaw_supported {d : ℕ} (e : Direction d) (μ : Measure (ActualEpisodeArray e))
    [IsProbabilityMeasure μ] (E : Set (ActualEpisodeArray e)) :
    ∀ᵐ p ∂markedArrayLaw e μ E, p.2∈arrayClassFinset e 0 p.1 := by
  apply (Measure.ae_compProd_iff ?_).mpr
  · exact ae_of_all _ fun Y => uniformFinsetKernel_supported (currentClassFinset e)
      (currentClassFinset_measurable e) (currentClassFinset_nonempty e) (arrayCurrentData e 0 Y)
  · exact measurableSet_setOfPred.mpr (by
      apply measurable_from_prod_countable_left
      intro a
      exact (measurable_finset_iff.mp (arrayClassFinset_measurable e 0)) a)

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

lemma marked_preserving (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) :
    MeasurePreserving (markedShift e) (markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event)
      (markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event) := by
  apply preserving_marking _ (preserving_cond _ L.preserving G.event G.measurable_event G.invariant)
    (arrayClassKernel e 0) (fun p => arrayTransport e 0 p.1 p.2)
    (measurable_from_prod_countable_left (arrayTransport_measurable e 0))
  have h : ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), Y∈G.event →
      ((arrayClassKernel e 0) Y).map (arrayTransport e 0 Y)=
        (arrayClassKernel e 0) (StationaryCompact.shift Y) := by
    filter_upwards [L.consistent,L.sampling,L.elliptic,L.continuation,L.finite_marks,
      G.no_dust,L.finite_classes_all_times hue htrans G,L.class_card_constant hue htrans G]
      with Y hO hs he hc hm hd hf hcard hY
    have hsurv := array_forward_survives e Y hs L.κ L.κ_pos he hc
      (fun j => ⟨(hm j).1,(hm j).2.1⟩) (hd hY) 0
    exact uniformFinset_map (arrayClassFinset e 0 Y) (arrayClassFinset e 1 Y)
      (currentClassFinset_nonempty e _) (currentClassFinset_nonempty e _)
      (arrayTransport e 0 Y) (arrayTransport_injOn e 0 Y hO.1 (hf hY 0) hsurv)
      (by
        apply Finset.coe_injective
        simpa only [Finset.coe_image, zero_add] using congrArg (fun s : Finset ℕ => (s : Set ℕ))
          (arrayTransport_image e 0 Y hO.1 (hf hY) hsurv (hcard hY 0)))
  filter_upwards [(show (L.law : Measure (ActualEpisodeArray e))[|G.event]≪(L.law : Measure (ActualEpisodeArray e)) from cond_absolutelyContinuous).ae_le h,ae_cond_mem G.measurable_event] with Y hY hy
  exact hY hy

end StationaryArrayLaw
end DirectionalTransience

end

end OAI
