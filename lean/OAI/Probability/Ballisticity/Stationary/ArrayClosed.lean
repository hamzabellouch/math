import Mathlib
import OAI.Probability.Ballisticity.Geometry.WindowProjection
import OAI.Probability.Ballisticity.Estimates.OccupationSampling

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma closed_support_weak_limit {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [HasOuterApproxClosed X]
    (μ : ℕ → ProbabilityMeasure X) (ρ : ProbabilityMeasure X)
    (hlim : Tendsto μ atTop (𝓝 ρ)) (s : Set X) (hs : IsClosed s)
    (hμ : ∀ n, ∀ᵐ x ∂(μ n : Measure X), x∈s) :
    ∀ᵐ x ∂(ρ : Measure X), x∈s := by
  have he (n : ℕ) : (μ n : Measure X) s=1 :=
    (mem_ae_iff_prob_eq_one hs.measurableSet).mp (hμ n)
  have hle := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hs
  simp only [he,limsup_const] at hle
  exact (mem_ae_iff_prob_eq_one hs.measurableSet).mpr
    (le_antisymm prob_le_one hle)

lemma actualOccupation_ae_of_invariant {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) (N : ℕ) (M : Environment d → ℕ)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ)
    (s : Set (ActualEpisodeArray e)) (hs : MeasurableSet s)
    (ha : ∀ X, actualArrayMap e t J X∈s)
    (hshift : ∀ Y∈s, StationaryCompact.shift Y∈s) :
    ∀ᵐ Y ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)), Y∈s := by
  have hiter (i : ℕ) (X : EpisodeInput e) :
      StationaryCompact.shift^[i] (actualArrayMap e t J X)∈s := by
    induction i with
    | zero => exact ha X
    | succ i hi =>
      rw [Function.iterate_succ_apply']
      exact hshift _ hi
  have hraw : ∀ᵐ Y ∂actualOccupationRaw e ν Q t J ht N M, Y∈s := by
    unfold actualOccupationRaw StationaryCompact.episodeOccupationRaw
    rw [ae_finsetSum_measure_iff]
    intro i _
    apply (ae_map_iff ((StationaryCompact.shift_continuous.measurable.iterate i).comp
      (actualArrayMap_measurable e t J ht hJ)).aemeasurable hs).mpr
    exact Filter.Eventually.of_forall (hiter i)
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let ρ : FiniteMeasure (ActualEpisodeArray e) := ⟨actualOccupationRaw e ν Q t J ht N M,inferInstance⟩
  have hn : ρ≠0 := by
    intro hz
    have hh : (actualOccupationRaw e ν Q t J ht N M).real Set.univ=0 := by
      change (ρ : Measure (ActualEpisodeArray e)).real Set.univ=0
      rw [hz]
      simp
    linarith
  change ∀ᵐ Y ∂(ρ.normalize : Measure (ActualEpisodeArray e)), Y∈s
  rw [ρ.toMeasure_normalize_eq_of_nonzero hn]
  exact Measure.ae_smul_measure hraw _

noncomputable def currentOffsets {d : ℕ} (e : Direction d) (j : ℤ)
    (Y : ActualEpisodeArray e) : ReferenceClasses.Offsets (HorizontalSpace e) :=
  fun p => Y.2.1 ((j,p.1),(j,p.2))

lemma currentOffsets_continuous {d : ℕ} (e : Direction d) (j : ℤ) :
    Continuous (currentOffsets e j) := by
  unfold currentOffsets
  fun_prop

lemma currentOffsets_closed {d : ℕ} (e : Direction d) :
    IsClosed {Y : ActualEpisodeArray e | ∀ j, ReferenceClasses.Consistent (currentOffsets e j Y)} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun j => ReferenceClasses.consistent_closed.preimage
    (currentOffsets_continuous e j)

lemma actual_currentOffsets {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (X : EpisodeInput e) (j : ℤ) :
    ReferenceClasses.Consistent (currentOffsets e j (actualArrayMap e t J X)) := by
  constructor
  · intro a
    simp [currentOffsets,actualArrayMap]
  · intro a b z h
    have he : X.1.2 (j,b)-X.1.2 (j,a)=z := OnePoint.coe_injective h
    change ((X.1.2 (j,a)-X.1.2 (j,b) : HorizontalSpace e):OnePoint (HorizontalSpace e))=((-z : HorizontalSpace e):OnePoint (HorizontalSpace e))
    rw [←he,neg_sub]
  · intro a b c z w h₁ h₂
    have h₁ : X.1.2 (j,b)-X.1.2 (j,a)=z := OnePoint.coe_injective h₁
    have h₂ : X.1.2 (j,c)-X.1.2 (j,b)=w := OnePoint.coe_injective h₂
    change ((X.1.2 (j,c)-X.1.2 (j,a) : HorizontalSpace e):OnePoint (HorizontalSpace e))=((z+w : HorizontalSpace e):OnePoint (HorizontalSpace e))
    rw [←h₁,←h₂]
    congr 1
    abel

lemma actualOccupation_currentOffsets {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) (N : ℕ) (M : Environment d → ℕ)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ) :
    ∀ᵐ Y ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)),
      ∀ j, ReferenceClasses.Consistent (currentOffsets e j Y) := by
  apply actualOccupation_ae_of_invariant e ν Q t J ht hJ N M hpos _
    (currentOffsets_closed e).measurableSet (actual_currentOffsets e t J)
  intro Y hY j
  exact hY (j+1)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal Classical
namespace DirectionalTransience

abbrev AmbientCurrentWindow {d : ℕ} (e : Direction d) :=
  (ReferenceClasses.Offsets (HorizontalSpace e) × CurrentProfiles e) ×
    ReferenceClasses.AllFields (HorizontalSpace e) (Row d)

instance currentOffsets_secondCountable {d : ℕ} (e : Direction d) :
    SecondCountableTopology (ReferenceClasses.Offsets (HorizontalSpace e)) := inferInstance
instance currentData_secondCountable {d : ℕ} (e : Direction d) :
    SecondCountableTopology (ReferenceClasses.Data (HorizontalSpace e)) :=
  Subtype.secondCountableTopology {O : ReferenceClasses.Offsets (HorizontalSpace e) | ReferenceClasses.Consistent O}
instance currentProfiles_secondCountable {d : ℕ} (e : Direction d) :
    SecondCountableTopology (CurrentProfiles e) := inferInstance
instance currentFields_secondCountable {d : ℕ} (e : Direction d) :
    SecondCountableTopology (ReferenceClasses.AllFields (HorizontalSpace e) (Row d)) := inferInstance
instance ambientCurrentWindow_borel {d : ℕ} (e : Direction d) :
    BorelSpace (AmbientCurrentWindow e) := inferInstance
instance currentWindow_borel {d : ℕ} (e : Direction d) :
    BorelSpace (CurrentWindow e) := inferInstance

def currentWindowInclude {d : ℕ} (e : Direction d) (W : CurrentWindow e) : AmbientCurrentWindow e :=
  ((W.1.1.1,W.1.2),W.2)

lemma currentWindowInclude_continuous {d : ℕ} (e : Direction d) :
    Continuous (currentWindowInclude e) := by unfold currentWindowInclude; fun_prop

lemma currentWindowInclude_injective {d : ℕ} (e : Direction d) :
    Function.Injective (currentWindowInclude e) := by
  intro W W' h
  have h1 : W.1.1.1=W'.1.1.1 := congrArg (fun p => p.1.1) h
  have h2 : W.1.2=W'.1.2 := congrArg (fun p => p.1.2) h
  have h3 : W.2=W'.2 := congrArg (fun p => p.2) h
  exact Prod.ext (Prod.ext (Subtype.ext h1) h2) h3

noncomputable def currentArrayWindow {d : ℕ} (e : Direction d) (j : ℤ) (m : ℕ)
    (Y : ActualEpisodeArray e) : AmbientCurrentWindow e :=
  ((currentOffsets e j Y,fun p => Y.2.2.1 (j,(j,p.1),p.2)),
    fun p => Y.2.2.2 (j,m,p.1,p.2.1,p.2.2))

lemma currentArrayWindow_continuous {d : ℕ} (e : Direction d) (j : ℤ) (m : ℕ) :
    Continuous (currentArrayWindow e j m) := by
  unfold currentArrayWindow currentOffsets
  fun_prop

lemma currentArrayWindow_actual {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (j : ℤ) (m : ℕ) (X : EpisodeInput e) :
    currentArrayWindow e j m (actualArrayMap e t J X) =
      currentWindowInclude e (actualCurrentWindow e t j m X) := rfl

lemma currentArrayWindow_shift {d : ℕ} (e : Direction d) (j : ℤ) (m : ℕ)
    (Y : ActualEpisodeArray e) :
    currentArrayWindow e j m (StationaryCompact.shift Y) = currentArrayWindow e (j+1) m Y := rfl

lemma currentArrayWindow_iterate {d : ℕ} (e : Direction d) (j : ℤ) (m i : ℕ)
    (Y : ActualEpisodeArray e) :
    currentArrayWindow e j m (StationaryCompact.shift^[i] Y) = currentArrayWindow e (j+i) m Y := by
  induction i generalizing Y with
  | zero => simp
  | succ i hi =>
    rw [Function.iterate_succ_apply,hi,currentArrayWindow_shift]
    simp only [Nat.cast_add,Nat.cast_one,add_assoc]

noncomputable def typedCurrentArrayWindow {d : ℕ} (e : Direction d) (j : ℤ) (m : ℕ)
    (Y : ActualEpisodeArray e) : CurrentWindow e :=
  ((if h : ReferenceClasses.Consistent (currentOffsets e j Y) then
      ⟨currentOffsets e j Y,h⟩ else ReferenceClasses.anchorOffsets (fun _ => 0),
    (currentArrayWindow e j m Y).1.2),(currentArrayWindow e j m Y).2)

lemma typedCurrentArrayWindow_measurable {d : ℕ} (e : Direction d) (j : ℤ) (m : ℕ) :
    Measurable (typedCurrentArrayWindow e j m) := by
  have hs : MeasurableSet {Y : ActualEpisodeArray e | ReferenceClasses.Consistent (currentOffsets e j Y)} :=
    (ReferenceClasses.consistent_closed.preimage (currentOffsets_continuous e j)).measurableSet
  have ho : Measurable (fun Y : ActualEpisodeArray e =>
    if h : ReferenceClasses.Consistent (currentOffsets e j Y) then
      (⟨currentOffsets e j Y,h⟩ : ReferenceClasses.Data (HorizontalSpace e))
    else ReferenceClasses.anchorOffsets (fun _ => 0)) := by
    apply (MeasurableEmbedding.subtype_coe ReferenceClasses.consistent_closed.measurableSet).measurable_comp_iff.mp
    simp only [Function.comp_def,apply_dite]
    change Measurable (fun Y => if ReferenceClasses.Consistent (currentOffsets e j Y) then
      currentOffsets e j Y else (ReferenceClasses.anchorOffsets (fun _ : ℕ => (0 : HorizontalSpace e))).1)
    exact Measurable.ite hs (currentOffsets_continuous e j).measurable measurable_const
  exact (ho.prodMk ((currentArrayWindow_continuous e j m).measurable.fst.snd)).prodMk
    (currentArrayWindow_continuous e j m).measurable.snd

lemma currentWindowInclude_typed {d : ℕ} (e : Direction d) (j : ℤ) (m : ℕ)
    (Y : ActualEpisodeArray e) (h : ReferenceClasses.Consistent (currentOffsets e j Y)) :
    currentWindowInclude e (typedCurrentArrayWindow e j m Y) = currentArrayWindow e j m Y := by
  simp only [typedCurrentArrayWindow,dite_eq_left h,currentWindowInclude,currentArrayWindow]

lemma typedCurrentArrayWindow_actual {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (j : ℤ) (m : ℕ) (X : EpisodeInput e) :
    typedCurrentArrayWindow e j m (actualArrayMap e t J X) = actualCurrentWindow e t j m X := by
  apply currentWindowInclude_injective e
  rw [currentWindowInclude_typed e j m _ (actual_currentOffsets e t J X j),currentArrayWindow_actual]

end DirectionalTransience

end

end OAI
