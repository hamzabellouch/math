import Mathlib
import OAI.Probability.Ballisticity.Stationary.ArrayFiniteClasses
import OAI.Probability.Ballisticity.Estimates.ClassFinset

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace DirectionalTransience
lemma stationary_nat_monotone {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (N : Ω → ℕ) (hm : Measurable N) (hle : ∀ᵐ ω ∂μ, N ω≤N (T ω)) :
    ∀ᵐ ω ∂μ, N (T ω)=N ω := by
  let f := fun ω => (1:ℝ)/((N ω:ℝ)+1)
  have hfm : Measurable f := measurable_const.div (((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp hm).add_const 1)
  have hfi : Integrable f μ := by
    apply Integrable.mono' (integrable_const (1:ℝ)) hfm.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (by dsimp [f]; positivity)]
    exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (N ω) (α:=ℝ); linarith)
  have hcomp : Integrable (fun ω => f (T ω)) μ := (hT.integrable_comp hfm.aestronglyMeasurable).mpr hfi
  have hfl : ∀ᵐ ω ∂μ, f (T ω)≤f ω := by
    filter_upwards [hle] with ω hω
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hω 1)
  have hF : (fun ω => f (T ω))=ᵐ[μ] f :=
    (integral_eq_iff_of_ae_le hcomp hfi hfl).mp (by rw [←integral_map hT.measurable.aemeasurable hfm.aestronglyMeasurable,hT.map_eq])
  filter_upwards [hF] with ω hω
  have hh : (N (T ω):ℝ)+1=(N ω:ℝ)+1 := inv_inj.mp (by simpa only [f,one_div] using hω)
  exact_mod_cast (add_right_cancel hh : (N (T ω):ℝ)=(N ω:ℝ))
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def arrayClassFinset {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e) : Finset ℕ :=
  currentClassFinset e (arrayCurrentData e i Y)
lemma arrayClassFinset_measurable {d : ℕ} (e : Direction d) (i : ℤ) : Measurable (arrayClassFinset e i) :=
  (currentClassFinset_measurable e).comp (arrayCurrentData_measurable e i)
lemma arrayClassFinset_shift {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e) :
    arrayClassFinset e i (StationaryCompact.shift Y)=arrayClassFinset e (i+1) Y := rfl

noncomputable def arrayLink {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e) (a : ℕ) : ℕ :=
  if h : ∃ b, ArrayRelated e Y (i,a) (i+1,b) then Nat.find h else 0

lemma arrayLink_measurable {d : ℕ} (e : Direction d) (i : ℤ) (a : ℕ) :
    Measurable (fun Y => arrayLink e i Y a) := by
  have hm : MeasurableSet {Y | ∃ b, ArrayRelated e Y (i,a) (i+1,b)} := by
    simpa only [Set.ofPred_exists] using MeasurableSet.iUnion fun b => arrayRelated_measurable e (i,a) (i+1,b)
  unfold arrayLink
  apply Measurable.dite (s := {Y | ∃ b, ArrayRelated e Y (i,a) (i+1,b)})
    (f := fun Y => Nat.find Y.property) (g := fun _ => 0)
  · exact measurable_find (fun Y : {Y | ∃ b, ArrayRelated e Y (i,a) (i+1,b)} => Y.property)
      (fun b => (arrayRelated_measurable e (i,a) (i+1,b)).preimage measurable_subtype_coe)
  · exact measurable_const
  · exact hm

lemma arrayLink_related {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e) (a : ℕ)
    (h : ∃ b, ArrayRelated e Y (i,a) (i+1,b)) :
    ArrayRelated e Y (i,a) (i+1,arrayLink e i Y a) := by
  rw [arrayLink,dite_eq_left h]
  exact Nat.find_spec h

noncomputable def arrayTransport {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e) (a : ℕ) : ℕ :=
  ReferenceClasses.representative (arrayCurrentData e (i+1) Y).1 (arrayLink e i Y a)

lemma arrayTransport_measurable {d : ℕ} (e : Direction d) (i : ℤ) (a : ℕ) :
    Measurable (fun Y => arrayTransport e i Y a) := by
  exact (measurable_from_prod_countable_left (f := fun p : ActualEpisodeArray e × ℕ =>
    ReferenceClasses.representative (arrayCurrentData e (i+1) p.1).1 p.2)
      (fun b => (ReferenceClasses.measurable_representative b).comp
        (arrayCurrentData_measurable e (i+1)).fst)).comp
    (measurable_id.prodMk (arrayLink_measurable e i a))

lemma arrayTransport_related {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e)
    (ho : ArrayOffsetsConsistent e Y) (a : ℕ) (h : ∃ b, ArrayRelated e Y (i,a) (i+1,b)) :
    ArrayRelated e Y (i,a) (i+1,arrayTransport e i Y a) := by
  apply arrayRelated_trans e Y ho (arrayLink_related e i Y a h)
  apply (arrayRelated_current e Y ho (i+1) _ _).mp
  exact ReferenceClasses.related_symm (ReferenceClasses.representative_related _ _)

lemma arrayTransport_mem {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e)
    (hf : CurrentFiniteClasses e (arrayCurrentData e (i+1) Y)) (a : ℕ) :
    arrayTransport e i Y a∈arrayClassFinset e (i+1) Y :=
  currentClassFinset_rep_mem e _ hf _

lemma arrayTransport_injOn {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e)
    (ho : ArrayOffsetsConsistent e Y) (hf : CurrentFiniteClasses e (arrayCurrentData e i Y))
    (hs : ∀ a, ∃ b, ArrayRelated e Y (i,a) (i+1,b)) :
    Set.InjOn (arrayTransport e i Y) (arrayClassFinset e i Y) := by
  intro a ha b hb hab
  have ha' := arrayTransport_related e i Y ho a (hs a)
  rw [hab] at ha'
  have hr := arrayRelated_trans e Y ho ha'
    (arrayRelated_symm e Y ho (arrayTransport_related e i Y ho b (hs b)))
  have hh : ReferenceClasses.related (arrayCurrentData e i Y).1 a b :=
    (arrayRelated_current e Y ho i a b).mpr (by simpa only [hab] using hr)
  have he := (ReferenceClasses.representative_eq_iff _ a b).mpr hh
  rw [(currentClassFinset_mem e _ hf a).mp ha,(currentClassFinset_mem e _ hf b).mp hb] at he
  exact he

lemma arrayClassFinset_card_le {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e)
    (ho : ArrayOffsetsConsistent e Y) (hf : ∀ i, CurrentFiniteClasses e (arrayCurrentData e i Y))
    (hs : ∀ a, ∃ b, ArrayRelated e Y (i,a) (i+1,b)) :
    (arrayClassFinset e i Y).card≤(arrayClassFinset e (i+1) Y).card := by
  calc
    _ = ((arrayClassFinset e i Y).image (arrayTransport e i Y)).card :=
      (Finset.card_image_iff.mpr (arrayTransport_injOn e i Y ho (hf i) hs)).symm
    _ ≤ _ := Finset.card_le_card (by
      intro b hb
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
      exact arrayTransport_mem e i Y (hf (i+1)) a)

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

lemma class_card_constant (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) :
    ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), Y∈G.event → ∀ i,
      (arrayClassFinset e (i+1) Y).card=(arrayClassFinset e i Y).card := by
  let N := fun Y => if Y∈G.event then (arrayClassFinset e 0 Y).card else 0
  have hm : Measurable N := Measurable.ite G.measurable_event
    ((measurable_of_countable Finset.card).comp (arrayClassFinset_measurable e 0)) measurable_const
  have hf := L.finite_classes_all_times hue htrans G
  have hle : ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), N Y≤N (StationaryCompact.shift Y) := by
    filter_upwards [L.consistent,L.sampling,L.elliptic,L.continuation,L.finite_marks,G.no_dust,hf,G.invariant]
      with Y hO hs he hc hm hd hf hi
    by_cases hY : Y∈G.event
    · simp only [N,ite_eq_left hY,ite_eq_left (hi.mpr hY),arrayClassFinset_shift]
      exact arrayClassFinset_card_le e 0 Y hO.1 (hf hY)
        (array_forward_survives e Y hs L.κ L.κ_pos he hc (fun i => ⟨(hm i).1,(hm i).2.1⟩) (hd hY) 0)
    · simp only [N,ite_eq_right hY,ite_eq_right (mt hi.mp hY),le_refl]
  have heq := stationary_nat_monotone _ L.preserving N hm hle
  have h0 : ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), Y∈G.event →
      (arrayClassFinset e (0+1) Y).card=(arrayClassFinset e 0 Y).card := by
    filter_upwards [heq,G.invariant] with Y hY hi hy
    simpa only [N,ite_eq_left hy,ite_eq_left (hi.mpr hy),arrayClassFinset_shift] using hY
  have hall := stationary_ae_integer_family _ L.preserving
    (fun i Y => Y∈G.event → (arrayClassFinset e (i+1) Y).card=(arrayClassFinset e i Y).card)
    (fun i => G.measurable_event.imp (measurableSet_eq_fun
      ((measurable_of_countable Finset.card).comp (arrayClassFinset_measurable e (i+1)))
      ((measurable_of_countable Finset.card).comp (arrayClassFinset_measurable e i))))
    (fun i => G.invariant.mono fun Y hi => by rw [hi]; rfl) h0
  filter_upwards [hall] with Y hY hy i
  exact hY i hy

end StationaryArrayLaw
end DirectionalTransience

end

end OAI
