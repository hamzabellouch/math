import Mathlib
import OAI.Probability.Ballisticity.Crossings.CommonCutCounting

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

lemma restart_preserves_ae {Ω I : Type*} [MeasurableSpace Ω]
    (μ : I → Measure Ω) (state : Ω → I) (next : Ω → Ω) (good : I → Prop)
    (hn : Measurable next)
    (hrestart : ∀ i, good i → ∀ g : Ω → ℝ≥0∞, Measurable g →
      (∫⁻ ω, g (next ω) ∂μ i) = ∫⁻ ω, (∫⁻ η, g η ∂μ (state (next ω))) ∂μ i)
    (hgood : ∀ i, good i → ∀ᵐ ω ∂μ i, good (state (next ω)))
    (A : Set Ω) (hA : MeasurableSet A)
    (hprob : ∀ i, good i → ∀ᵐ ω ∂μ i, ω ∈ A) (i : I) (hi : good i) :
    ∀ᵐ ω ∂μ i, next ω ∈ A := by
  apply (ae_map_iff hn.aemeasurable hA).mp
  change ∀ᵐ y ∂(μ i).map next, y ∈ A
  rw [ae_iff]
  change (μ i).map next Aᶜ=0
  rw [← lintegral_indicator_one hA.compl]
  change (∫⁻ a, Aᶜ.indicator (fun _ => (1:ℝ≥0∞)) a ∂(μ i).map next)=0
  rw [lintegral_map (measurable_const.indicator hA.compl) hn,
    hrestart i hi _ (measurable_const.indicator hA.compl)]
  apply (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hgood i hi] with ω hω
  rw [lintegral_indicator_const hA.compl,one_mul]
  exact ae_iff.mp (hprob _ hω)

lemma restart_iteration_ae {Ω I : Type*} [MeasurableSpace Ω]
    (μ : I → Measure Ω) (state : Ω → I) (next : Ω → Ω) (good : I → Prop)
    (hn : Measurable next)
    (hrestart : ∀ i, good i → ∀ g : Ω → ℝ≥0∞, Measurable g →
      (∫⁻ ω, g (next ω) ∂μ i) = ∫⁻ ω, (∫⁻ η, g η ∂μ (state (next ω))) ∂μ i)
    (hgood : ∀ i, good i → ∀ᵐ ω ∂μ i, good (state (next ω)))
    (A : Set Ω) (hA : MeasurableSet A)
    (hprob : ∀ i, good i → ∀ᵐ ω ∂μ i, ω ∈ A) (N : ℕ) (i : I) (hi : good i) :
    ∀ᵐ ω ∂μ i, next^[N] ω ∈ A := by
  induction N generalizing i with
  | zero => exact hprob i hi
  | succ N ih =>
    simpa only [Function.iterate_succ_apply, Set.mem_preimage] using
      restart_preserves_ae μ state next good hn hrestart hgood
        ((next^[N]) ⁻¹' A) (hA.preimage (hn.iterate N)) ih i hi

lemma measurableSet_countable_chosen {Ω I : Type*} [MeasurableSpace Ω]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    (state : Ω → I) (hs : Measurable state) (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    MeasurableSet {ω | ω ∈ A (state ω)} := by
  have he : {ω | ω ∈ A (state ω)} = ⋃ i, state ⁻¹' {i} ∩ A i := by
    ext ω
    simp only [Set.mem_iUnion,Set.mem_inter_iff,Set.mem_preimage,Set.mem_singleton_iff,Set.mem_ofPred_eq]
    constructor
    · intro h; exact ⟨state ω,rfl,h⟩
    · rintro ⟨i,hi,h⟩; rwa [hi]
  rw [he]
  exact MeasurableSet.iUnion fun i => ((measurableSet_singleton i).preimage hs).inter (hA i)

lemma measurableSet_validObservation {d : ℕ} (e f : Direction d) (b R : ℝ)
    (K : ℕ) (k : ℝ → ℕ) : MeasurableSet {P | ValidObservation e f b R K k P} := by
  let ℓ := realPosition (step e)
  have hND : MeasurableSet {X : Path d | X ∈ NoDrop ℓ (X 0)} := by
    simpa only [NoDrop,FutureNoDrop,Set.mem_ofPred_eq,Nat.zero_add] using
      (measurableSet_futureNoDrop ℓ 0)
  have hNN : MeasurableSet {X : Path d | ∀ n, ∃ g, X (n+1)=X n+step g} := by
    simp only [Set.ofPred_forall,Set.ofPred_exists]
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun g =>
      measurableSet_eq_fun (measurable_pi_apply _) ((measurable_pi_apply _).add_const _)
  have hsex : MeasurableSet {P : Path d × Path d | ∃ n m,
      selectedBoundaryAt ℓ (observedAdvanceRule e f b K k (pairOrigin P)) P n m} := by
    apply measurableSet_countable_chosen pairOrigin measurable_pairOrigin
      (fun i => {P | ∃ n m, selectedBoundaryAt ℓ (observedAdvanceRule e f b K k i) P n m})
    intro i
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m =>
      selectedMeasurableSet_boundaryAt ℓ (observedAdvanceRule e f b K k i) n m
  have hss : MeasurableSet {P : Path d × Path d |
      selectedBoundaryAt ℓ (observedAdvanceRule e f b K k (pairOrigin P)) P
        (selectedBoundaryTimes ℓ (observedAdvanceRule e f b K k (pairOrigin P)) P).1
        (selectedBoundaryTimes ℓ (observedAdvanceRule e f b K k (pairOrigin P)) P).2} := by
    convert hsex using 1
    ext P
    constructor
    · intro h; exact ⟨_,_,h⟩
    · exact selectedBoundaryTimes_spec ℓ _ P
  have hact : MeasurableSet {P : Path d × Path d | pairGap f (pairOrigin P) < R} :=
    measurableSet_lt ((measurable_of_countable (pairGap f)).comp measurable_pairOrigin) measurable_const
  have hlast : MeasurableSet {P : Path d × Path d | pairGap f (pairOrigin P) < R →
      selectedBoundaryAt ℓ (observedAdvanceRule e f b K k (pairOrigin P)) P
      (selectedBoundaryTimes ℓ (observedAdvanceRule e f b K k (pairOrigin P)) P).1
      (selectedBoundaryTimes ℓ (observedAdvanceRule e f b K k (pairOrigin P)) P).2} := by
    convert hact.compl.union hss using 1
    ext P
    change (_ → _) ↔ (¬_ ∨ _)
    exact imp_iff_not_or
  exact (measurableSet_eq_fun
    ((measurable_of_countable (signedHeight e)).comp ((measurable_pi_apply 0).comp measurable_fst))
    ((measurable_of_countable (signedHeight e)).comp ((measurable_pi_apply 0).comp measurable_snd))).inter
    ((hND.preimage measurable_fst).inter ((hND.preimage measurable_snd).inter
      ((hNN.preimage measurable_fst).inter ((hNN.preimage measurable_snd).inter hlast))))

lemma validObservation_ae {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (b R : ℝ) (K : ℕ) (k : ℝ → ℕ)
    (hK : ∀ i : Lattice d × Lattice d, signedHeight e i.1=signedHeight e i.2 →
      pairGap f i < R → 0 < observedAdvanceBound f b K k i)
    (i : Lattice d × Lattice d) (hi : signedHeight e i.1=signedHeight e i.2) :
    ∀ᵐ P ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2,
      ValidObservation e f b R K k P := by
  let ℓ := realPosition (step e)
  have hp : ∀ᵐ P ∂sharedConditionedPairLaw ν ℓ i.1 i.2,
      pairGap f i < R → selectedBoundaryAt ℓ (observedAdvanceRule e f b K k i) P
        (selectedBoundaryTimes ℓ (observedAdvanceRule e f b K k i) P).1
        (selectedBoundaryTimes ℓ (observedAdvanceRule e f b K k i) P).2 := by
    by_cases ha : pairGap f i < R
    · exact (shared_selectedBoundaryTimes_spec ν hue ℓ (signed_direction_unit e) htrans
        (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e)
        i.1 i.2 hi _ (hK i hi ha) _ (observedAdvanceRule_height e f b K k i)).mono fun P hP _ => hP
    · exact Eventually.of_forall fun _ h => (ha h).elim
  filter_upwards [sharedConditioned_regularPath ν ℓ htrans i.1 i.2,hp] with P hP hsel
  have ho : pairOrigin P=i := Prod.ext hP.1.1.1 hP.2.1.1
  refine ⟨by simpa only [hP.1.1.1,hP.2.1.1] using hi,
    by simpa only [hP.1.1.1] using hP.1.2,
    by simpa only [hP.2.1.1] using hP.2.2,hP.1.1.2.1,hP.2.1.2.1,?_⟩
  simpa only [ho] using hsel

theorem validObservation_iterates_ae {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (b R : ℝ) (K : ℕ) (k : ℝ → ℕ)
    (hK : ∀ i : Lattice d × Lattice d, signedHeight e i.1=signedHeight e i.2 →
      pairGap f i < R → 0 < observedAdvanceBound f b K k i)
    (i : Lattice d × Lattice d) (hi : signedHeight e i.1=signedHeight e i.2) :
    ∀ᵐ P ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2,
      ∀ N, ValidObservation e f b R K k
      ((commonCutObserver (realPosition (step e)) (fun j => pairGap f j < R)
        (observedAdvanceRule e f b K k))^[N] P) := by
  let ℓ := realPosition (step e)
  let μ := fun j : Lattice d × Lattice d => sharedConditionedPairLaw ν ℓ j.1 j.2
  let active := fun j => pairGap f j < R
  let B := observedAdvanceRule e f b K k
  let next := commonCutObserver ℓ active B
  let K' := observedAdvanceBound f b K k
  have hB : ∀ j, active j → ∀ z w, signedHeight e j.1+K' j ≤ signedHeight e z → B j (z,w) :=
    fun j _ => observedAdvanceRule_height e f b K k j
  apply ae_all_iff.mpr
  intro N
  exact restart_iteration_ae μ pairOrigin next
    (fun j => signedHeight e j.1=signedHeight e j.2)
    (measurable_commonCutObserver ℓ active B)
    (fun j hj g hg => commonCutObserver_restart ν hue e htrans active B K' hK hB j hj g hg)
    (fun j hj => commonCutObserver_sameHeight ν hue e htrans active B K' hK hB j hj)
    {P | ValidObservation e f b R K k P} (measurableSet_validObservation e f b R K k)
    (validObservation_ae ν hue e f htrans b R K k hK) N i hi

end DirectionalTransience

end

end

end OAI
