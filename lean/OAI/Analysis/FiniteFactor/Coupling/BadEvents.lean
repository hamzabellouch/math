import OAI.Analysis.FiniteFactor.Coupling.Conditioning
import OAI.Analysis.FiniteFactor.Coupling.Order

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal
noncomputable section
namespace CouplingParameters

def eligible (right : Bool) (x u : ℝ) : Prop := if right then u ≤ x else x < u

instance eligible_decidable (right : Bool) (x u : ℝ) : Decidable (eligible right x u) := by
  unfold eligible
  infer_instance

def eligibleIndices {ι : Type*} (right : ι → Bool) (x u : ι → ℝ) (I : Finset ι) : Finset ι :=
  I.filter (fun i => eligible (right i) (x i) (u i))

theorem eligible_measurable (right : Bool) (u : ℝ) : MeasurableSet {x : ℝ | eligible right x u} := by
  cases right
  · exact measurableSet_Iio
  · exact measurableSet_Ici

theorem eligible_count_measurable {ι : Type*} (right : ι → Bool) (u : ι → ℝ) (I : Finset ι) :
    Measurable (fun x : ι → ℝ => (eligibleIndices right x u I).card) := by
  unfold eligibleIndices
  simp_rw [Finset.card_filter]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite ((eligible_measurable (right i) (u i)).preimage (measurable_pi_apply i))
    measurable_const measurable_const

/-- A measurable half of the noncrossing event, with the eligibility count
read from the conditioning vector. Taking right=false or right=true gives
the two orientations used in the contradiction. -/
def badHalfEvent {ι : Type*} (right : ι → Bool) (u : ι → ℝ) (I : Finset ι) (q : ℝ) :
    Set ((ι → ℝ) × (ι → ℝ)) :=
  {z | q/2 ≤ ((eligibleIndices right z.1 u I).card : ℝ) ∧
    ∀ i : I, ¬(eligible (right i) (z.1 i) (u i) ∧ z.2 i ∈ crossingPartner (right i) (u i))}

theorem badHalfEvent_measurable {ι : Type*} (right : ι → Bool) (u : ι → ℝ) (I : Finset ι) (q : ℝ) :
    MeasurableSet (badHalfEvent right u I q) := by
  have hcount : Measurable (fun z : (ι → ℝ) × (ι → ℝ) =>
      ((eligibleIndices right z.1 u I).card : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      ((eligible_count_measurable right u I).comp measurable_fst)
  have hq : MeasurableSet {z : (ι → ℝ) × (ι → ℝ) | q/2 ≤ ((eligibleIndices right z.1 u I).card : ℝ)} :=
    measurableSet_le measurable_const hcount
  have hi (i : I) : MeasurableSet {z : (ι → ℝ) × (ι → ℝ) |
      ¬(eligible (right i) (z.1 i) (u i) ∧ z.2 i ∈ crossingPartner (right i) (u i))} :=
    (((eligible_measurable (right i) (u i)).preimage
      ((measurable_pi_apply (i : ι)).comp measurable_fst)).inter
      ((crossingPartner_measurable (right i) (u i)).preimage
        ((measurable_pi_apply (i : ι)).comp measurable_snd))).compl
  convert hq.inter (MeasurableSet.iInter hi) using 1
  ext z
  simp [badHalfEvent]

theorem badHalfEvent_section {ι : Type*} (right : ι → Bool) (x u : ι → ℝ)
    (I : Finset ι) (q : ℝ) (hq : q/2 ≤ ((eligibleIndices right x u I).card : ℝ)) :
    Prod.mk x ⁻¹' badHalfEvent right u I q =
      Set.pi (eligibleIndices right x u I : Set ι) (fun i => (crossingPartner (right i) (u i))ᶜ) := by
  ext y
  simp only [Set.mem_preimage, badHalfEvent, Set.mem_ofPred_eq, Set.mem_pi,
    Finset.mem_coe, eligibleIndices, Finset.mem_filter, Set.mem_compl_iff]
  constructor
  · intro h i hi
    exact fun hy => h.2 ⟨i, hi.1⟩ ⟨hi.2, hy⟩
  · intro h
    refine ⟨hq, fun i hi => ?_⟩
    exact h i ⟨i.2, hi.1⟩ hi.2

theorem vectorPosterior_badHalf_bound {ι : Type*}
    (p : ι → CouplingParameters) (right : ι → Bool) (w : ι → Fin 2)
    (x u : ι → ℝ) (I : Finset ι) (q m ρ L : ℝ)
    (hx : ∀ i ∈ I, x i ∈ Set.Ico 0 1)
    (hu : ∀ i ∈ I, (p i).width (w i) ≤ u i ∧ u i ≤ 1-(p i).width (w i))
    (hρ : ∀ i ∈ I, (p i).rho (w i) = ρ)
    (hρ0 : 0 ≤ ρ) (hq : m/20 ≤ q) (hL : L ≤ m*ρ) :
    vectorPosterior p right x (Prod.mk x ⁻¹' badHalfEvent right u I q) ≤
      ENNReal.ofReal (Real.exp (-L/400)) := by
  by_cases hn : q/2 ≤ ((eligibleIndices right x u I).card : ℝ)
  · rw [badHalfEvent_section right x u I q hn]
    apply vectorPosterior_noncrossing_source_bound p right w x u (eligibleIndices right x u I) m ρ L
    · intro i hi
      exact hx i (Finset.mem_filter.mp hi).1
    · intro i hi
      exact hu i (Finset.mem_filter.mp hi).1
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i hi
      exact hρ i (Finset.mem_filter.mp hi).1
    · exact hρ0
    · linarith
    · exact hL
  · have he : Prod.mk x ⁻¹' badHalfEvent right u I q = ∅ := by
      ext y
      simp [badHalfEvent, hn]
    rw [he, measure_empty]
    exact zero_le

theorem vectorEndpoint_unitCube {ι : Type*} [Countable ι]
    (p : ι → CouplingParameters) (right : ι → Bool) :
    ∀ᵐ x ∂(vectorCoupling p).map (vectorEndpoint right), ∀ i, x i ∈ Set.Ico 0 1 := by
  rw [vectorEndpoint_law, ae_all_iff]
  intro i
  have hi : ∀ᵐ t ∂(p i).selectedLaw true (right i), t ∈ Set.Ico 0 1 :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ico)
  have hh := Measure.infinitePi_map_eval (fun i => (p i).selectedLaw true (right i)) i
  rw [← hh] at hi
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hi

/-- Actual conditional bound for each oriented bad event, ready for the
countably infinite masked-sum theorem. No conditional-independence assumption
or posterior bound is an input. -/
theorem badHalf_condExp_bound {ι : Type*} [Countable ι]
    (p : ι → CouplingParameters) (right : ι → Bool) (w : ι → Fin 2)
    (u : ι → ℝ) (I : Finset ι) (q m ρ L : ℝ)
    (hu : ∀ i ∈ I, (p i).width (w i) ≤ u i ∧ u i ≤ 1-(p i).width (w i))
    (hρ : ∀ i ∈ I, (p i).rho (w i) = ρ)
    (hρ0 : 0 ≤ ρ) (hq : m/20 ≤ q) (hL : L ≤ m*ρ) :
    ∀ᵐ ω ∂vectorCoupling p,
      (vectorCoupling p)[
        (fun ω => (badHalfEvent right u I q).indicator (fun _ => (1 : ℝ))
          (vectorEndpoint right ω, vectorEndpoint (fun i => !right i) ω)) |
        (inferInstance : MeasurableSpace (ι → ℝ)).comap (vectorEndpoint right)] ω ≤ Real.exp (-L/400) := by
  apply vector_condExp_event_le p right (badHalfEvent_measurable right u I q)
  filter_upwards [vectorEndpoint_unitCube p right] with x hx
  have hh := vectorPosterior_badHalf_bound p right w x u I q m ρ L (fun i _ => hx i) hu hρ hρ0 hq hL
  have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  simpa only [measureReal_def, ENNReal.toReal_ofReal (Real.exp_pos _).le] using hh'

/-- On ordered noncrossing pairs, the two eligibility counts are complementary.
Thus the strict second half of the source bad event lies in the reverse
badHalfEvent; using a weak inequality there only enlarges that event. -/
theorem noncrossing_eligible_complement {ι : Type*} (x y u : ι → ℝ) (I : Finset ι)
    (hxy : ∀ i ∈ I, x i ≤ y i) (hn : ∀ i ∈ I, ¬(x i < u i ∧ u i ≤ y i)) :
    (eligibleIndices (fun _ => false) x u I).card +
      (eligibleIndices (fun _ => true) y u I).card = I.card := by
  have he : eligibleIndices (fun _ => true) y u I = I.filter (fun i => ¬(x i < u i)) := by
    ext i
    simp only [eligibleIndices, Finset.mem_filter, eligible, ↓reduceIte]
    constructor
    · rintro ⟨hi, hy⟩
      exact ⟨hi, fun hx => hn i hi ⟨hx, hy⟩⟩
    · rintro ⟨hi, hx⟩
      exact ⟨hi, le_trans (le_of_not_gt hx) (hxy i hi)⟩
  rw [he]
  exact Finset.card_filter_add_card_filter_not (fun i => x i < u i)

/-- Exact source second-half event is contained in the reverse event whose
conditional estimate was proved above. All coordinates in I are accounted for. -/
theorem second_bad_half_in_reverse {ι : Type*} (x y u : ι → ℝ) (I : Finset ι)
    (hxy : ∀ i ∈ I, x i ≤ y i)
    (hn : ∀ i ∈ I, ¬(x i < u i ∧ u i ≤ y i))
    (hcount : ((eligibleIndices (fun _ => false) x u I).card : ℝ) < (I.card : ℝ)/2) :
    (y,x) ∈ badHalfEvent (fun _ => true) u I I.card := by
  constructor
  · have he := noncrossing_eligible_complement x y u I hxy hn
    have her : ((eligibleIndices (fun _ => false) x u I).card : ℝ) +
        ((eligibleIndices (fun _ => true) y u I).card : ℝ) = (I.card : ℝ) := by exact_mod_cast he
    linarith
  · intro i hi
    exact hn i i.2 ⟨hi.2, hi.1⟩

/-- The pointwise orderedness needed for the complementary-event argument is
itself a theorem about the actual full augmented law. -/
theorem vectorCoupling_ordered {ι : Type*} [Countable ι] (p : ι → CouplingParameters) :
    vectorCoupling p {ω | ∀ i, (ω i).2.1 ≤ (ω i).2.2} = 1 := by
  have he : {ω : ι → Fin 6 × (ℝ × ℝ) | ∀ i, (ω i).2.1 ≤ (ω i).2.2} =
      Set.pi Set.univ (fun _ : ι => {z : Fin 6 × (ℝ × ℝ) | z.2.1 ≤ z.2.2}) := by ext ω; simp
  rw [he, vectorCoupling, Measure.infinitePi_pi_univ]
  · simp [labelledCoupling_ordered]
  · intro i
    exact orderedPairs_measurable.preimage measurable_snd

end CouplingParameters
end
end FiniteFactor

end OAI
