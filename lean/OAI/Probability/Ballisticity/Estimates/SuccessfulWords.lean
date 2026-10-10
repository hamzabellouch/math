import Mathlib
import OAI.Probability.Ballisticity.Estimates.TupleEndpoint

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def hitWordEvent {d : ℕ} (x : Lattice d) (S T : Set (Lattice d))
    (E : Set (HitWord x S T)) : Set (Path d) :=
  ⋃ w : E, wordCylinder x w.val.val

lemma measurableSet_hitWordEvent {d : ℕ} (x : Lattice d) (S T : Set (Lattice d))
    (E : Set (HitWord x S T)) : MeasurableSet (hitWordEvent x S T E) := by
  exact MeasurableSet.iUnion fun w => measurableSet_wordCylinder x w.val.val

lemma hitWordEvent_mass {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (hST : Disjoint S T) (E : Set (HitWord x S T)) :
    quenchedKernel (ω,x) (hitWordEvent x S T E) =
      ∑' w : E, ENNReal.ofReal (wordWeight ω x w.val.val) := by
  rw [hitWordEvent,measure_iUnion]
  · congr 1; funext w; exact quenched_wordCylinder ω x w.val.val
  · intro u v huv
    exact hitWord_cylinders_disjoint x S T hST (fun h => huv (Subtype.ext h))
  · exact fun w => measurableSet_wordCylinder x w.val.val

lemma hitWordEvent_univ_ae {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) :
    hitWordEvent x S T Set.univ =ᵐ[quenchedKernel (ω,x)] Hit S T := by
  filter_upwards [quenched_initial_ae (ω,x), quenched_nearest_neighbor (ω,x)] with X h0 hnn
  apply propext
  rw [hitWord_cover x S T X h0 hnn]
  simp only [hitWordEvent,Set.mem_iUnion,Subtype.exists,Set.mem_univ,exists_true_left]

noncomputable def successfulWordLaw {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) : Measure (HitWord x S T) :=
  Measure.sum (fun w => ENNReal.ofReal (wordWeight ω x w.val) • Measure.dirac w)

lemma successfulWordLaw_apply {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (E : Set (HitWord x S T)) :
    successfulWordLaw ω x S T E = ∑' w : E, ENNReal.ofReal (wordWeight ω x w.val.val) := by
  rw [successfulWordLaw,Measure.sum_apply_of_countable]
  simp only [Measure.smul_apply,smul_eq_mul,Measure.dirac_apply' _ (Set.to_countable E).measurableSet]
  calc
    _ = ∑' w, E.indicator (fun w => ENNReal.ofReal (wordWeight ω x w.val)) w := by
      congr 1
      funext w
      by_cases hw : w ∈ E <;> simp [hw]
    _ = _ := (tsum_subtype E (fun w => ENNReal.ofReal (wordWeight ω x w.val))).symm

lemma successfulWordLaw_event {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (hST : Disjoint S T) (E : Set (HitWord x S T)) :
    successfulWordLaw ω x S T E = quenchedKernel (ω,x) (hitWordEvent x S T E) := by
  rw [successfulWordLaw_apply,hitWordEvent_mass ω x S T hST]

lemma successfulWordLaw_univ {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (hST : Disjoint S T) :
    successfulWordLaw ω x S T Set.univ = quenchedKernel (ω,x) (Hit S T) := by
  rw [successfulWordLaw_event ω x S T hST]
  exact measure_congr (hitWordEvent_univ_ae ω x S T)

lemma successfulWordLaw_le_one {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (hST : Disjoint S T) :
    successfulWordLaw ω x S T Set.univ ≤ 1 := by
  rw [successfulWordLaw_univ ω x S T hST]
  exact prob_le_one

lemma successfulWordLaw_finite {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (hST : Disjoint S T) :
    IsFiniteMeasure (successfulWordLaw ω x S T) :=
  ⟨lt_of_le_of_lt (successfulWordLaw_le_one ω x S T hST) ENNReal.one_lt_top⟩

lemma successfulWordLaw_endpoint {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (hST : Disjoint S T) :
    (successfulWordLaw ω x S T).map (fun w => wordPath x w.val w.val.length) =
      hitKernel S T (ω,x) := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (measurable_of_countable _) hA,
    successfulWordLaw_event ω x S T hST,hitKernel_apply_eq_hit hST]
  apply measure_congr
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  apply propext
  constructor
  · intro hx
    obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hx
    have hp := hitWord_prefix x S T w.val hw
    exact Set.mem_iUnion.mpr ⟨w.val.val.length,⟨⟨hp.1,by
      rw [hw _ le_rfl]
      exact w.property⟩,hp.2⟩⟩
  · intro hx
    have hhit : X ∈ Hit S T := by
      obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨n,hn.1.1,hn.2⟩
    obtain ⟨w,hw⟩ := (hitWord_cover x S T X h0 hnn).mp hhit
    have hp := hitWord_prefix x S T w hw
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
    have hn' : X ∈ HitAt S T n := ⟨hn.1.1,hn.2⟩
    have he : n = w.val.length := by
      by_contra hne
      exact Set.disjoint_left.mp (hitAt_pairwise_disjoint hST hne) hn' hp
    have hwA : wordPath x w.val w.val.length ∈ A := by
      simpa only [he,hw _ le_rfl] using hn.1.2
    exact Set.mem_iUnion.mpr ⟨⟨w,hwA⟩,hw⟩

lemma successfulWordLaw_singleton {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (w : HitWord x S T) :
    successfulWordLaw ω x S T {w} = ENNReal.ofReal (wordWeight ω x w.val) := by
  rw [successfulWordLaw_apply,tsum_subtype {w} (fun v => ENNReal.ofReal (wordWeight ω x v.val))]
  simp

noncomputable def rawWordLaw {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Lattice d) : Measure (List (Direction d)) :=
  (successfulWordLaw ω x (Strip ℓ x H) (Upper ℓ x H)).map Subtype.val

instance rawWordLaw_finite {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Lattice d) : IsFiniteMeasure (rawWordLaw ℓ H ω x) := by
  let := successfulWordLaw_finite ω x (Strip ℓ x H) (Upper ℓ x H) (disjoint_strip_upper _ _ _)
  exact Measure.isFiniteMeasure_map _ _

lemma rawWordLaw_singleton {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Lattice d) (w : List (Direction d)) :
    rawWordLaw ℓ H ω x {w} =
      if wordPath x w ∈ HitAt (Strip ℓ x H) (Upper ℓ x H) w.length
      then ENNReal.ofReal (wordWeight ω x w) else 0 := by
  rw [rawWordLaw,Measure.map_apply measurable_subtype_coe (measurableSet_singleton _)]
  split_ifs with hw
  · have he : Subtype.val ⁻¹' {w} = ({⟨w,hw⟩} : Set (HitWord x (Strip ℓ x H) (Upper ℓ x H))) := by
      ext v
      simp only [Set.mem_preimage,Set.mem_singleton_iff,Subtype.ext_iff]
    rw [he,successfulWordLaw_singleton]
  · have he : Subtype.val ⁻¹' {w} = (∅ : Set (HitWord x (Strip ℓ x H) (Upper ℓ x H))) := by
      ext v
      simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_empty_iff_false,iff_false]
      intro hv
      exact hw (hv ▸ v.property)
    rw [he,measure_empty]

lemma rawWordLaw_univ {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Lattice d) :
    rawWordLaw ℓ H ω x Set.univ = variableHitKernel ℓ H (ω,x) Set.univ := by
  rw [rawWordLaw,Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    Set.preimage_univ,successfulWordLaw_univ ω x _ _ (disjoint_strip_upper _ _ _)]
  change _ = hitKernel (Strip ℓ x H) (Upper ℓ x H) (ω,x) Set.univ
  rw [hitKernel_apply_eq_hit (disjoint_strip_upper _ _ _),Set.inter_univ]

lemma rawWordLaw_endpoint {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Lattice d) :
    (rawWordLaw ℓ H ω x).map (fun w => wordPath x w w.length) = variableHitKernel ℓ H (ω,x) := by
  rw [rawWordLaw,Measure.map_map (measurable_of_countable _) measurable_subtype_coe]
  exact successfulWordLaw_endpoint ω x _ _ (disjoint_strip_upper _ _ _)

lemma measurable_rawWordLaw_rows {d : ℕ} (ℓ : Vector d) (H : ℕ) (x : Lattice d) :
    @Measurable _ _ (rowSigma (Strip ℓ x H)) _ (rawWordLaw ℓ H · x) := by
  let : MeasurableSpace (Environment d) := rowSigma (Strip ℓ x H)
  apply TupleKernel.measurable_countable_measure
  intro w
  simp_rw [rawWordLaw_singleton]
  by_cases hw : wordPath x w ∈ HitAt (Strip ℓ x H) (Upper ℓ x H) w.length
  · simp only [ite_eq_left hw]
    apply Measurable.ennreal_ofReal
    exact measurable_wordWeight_on x w fun y hy => by
      obtain ⟨n,hn,he⟩ := (wordDepartures_mem_iff x y w).mp hy
      rw [he]
      exact hw.2 n hn
  · simp only [ite_eq_right hw]
    exact measurable_const

lemma measurable_rawWordLaw {d : ℕ} (ℓ : Vector d) (H : ℕ) :
    Measurable (fun p : Environment d × Lattice d => rawWordLaw ℓ H p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro x
  exact (measurable_rawWordLaw_rows ℓ H x).mono (rowSigma_le _) le_rfl

noncomputable def rawTupleWordLaw {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) : Measure (Fin k → List (Direction d)) :=
  Measure.pi (fun j => rawWordLaw ℓ H ω (x j))

instance rawTupleWordLaw_finite {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) : IsFiniteMeasure (rawTupleWordLaw ℓ H ω x) := by
  unfold rawTupleWordLaw
  infer_instance

lemma rawTupleWordLaw_endpoint {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) :
    (rawTupleWordLaw ℓ H ω x).map (fun w j => wordPath (x j) (w j) (w j).length) =
      rawTupleEndpointLaw ℓ H ω x := by
  have he := Measure.pi_map_pi (μ := fun j : Fin k => rawWordLaw ℓ H ω (x j))
    (f := fun j w => wordPath (x j) w w.length)
    (fun _ => (measurable_of_countable _).aemeasurable)
  rw [rawTupleWordLaw,he]
  simp only [rawWordLaw_endpoint,rawTupleEndpointLaw]

lemma rawTupleWordLaw_singleton {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) (w : Fin k → List (Direction d)) :
    rawTupleWordLaw ℓ H ω x {w} = ∏ j, rawWordLaw ℓ H ω (x j) {w j} := by
  exact Measure.pi_singleton _ _

lemma measurable_rawWordLaw_tuple_component {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (j : Fin k) :
    Measurable (fun p : Environment d × (Fin k → Lattice d) => rawWordLaw ℓ H p.1 (p.2 j)) := by
  have hg : Measurable (fun p : Environment d × (Fin k → Lattice d) => (p.1,p.2 j)) :=
    measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)
  have hc := (measurable_rawWordLaw ℓ H).comp hg
  simpa only [Function.comp_def] using hc

lemma measurable_rawTupleWordLaw_singleton {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (w : Fin k → List (Direction d)) :
    Measurable (fun p : Environment d × (Fin k → Lattice d) => rawTupleWordLaw ℓ H p.1 p.2 {w}) := by
  simp only [rawTupleWordLaw_singleton]
  apply Finset.measurable_prod
  intro j _
  have hc := (Measure.measurable_coe (measurableSet_singleton (w j))).comp
    (measurable_rawWordLaw_tuple_component ℓ H j)
  simpa only [Function.comp_def] using hc

lemma measurable_rawTupleWordLaw {d k : ℕ} (ℓ : Vector d) (H : ℕ) :
    Measurable (fun p : Environment d × (Fin k → Lattice d) => rawTupleWordLaw ℓ H p.1 p.2) := by
  exact TupleKernel.measurable_countable_measure _ (measurable_rawTupleWordLaw_singleton ℓ H)

end DirectionalTransience

end

end OAI
