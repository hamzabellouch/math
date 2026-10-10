import OAI.Probability.DirectionalWalk.Words

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

noncomputable def conditioned {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) : Measure (Path d) := (annealed μ 0)[|nonBacktracking v]

lemma conditioned_probability {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    IsProbabilityMeasure (conditioned μ v) := cond_isProbabilityMeasure hp.ne'

lemma ae_conditioned_firstWord {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    ∀ᵐ X ∂conditioned μ v, RegenerationWord v (firstWord v X) := by
  have hac : conditioned μ v ≪ annealed μ 0 := cond_absolutelyContinuous
  have hfin := hac.ae_le (finite_supremum μ hell 0 v hv)
  have hcut := hac.ae_le (ae_infinitely_trueCuts μ 0 v hp)
  have hNN := hac.ae_le (ae_start_and_nearestNeighbour μ 0)
  filter_upwards [ae_cond_mem (μ := annealed μ 0) (measurableSet_nonBacktracking v),
    hfin,hcut,hNN] with X hD hf hc hs
  apply firstWord_regeneration v X hs.1 hs.2 hD
  have hu : ¬∃ b : ℝ, ∀ n, height v (X n) ≤ b := by
    intro hb
    obtain ⟨n,hn⟩ := eventually_atTop.mp ((hf hb).eventually (eventually_lt_atBot (-1)))
    have hh := hD n
    have := hn n le_rfl
    linarith
  obtain ⟨n,_,hn⟩ := hc hu 0
  exact ⟨n,hn⟩

lemma conditioned_firstWord_suffix {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (γ : Word d) (hγ : RegenerationWord v γ)
    {E : Set (Path d)} (hE : MeasurableSet E) :
    conditioned μ v {X | firstWord v X = γ ∧ cutSuffix v X ∈ E} =
      annealedWordWeight μ γ * conditioned μ v E := by
  change (annealed μ 0)[{X | firstWord v X = γ ∧ cutSuffix v X ∈ E}|nonBacktracking v] = _
  rw [cond_apply (measurableSet_nonBacktracking v)]
  have hsub : {X | firstWord v X = γ ∧ cutSuffix v X ∈ E} ⊆ nonBacktracking v :=
    fun _ h => firstWord_event_subset_nonBacktracking v γ hγ h.1
  rw [Set.inter_eq_right.mpr hsub,firstWord_event v γ hγ E,
    annealed_record_relative_tail μ v 0 γ.1 (wordPath γ)
      (fun i hi => (hγ.2.2.2.1 i hi).2) hE,
    annealed_cylinder,ite_eq_left hγ.2.1.symm]
  unfold conditioned
  rw [cond_apply (measurableSet_nonBacktracking v),Set.inter_comm (nonBacktracking v) E]
  unfold annealedWordWeight
  ac_rfl

lemma measure_eq_tsum_fibres {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A] (P : Measure Ω) (f : Ω → A)
    (hf : Measurable f) {E : Set Ω} (hE : MeasurableSet E) :
    P E = ∑' a, P ({X | f X = a} ∩ E) := by
  have heq : E = ⋃ a, {X | f X = a} ∩ E := by
    ext X; simp
  calc
    P E = P (⋃ a, {X | f X = a} ∩ E) := congrArg P heq
    _ = _ := measure_iUnion (fun a b hab => ?_) (fun a => ?_)
  · apply Set.disjoint_left.mpr
    rintro X ⟨ha,_⟩ ⟨hb,_⟩
    exact hab (ha.symm.trans hb)
  · exact ((measurableSet_singleton a).preimage hf).inter hE

noncomputable def slabLaw {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) : Measure (Word d) := (conditioned μ v).map (firstWord v)

lemma slabLaw_probability {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    IsProbabilityMeasure (slabLaw μ v) := by
  let := conditioned_probability μ v hp
  exact probabilityMeasure_map (measurable_firstWord v).aemeasurable

lemma slabLaw_atom {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v))
    (γ : Word d) (hγ : RegenerationWord v γ) :
    slabLaw μ v {γ} = annealedWordWeight μ γ := by
  let := conditioned_probability μ v hp
  have h := conditioned_firstWord_suffix μ v γ hγ MeasurableSet.univ
  rw [slabLaw, Measure.map_apply (measurable_firstWord v) (measurableSet_singleton γ)]
  change conditioned μ v {X | firstWord v X = γ} = _
  simpa only [Set.mem_univ, and_true, measure_univ, mul_one] using h

lemma ae_slabLaw_regeneration {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    ∀ᵐ γ ∂slabLaw μ v, RegenerationWord v γ := by
  exact (ae_map_iff (measurable_firstWord v).aemeasurable
    (Set.to_countable {γ : Word d | RegenerationWord v γ}).measurableSet).mpr
      (ae_conditioned_firstWord μ hell v hv hp)

lemma firstWord_suffix_factorization {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (γ : Word d)
    {E : Set (Path d)} (hE : MeasurableSet E) :
    conditioned μ v {X | firstWord v X = γ ∧ cutSuffix v X ∈ E} =
      slabLaw μ v {γ} * conditioned μ v E := by
  by_cases hγ : RegenerationWord v γ
  · rw [conditioned_firstWord_suffix μ v γ hγ hE,slabLaw_atom μ v hp γ hγ]
  · have hz : conditioned μ v {X | firstWord v X = γ} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [ae_conditioned_firstWord μ hell v hv hp] with X hX hEq
      exact hγ (hEq ▸ hX)
    have hν : slabLaw μ v {γ} = 0 := by
      rw [slabLaw,Measure.map_apply (measurable_firstWord v) (measurableSet_singleton γ)]
      exact hz
    rw [hν,zero_mul]
    exact measure_mono_null (fun _ h => h.1) hz

lemma cutSuffix_measurePreserving {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    MeasurePreserving (cutSuffix v) (conditioned μ v) (conditioned μ v) := by
  let := conditioned_probability μ v hp
  let := slabLaw_probability μ v hp
  refine ⟨measurable_cutSuffix v,?_⟩
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply (measurable_cutSuffix v) hE,
    measure_eq_tsum_fibres (conditioned μ v) (firstWord v) (measurable_firstWord v)
      ((measurable_cutSuffix v) hE)]
  simp_rw [show ∀ γ, {X | firstWord v X = γ} ∩ cutSuffix v ⁻¹' E =
    {X | firstWord v X = γ ∧ cutSuffix v X ∈ E} from fun _ => rfl,
    firstWord_suffix_factorization μ hell v hv hp _ hE, ENNReal.tsum_mul_right]
  have hsum := measure_eq_tsum_fibres (slabLaw μ v) id measurable_id MeasurableSet.univ
  simp only [id_eq,Set.inter_univ,Set.ofPred_eq_eq_singleton,measure_univ] at hsum
  rw [← hsum,one_mul]

noncomputable def slabs {d : ℕ} (v : Fin d → ℝ) (X : Path d) (k : ℕ) : Word d :=
  firstWord v ((cutSuffix v)^[k] X)

lemma measurable_slabs {d : ℕ} (v : Fin d → ℝ) : Measurable (slabs v) :=
  Measurable.of_eval (fun k => (measurable_firstWord v).comp ((measurable_cutSuffix v).iterate k))

lemma slabs_prefix_mass {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (n : ℕ) (γ : ℕ → Word d) :
    conditioned μ v {X | ∀ i < n, slabs v X i = γ i} =
      ∏ i ∈ Finset.range n, slabLaw μ v {γ i} := by
  let := conditioned_probability μ v hp
  induction n generalizing γ with
  | zero => simp
  | succ n ih =>
    have heq : {X | ∀ i < n+1, slabs v X i = γ i} =
        {X | firstWord v X = γ 0 ∧ cutSuffix v X ∈
          {Y | ∀ i < n, slabs v Y i = γ (i+1)}} := by
      ext X
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h
        refine ⟨h 0 (Nat.succ_pos _),fun i hi => ?_⟩
        simpa only [slabs,Function.iterate_succ_apply] using h (i+1) (by omega)
      · rintro ⟨h0,h⟩ i hi
        cases i with
        | zero => exact h0
        | succ i => simpa only [slabs,Function.iterate_succ_apply] using h i (by omega)
    have hE : MeasurableSet {Y | ∀ i < n, slabs v Y i = γ (i+1)} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
        (measurableSet_singleton (γ (i+1))).preimage ((measurable_pi_apply i).comp (measurable_slabs v))))
    rw [heq,firstWord_suffix_factorization μ hell v hv hp _ hE,ih]
    rw [Finset.prod_range_succ']
    exact mul_comm _ _

lemma slabs_map_eq_infinitePi {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    (conditioned μ v).map (slabs v) = Measure.infinitePi (fun _ : ℕ => slabLaw μ v) := by
  classical
  let := conditioned_probability μ v hp
  let := slabLaw_probability μ v hp
  apply measure_eq_of_prefix
  intro n
  apply Measure.ext_of_singleton
  intro a
  let γ : ℕ → Word d := fun i => if hi : i ≤ n then a ⟨i,Finset.mem_Iic.mpr hi⟩ else
    a ⟨0,Finset.mem_Iic.mpr (Nat.zero_le n)⟩
  have heq : (frestrictLe n : (ℕ → Word d) → (Finset.Iic n → Word d)) ⁻¹' {a} = (↑(Finset.range (n+1)) : Set ℕ).pi (fun i => {γ i}) := by
    ext b
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_pi,Finset.mem_coe,Finset.mem_range]
    constructor
    · intro h i hi
      have hh := congr_fun h ⟨i,Finset.mem_Iic.mpr (by omega)⟩
      simpa [γ,show i ≤ n by omega] using hh
    · intro h
      funext i
      have hi := Finset.mem_Iic.mp i.property
      simpa [γ,hi] using h i (by omega)
  rw [Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton a),
    Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton a),heq,
    Measure.map_apply (measurable_slabs v) (MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => measurableSet_singleton _)),
    Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  have hpre : slabs v ⁻¹' (↑(Finset.range (n+1)) : Set ℕ).pi (fun i => {γ i}) =
      {X | ∀ i < n+1, slabs v X i = γ i} := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_singleton_iff,
      Finset.mem_coe, Finset.mem_range, Set.mem_ofPred_eq]
  rw [hpre]
  exact slabs_prefix_mass μ hell v hv hp (n+1) γ

lemma slabs_marginal {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (k : ℕ) :
    (conditioned μ v).map (fun X => slabs v X k) = slabLaw μ v := by
  rw [show (fun X => slabs v X k) = firstWord v ∘ (cutSuffix v)^[k] from rfl,
    ← Measure.map_map (measurable_firstWord v) ((measurable_cutSuffix v).iterate k),
    ((cutSuffix_measurePreserving μ hell v hv hp).iterate k).map_eq]
  rfl

lemma slabs_iid {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    iIndepFun (fun k X => slabs v X k) (conditioned μ v) := by
  let := conditioned_probability μ v hp
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map (fun k =>
    (measurable_pi_apply k).comp (measurable_slabs v))).mpr
  change (conditioned μ v).map (slabs v) = Measure.infinitePi
    (fun k => (conditioned μ v).map (fun X => slabs v X k))
  rw [slabs_map_eq_infinitePi μ hell v hv hp]
  congr 1
  funext k
  exact (slabs_marginal μ hell v hv hp k).symm

end DirectionalZeroOne

end OAI
