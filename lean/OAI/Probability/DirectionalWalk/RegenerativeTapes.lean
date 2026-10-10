import OAI.Probability.DirectionalWalk.CommonBlocks

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

abbrev tapeSigma {α : Type*} [MeasurableSpace α] (s : Set ℕ) : MeasurableSpace (ℕ → α) :=
  ⨆ i ∈ s, MeasurableSpace.comap (fun Z : ℕ → α => Z i) inferInstance

lemma measurable_tapeEval {α : Type*} [MeasurableSpace α] {s : Set ℕ} {i : ℕ} (hi : i ∈ s) :
    @Measurable (ℕ → α) α (tapeSigma s) _ (fun Z => Z i) :=
  measurable_iff_comap_le.mpr (le_iSup₂_of_le i hi le_rfl)

lemma iid_prefix_suffix_independent {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ) :
    IndepFun (fun Z (i : Fin n) => Z i) (fun (Z : ℕ → α) j => Z (n+j))
      (Measure.infinitePi (fun _ : ℕ => ν)) := by
  have hS : @Measurable (ℕ → α) (Fin n → α) (tapeSigma {i | i < n}) _
      (fun Z i => Z i) := by
    let : MeasurableSpace (ℕ → α) := tapeSigma {i | i < n}
    exact Measurable.of_eval (fun i => measurable_tapeEval i.isLt)
  have hT : @Measurable (ℕ → α) (ℕ → α) (tapeSigma {i | n ≤ i}) _
      (fun Z j => Z (n+j)) := by
    let : MeasurableSpace (ℕ → α) := tapeSigma {i | n ≤ i}
    exact Measurable.of_eval (fun j => measurable_tapeEval (Nat.le_add_right n j))
  have hd : Disjoint {i : ℕ | i < n} {i | n ≤ i} := by
    apply Set.disjoint_left.mpr
    intro i hi hj
    exact (not_lt_of_ge (show n ≤ i from hj)) (show i < n from hi)
  have hind := indep_iSup_of_disjoint (fun i : ℕ => (measurable_pi_apply (X := fun _ => α) i).comap_le)
    (iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ x => x) (fun _ => measurable_id)) hd
  exact (IndepFun_iff_Indep _ _ _).mpr (indep_of_indep_of_le hind hS.comap_le hT.comap_le)

lemma iid_suffix_law {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun Z j => Z (n+j)) =
      Measure.infinitePi (fun _ : ℕ => ν) := by
  exact Measure.map_infinitePi_infinitePi_of_inj (fun _ _ h => Nat.add_left_cancel h)

lemma tapeCylinder_suffix_factorization {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν] (a : TapeList α) (E : Set (ℕ → α)) (hE : MeasurableSet E) :
    Measure.infinitePi (fun _ : ℕ => ν) {Z | Z ∈ tapeCylinder a ∧ (fun j => Z (a.1+j)) ∈ E} =
      (∏ i : Fin a.1, ν {a.2 i}) * Measure.infinitePi (fun _ : ℕ => ν) E := by
  have hh := (iid_prefix_suffix_independent ν a.1).measure_inter_preimage_eq_mul {a.2} E
    (measurableSet_singleton _) hE
  have hc : (fun Z (i : Fin a.1) => Z i) ⁻¹' {a.2} = tapeCylinder a := by
    ext Z; simp only [Set.mem_preimage,Set.mem_singleton_iff,tapeCylinder,Set.mem_ofPred_eq,funext_iff]
  rw [hc,tapeCylinder_mass ν a,← Measure.map_apply (by fun_prop) hE,iid_suffix_law] at hh
  exact hh

noncomputable def regenerativeSequence {Ω β : Type*} (f : Ω → β) (T : Ω → Ω) (x : Ω) (k : ℕ) : β :=
  f (T^[k] x)

lemma measurable_regenerativeSequence {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (f : Ω → β) (T : Ω → Ω) (hf : Measurable f) (hT : Measurable T) :
    Measurable (regenerativeSequence f T) :=
  Measurable.of_eval (fun k => hf.comp (hT.iterate k))

lemma regenerativeSequence_prefix_mass {Ω β : Type*} [MeasurableSpace Ω] [Countable β]
    [MeasurableSpace β] [MeasurableSingletonClass β] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure β) (f : Ω → β) (T : Ω → Ω) (hf : Measurable f) (hT : Measurable T)
    (hfac : ∀ a E, MeasurableSet E → P {x | f x = a ∧ T x ∈ E} = ν {a} * P E)
    (n : ℕ) (a : ℕ → β) :
    P {x | ∀ i < n, regenerativeSequence f T x i = a i} = ∏ i ∈ Finset.range n, ν {a i} := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    have heq : {x | ∀ i < n+1, regenerativeSequence f T x i = a i} =
        {x | f x = a 0 ∧ T x ∈ {y | ∀ i < n, regenerativeSequence f T y i = a (i+1)}} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h
        refine ⟨h 0 (Nat.succ_pos _),fun i hi => ?_⟩
        simpa only [regenerativeSequence,Function.iterate_succ_apply] using h (i+1) (by omega)
      · rintro ⟨h0,h⟩ i hi
        cases i with
        | zero => exact h0
        | succ i => simpa only [regenerativeSequence,Function.iterate_succ_apply] using h i (by omega)
    have hE : MeasurableSet {y | ∀ i < n, regenerativeSequence f T y i = a (i+1)} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
        (measurableSet_singleton (a (i+1))).preimage ((measurable_pi_apply i).comp
          (measurable_regenerativeSequence f T hf hT))))
    rw [heq,hfac _ _ hE,ih,Finset.prod_range_succ']
    exact mul_comm _ _

lemma regenerativeSequence_map {Ω β : Type*} [MeasurableSpace Ω] [Countable β]
    [MeasurableSpace β] [MeasurableSingletonClass β] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure β) [IsProbabilityMeasure ν] (f : Ω → β) (T : Ω → Ω) (hf : Measurable f) (hT : Measurable T)
    (hfac : ∀ a E, MeasurableSet E → P {x | f x = a ∧ T x ∈ E} = ν {a} * P E) :
    P.map (regenerativeSequence f T) = Measure.infinitePi (fun _ : ℕ => ν) := by
  classical
  apply measure_eq_of_prefix
  intro n
  apply Measure.ext_of_singleton
  intro a
  let γ : ℕ → β := fun i => if hi : i ≤ n then a ⟨i,Finset.mem_Iic.mpr hi⟩ else
    a ⟨0,Finset.mem_Iic.mpr (Nat.zero_le n)⟩
  have heq : (frestrictLe n : (ℕ → β) → (Finset.Iic n → β)) ⁻¹' {a} =
      (↑(Finset.range (n+1)) : Set ℕ).pi (fun i => {γ i}) := by
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
    Measure.map_apply (measurable_regenerativeSequence f T hf hT)
      (MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => measurableSet_singleton _)),
    Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  have hpre : regenerativeSequence f T ⁻¹' (↑(Finset.range (n+1)) : Set ℕ).pi (fun i => {γ i}) =
      {x | ∀ i < n+1, regenerativeSequence f T x i = γ i} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_singleton_iff,Finset.mem_coe, Finset.mem_range, Set.mem_ofPred_eq]
  rw [hpre]
  exact regenerativeSequence_prefix_mass P ν f T hf hT hfac (n+1) γ

noncomputable def commonBlocks {α : Type*} (L : Bool → α → ℕ) : TwoTape α → ℕ → TwoTapeList α :=
  regenerativeSequence (firstCommonBlock L) (commonRestart L)

lemma commonBlocks_map {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H) :
    (twoTapeLaw ν).map (commonBlocks L) = Measure.infinitePi (fun _ : ℕ => commonBlockLaw ν L) := by
  let : IsProbabilityMeasure (commonBlockLaw ν L) :=
    probabilityMeasure_map (μ := twoTapeLaw ν) (measurable_firstCommonBlock L).aemeasurable
  exact regenerativeSequence_map (twoTapeLaw ν) (commonBlockLaw ν L) _ _
    (measurable_firstCommonBlock L) (measurable_commonRestart L)
    (firstCommonBlock_suffix_factorization ν L hL he)

lemma commonBlockLaw_atom {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (a : TwoTapeList α) (ha : IsFirstCommonList L a) :
    commonBlockLaw ν L {a} = ∏ b : Bool, ∏ i : Fin (a b).1, ν b {(a b).2 i} := by
  rw [commonBlockLaw,Measure.map_apply (measurable_firstCommonBlock L) (measurableSet_singleton a),← twoCylinder_mass ν a]
  apply measure_congr
  filter_upwards [ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL,he] with Z hZ he
  exact propext (firstCommonBlock_atom_iff L Z hZ he a ha)

end DirectionalZeroOne

end OAI
