import OAI.Probability.DirectionalWalk.Renewal

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

abbrev TwoTape (α : Type*) := (Bool × ℕ) → α
abbrev TwoTapeList (α : Type*) := Bool → TapeList α

noncomputable def twoTapeLaw {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)] : Measure (TwoTape α) :=
  Measure.infinitePi (fun i => ν i.1)

def twoPrefix {α : Type*} (n : Bool → ℕ) (Z : TwoTape α) : TwoTapeList α :=
  fun b => tapePrefix (n b) (fun i => Z (b,i))

def twoCylinder {α : Type*} (a : TwoTapeList α) : Set (TwoTape α) :=
  {Z | ∀ b, ∀ i : Fin (a b).1, Z (b,i) = (a b).2 i}

lemma measurableSet_twoCylinder {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (a : TwoTapeList α) : MeasurableSet (twoCylinder a) := by
  simp only [twoCylinder,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun b => MeasurableSet.iInter (fun i =>
    (measurableSet_singleton ((a b).2 i)).preimage (measurable_pi_apply (b,(i : ℕ)))))

lemma measurable_twoPrefix {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (n : Bool → ℕ) : Measurable (twoPrefix (α := α) n) := by
  exact Measurable.of_eval (fun b => (measurable_tapePrefix (n b)).comp (by fun_prop))

def twoShift {α : Type*} (n : Bool → ℕ) (Z : TwoTape α) : TwoTape α :=
  fun i => Z (i.1,n i.1+i.2)

lemma measurable_twoShift {α : Type*} [MeasurableSpace α] (n : Bool → ℕ) :
    Measurable (twoShift (α := α) n) := by
  exact Measurable.of_eval (fun i => measurable_pi_apply _)

lemma twoShift_law {α : Type*} [MeasurableSpace α] (ν : Bool → Measure α)
    [∀ b, IsProbabilityMeasure (ν b)] (n : Bool → ℕ) :
    (twoTapeLaw ν).map (twoShift n) = twoTapeLaw ν := by
  apply Measure.map_infinitePi_infinitePi_of_inj
  intro i j h
  have hb := congrArg Prod.fst h
  have hn := congrArg Prod.snd h
  cases i with | mk b i =>
    cases j with | mk c j =>
      simp only [Prod.mk.injEq] at hb hn ⊢
      subst c
      exact ⟨rfl,Nat.add_left_cancel hn⟩

lemma twoExtract_law {α : Type*} [MeasurableSpace α] (ν : Bool → Measure α)
    [∀ b, IsProbabilityMeasure (ν b)] (b : Bool) :
    (twoTapeLaw ν).map (fun Z i => Z (b,i)) = Measure.infinitePi (fun _ : ℕ => ν b) := by
  exact Measure.map_infinitePi_infinitePi_of_inj (fun _ _ h => congrArg Prod.snd h)

lemma ae_twoTape_prop {α : Type*} [MeasurableSpace α] (ν : Bool → Measure α)
    [∀ b, IsProbabilityMeasure (ν b)] (p : Bool → α → Prop)
    (hp : ∀ b, MeasurableSet {a | p b a}) (h : ∀ b, ∀ᵐ a ∂ν b, p b a) :
    ∀ᵐ Z ∂twoTapeLaw ν, ∀ b i, p b (Z (b,i)) := by
  rw [ae_all_iff]
  intro b
  apply ae_of_ae_map (μ := twoTapeLaw ν) (f := fun Z i => Z (b,i))
    (p := fun Z => ∀ i, p b (Z i))
    ((Measurable.of_eval (fun i => measurable_pi_apply (b,i))).aemeasurable)
  rw [twoExtract_law]
  exact ae_tape_prop (ν b) (p b) (hp b) (h b)

abbrev coordSigma {ι α : Type*} [MeasurableSpace α] (s : Set ι) : MeasurableSpace (ι → α) :=
  ⨆ i ∈ s, MeasurableSpace.comap (fun Z : ι → α => Z i) inferInstance

lemma measurable_coordEval {ι α : Type*} [MeasurableSpace α] {s : Set ι} {i : ι} (hi : i ∈ s) :
    @Measurable (ι → α) α (coordSigma s) _ (fun Z => Z i) :=
  measurable_iff_comap_le.mpr (le_iSup₂_of_le i hi le_rfl)

lemma two_prefix_suffix_independent {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (n : Bool → ℕ) :
    IndepFun (fun Z (i : Σ b : Bool, Fin (n b)) => Z (i.1,i.2)) (twoShift n) (twoTapeLaw ν) := by
  have hS : @Measurable (TwoTape α) ((Σ b : Bool, Fin (n b)) → α)
      (coordSigma {i | i.2 < n i.1}) _ (fun Z i => Z (i.1,i.2)) := by
    let : MeasurableSpace (TwoTape α) := coordSigma {i | i.2 < n i.1}
    exact Measurable.of_eval (fun i => measurable_coordEval i.2.isLt)
  have hT : @Measurable (TwoTape α) (TwoTape α)
      (coordSigma {i | n i.1 ≤ i.2}) _ (twoShift n) := by
    let : MeasurableSpace (TwoTape α) := coordSigma {i | n i.1 ≤ i.2}
    exact Measurable.of_eval (fun i => measurable_coordEval (Nat.le_add_right (n i.1) i.2))
  have hd : Disjoint {i : Bool × ℕ | i.2 < n i.1} {i | n i.1 ≤ i.2} := by
    apply Set.disjoint_left.mpr
    intro i hi hj
    exact (not_lt_of_ge (show n i.1 ≤ i.2 from hj)) (show i.2 < n i.1 from hi)
  have hind := indep_iSup_of_disjoint (fun i : Bool × ℕ => (measurable_pi_apply (X := fun _ => α) i).comap_le)
    (iIndepFun_infinitePi (P := fun i : Bool × ℕ => ν i.1) (X := fun _ x => x) (fun _ => measurable_id)) hd
  exact (IndepFun_iff_Indep _ _ _).mpr (indep_of_indep_of_le hind hS.comap_le hT.comap_le)

lemma twoCylinder_mass {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)] (a : TwoTapeList α) :
    twoTapeLaw ν (twoCylinder a) = ∏ b : Bool, ∏ i : Fin (a b).1, ν b {(a b).2 i} := by
  classical
  let f : (Σ b : Bool, Fin (a b).1) → Bool × ℕ := fun i => (i.1,i.2)
  have hf : Function.Injective f := by
    rintro ⟨b,i⟩ ⟨c,j⟩ h
    have hb := congrArg Prod.fst h
    change b = c at hb
    subst c
    have hi := congrArg Prod.snd h
    simp only [f] at hi
    exact congrArg (Sigma.mk b) (Fin.ext hi)
  have hm := Measure.map_infinitePi_infinitePi_of_inj (P := fun i : Bool × ℕ => ν i.1) hf
  have he : (fun Z i => Z (f i)) ⁻¹' {fun i : Σ b : Bool, Fin (a b).1 => (a i.1).2 i.2} = twoCylinder a := by
    ext Z
    simp only [Set.mem_preimage,Set.mem_singleton_iff,funext_iff, twoCylinder, Set.mem_ofPred_eq,
      Sigma.forall,f]
  rw [← he,← Measure.map_apply (by fun_prop) (measurableSet_singleton _),twoTapeLaw,hm]
  rw [Measure.infinitePi_singleton_of_fintype]
  exact Fintype.prod_sigma _

lemma twoCylinder_suffix_factorization {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (a : TwoTapeList α) (E : Set (TwoTape α)) (hE : MeasurableSet E) :
    twoTapeLaw ν {Z | Z ∈ twoCylinder a ∧ twoShift (fun b => (a b).1) Z ∈ E} =
      (∏ b : Bool, ∏ i : Fin (a b).1, ν b {(a b).2 i}) * twoTapeLaw ν E := by
  have hh := (two_prefix_suffix_independent ν (fun b => (a b).1)).measure_inter_preimage_eq_mul
    {fun i : Σ b : Bool, Fin (a b).1 => (a i.1).2 i.2} E (measurableSet_singleton _) hE
  have hc : (fun Z (i : Σ b : Bool, Fin (a b).1) => Z (i.1,i.2)) ⁻¹'
      {fun i : Σ b : Bool, Fin (a b).1 => (a i.1).2 i.2} = twoCylinder a := by
    ext Z
    simp only [Set.mem_preimage,Set.mem_singleton_iff,funext_iff,twoCylinder,Set.mem_ofPred_eq,Sigma.forall]
  rw [hc,twoCylinder_mass ν a,← Measure.map_apply (measurable_twoShift _) hE,twoShift_law] at hh
  exact hh

lemma tapeHeight_add {α : Type*} (L : α → ℕ) (Z : ℕ → α) (n m : ℕ) :
    tapeHeight L Z (n+m) = tapeHeight L Z n + tapeHeight L (fun i => Z (n+i)) m := by
  exact Finset.sum_range_add (fun i => L (Z i)) n m

lemma renewalCut_add_iff {α : Type*} (L : α → ℕ) (Z : ℕ → α)
    (hZ : ∀ i, 0 < L (Z i)) {n H : ℕ} (hn : tapeHeight L Z n = H) (J : ℕ) :
    Z ∈ renewalCut L (H+J) ↔ (fun i => Z (n+i)) ∈ renewalCut L J := by
  constructor
  · rintro ⟨k,hk⟩
    have hnk : n ≤ k := (tapeHeight_strictMono L Z hZ).le_iff_le.mp (by omega)
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hnk
    refine ⟨j,?_⟩
    rw [tapeHeight_add,hn] at hk
    omega
  · rintro ⟨j,hj⟩
    exact ⟨n+j,by rw [tapeHeight_add,hn,hj]⟩

def commonCut {α : Type*} (L : Bool → α → ℕ) (H : ℕ) : Set (TwoTape α) :=
  {Z | ∀ b, (fun i => Z (b,i)) ∈ renewalCut (L b) H}

lemma measurableSet_commonCut {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (H : ℕ) : MeasurableSet (commonCut L H) := by
  simp only [commonCut,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun b => (measurableSet_renewalCut (L b) H).preimage (by fun_prop))

lemma commonCut_zero {α : Type*} (L : Bool → α → ℕ) : commonCut L 0 = Set.univ := by
  ext Z; simp only [commonCut,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
  intro b
  exact ⟨0,rfl⟩

noncomputable def commonCutIndices {α : Type*} (L : Bool → α → ℕ) (H : ℕ) (Z : TwoTape α) : Bool → ℕ :=
  fun b => cutListIndex (L b) H (fun i => Z (b,i))

noncomputable def commonCutList {α : Type*} (L : Bool → α → ℕ) (H : ℕ) (Z : TwoTape α) : TwoTapeList α :=
  fun b => cutList (L b) H (fun i => Z (b,i))

noncomputable def afterCommonCut {α : Type*} (L : Bool → α → ℕ) (H : ℕ) (Z : TwoTape α) : TwoTape α :=
  twoShift (commonCutIndices L H Z) Z

lemma measurable_commonCutIndices {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (H : ℕ) : Measurable (commonCutIndices L H) := by
  exact Measurable.of_eval (fun b => (measurable_cutListIndex (L b) H).comp (by fun_prop))

lemma measurable_commonCutList {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (H : ℕ) : Measurable (commonCutList L H) := by
  exact Measurable.of_eval (fun b => (measurable_cutList (L b) H).comp (by fun_prop))

lemma measurable_afterCommonCut {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (H : ℕ) : Measurable (afterCommonCut L H) := by
  have hm : Measurable (fun p : TwoTape α × (Bool → ℕ) => twoShift p.2 p.1) :=
    measurable_from_prod_countable_left (measurable_twoShift (α := α))
  exact hm.comp (measurable_id.prodMk (measurable_commonCutIndices L H))

lemma commonCutList_atom_iff {α : Type*} (L : Bool → α → ℕ) (H : ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (a : TwoTapeList α) :
    (Z ∈ commonCut L H ∧ commonCutList L H Z = a) ↔
      ((∀ b, listHeight (L b) (a b) = H) ∧ Z ∈ twoCylinder a) := by
  constructor
  · rintro ⟨hc,ha⟩
    have hh : ∀ b, listHeight (L b) (a b) = H ∧
        (fun i => Z (b,i)) ∈ tapeCylinder (a b) := fun b =>
      (cutList_atom_iff (L b) H _ (hZ b) (a b)).mp ⟨hc b,congrFun ha b⟩
    exact ⟨fun b => (hh b).1,fun b => (hh b).2⟩
  · rintro ⟨hh,ha⟩
    have hb := fun b => (cutList_atom_iff (L b) H (fun i => Z (b,i)) (hZ b) (a b)).mpr ⟨hh b,ha b⟩
    exact ⟨fun b => (hb b).1,funext (fun b => (hb b).2)⟩

lemma commonCutIndices_eq_lengths {α : Type*} (L : Bool → α → ℕ) (H : ℕ) (Z : TwoTape α)
    (a : TwoTapeList α) (ha : commonCutList L H Z = a) :
    commonCutIndices L H Z = fun b => (a b).1 := by
  funext b
  exact congrArg Sigma.fst (congrFun ha b)

lemma commonCut_add_iff {α : Type*} (L : Bool → α → ℕ) (H : ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (hc : Z ∈ commonCut L H) (J : ℕ) :
    Z ∈ commonCut L (H+J) ↔ afterCommonCut L H Z ∈ commonCut L J := by
  apply forall_congr'
  intro b
  obtain ⟨n,hn⟩ := hc b
  have hi := cutListIndex_eq (L b) H (fun i => Z (b,i)) (hZ b) hn
  change _ ↔ (fun i => Z (b,cutListIndex (L b) H (fun i => Z (b,i))+i)) ∈ renewalCut (L b) J
  rw [hi]
  exact renewalCut_add_iff (L b) _ (hZ b) hn J

lemma commonCut_fibre_tail {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a) (H : ℕ)
    (a : TwoTapeList α) (E : Set (TwoTape α)) (hE : MeasurableSet E) :
    twoTapeLaw ν ({Z | commonCutList L H Z = a} ∩
      (commonCut L H ∩ afterCommonCut L H ⁻¹' E)) =
    twoTapeLaw ν ({Z | commonCutList L H Z = a} ∩ commonCut L H) * twoTapeLaw ν E := by
  classical
  have hZ := ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL
  by_cases ha : ∀ b, listHeight (L b) (a b) = H
  · have h1 : twoTapeLaw ν ({Z | commonCutList L H Z = a} ∩
        (commonCut L H ∩ afterCommonCut L H ⁻¹' E)) =
      twoTapeLaw ν {Z | Z ∈ twoCylinder a ∧ twoShift (fun b => (a b).1) Z ∈ E} := by
      apply measure_congr
      filter_upwards [hZ] with Z hZ
      apply propext
      constructor
      · rintro ⟨hlist,hc,hE⟩
        refine ⟨((commonCutList_atom_iff L H Z hZ a).mp ⟨hc,hlist⟩).2,?_⟩
        simpa only [Set.mem_preimage,afterCommonCut,commonCutIndices_eq_lengths L H Z a hlist] using hE
      · rintro ⟨hpre,hE⟩
        have hh := (commonCutList_atom_iff L H Z hZ a).mpr ⟨ha,hpre⟩
        refine ⟨hh.2,hh.1,?_⟩
        simpa only [Set.mem_preimage,afterCommonCut,commonCutIndices_eq_lengths L H Z a hh.2] using hE
    have h2 : twoTapeLaw ν ({Z | commonCutList L H Z = a} ∩ commonCut L H) =
        twoTapeLaw ν (twoCylinder a) := by
      apply measure_congr
      filter_upwards [hZ] with Z hZ
      apply propext
      constructor
      · rintro ⟨hb,hc⟩; exact ((commonCutList_atom_iff L H Z hZ a).mp ⟨hc,hb⟩).2
      · intro h; have hh := (commonCutList_atom_iff L H Z hZ a).mpr ⟨ha,h⟩; exact ⟨hh.2,hh.1⟩
    rw [h1,h2,twoCylinder_suffix_factorization ν a E hE,twoCylinder_mass]
  · have h0 : twoTapeLaw ν ({Z | commonCutList L H Z = a} ∩ commonCut L H) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hZ] with Z hZ hm
      exact ha ((commonCutList_atom_iff L H Z hZ a).mp ⟨hm.2,hm.1⟩).1
    rw [h0,zero_mul]
    apply measure_mono_null _ h0
    exact fun Z h => ⟨h.1,h.2.1⟩

lemma commonCut_tail_factorization {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a) (H : ℕ)
    (E : Set (TwoTape α)) (hE : MeasurableSet E) :
    twoTapeLaw ν (commonCut L H ∩ afterCommonCut L H ⁻¹' E) =
      twoTapeLaw ν (commonCut L H) * twoTapeLaw ν E := by
  rw [measure_eq_tsum_fibres (twoTapeLaw ν) (commonCutList L H) (measurable_commonCutList L H)
      ((measurableSet_commonCut L H).inter (hE.preimage (measurable_afterCommonCut L H)))]
  simp_rw [commonCut_fibre_tail ν L hL H _ E hE]
  rw [ENNReal.tsum_mul_right,← measure_eq_tsum_fibres (twoTapeLaw ν) (commonCutList L H)
    (measurable_commonCutList L H) (measurableSet_commonCut L H)]

instance twoTapeLaw_probability {α : Type*} [MeasurableSpace α] (ν : Bool → Measure α)
    [∀ b, IsProbabilityMeasure (ν b)] : IsProbabilityMeasure (twoTapeLaw ν) := by
  unfold twoTapeLaw
  infer_instance

lemma twoExtract_independent {α : Type*} [MeasurableSpace α] (ν : Bool → Measure α)
    [∀ b, IsProbabilityMeasure (ν b)] :
    IndepFun (fun Z i => Z (false,i)) (fun Z i => Z (true,i)) (twoTapeLaw ν) := by
  have hS : @Measurable (TwoTape α) (ℕ → α)
      (coordSigma {i | i.1 = false}) _ (fun Z i => Z (false,i)) := by
    let : MeasurableSpace (TwoTape α) := coordSigma {i | i.1 = false}
    exact Measurable.of_eval (fun _ => measurable_coordEval rfl)
  have hT : @Measurable (TwoTape α) (ℕ → α)
      (coordSigma {i | i.1 = true}) _ (fun Z i => Z (true,i)) := by
    let : MeasurableSpace (TwoTape α) := coordSigma {i | i.1 = true}
    exact Measurable.of_eval (fun _ => measurable_coordEval rfl)
  have hd : Disjoint {i : Bool × ℕ | i.1 = false} {i | i.1 = true} := by
    apply Set.disjoint_left.mpr
    intro i hi hj
    exact Bool.false_ne_true (hi.symm.trans hj)
  have hind := indep_iSup_of_disjoint (fun i : Bool × ℕ => (measurable_pi_apply (X := fun _ => α) i).comap_le)
    (iIndepFun_infinitePi (P := fun i : Bool × ℕ => ν i.1) (X := fun _ x => x) (fun _ => measurable_id)) hd
  exact (IndepFun_iff_Indep _ _ _).mpr (indep_of_indep_of_le hind hS.comap_le hT.comap_le)

lemma commonCut_mass {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (H : ℕ) :
    twoTapeLaw ν (commonCut L H) =
      Measure.infinitePi (fun _ : ℕ => ν false) (renewalCut (L false) H) *
      Measure.infinitePi (fun _ : ℕ => ν true) (renewalCut (L true) H) := by
  have hh := (twoExtract_independent ν).measure_inter_preimage_eq_mul
    (renewalCut (L false) H) (renewalCut (L true) H)
    (measurableSet_renewalCut _ _) (measurableSet_renewalCut _ _)
  have he : commonCut L H =
      (fun Z i => Z (false,i)) ⁻¹' renewalCut (L false) H ∩
      (fun Z i => Z (true,i)) ⁻¹' renewalCut (L true) H := by
    ext Z
    exact Bool.forall_bool
  rw [he,hh,← Measure.map_apply (by fun_prop) (measurableSet_renewalCut (L false) H),
    ← Measure.map_apply (by fun_prop) (measurableSet_renewalCut (L true) H),twoExtract_law,twoExtract_law]

def noCommonThrough {α : Type*} (L : Bool → α → ℕ) (N : ℕ) : Set (TwoTape α) :=
  {Z | ∀ i, 0 < i → i ≤ N → Z ∉ commonCut L i}

lemma measurableSet_noCommonThrough {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (N : ℕ) : MeasurableSet (noCommonThrough L N) := by
  simp only [noCommonThrough,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    MeasurableSet.iInter (fun _ => (measurableSet_commonCut L i).compl)))

def lastCommonEvent {α : Type*} (L : Bool → α → ℕ) (N j : ℕ) : Set (TwoTape α) :=
  {Z | Z ∈ commonCut L j ∧ ∀ k, j < k → k ≤ N → Z ∉ commonCut L k}

lemma measurableSet_lastCommonEvent {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (N j : ℕ) : MeasurableSet (lastCommonEvent L N j) := by
  change MeasurableSet (commonCut L j ∩ {Z | ∀ k, j < k → k ≤ N → Z ∉ commonCut L k})
  apply (measurableSet_commonCut L j).inter
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ =>
    MeasurableSet.iInter (fun _ => (measurableSet_commonCut L k).compl)))

lemma lastCommonEvent_disjoint {α : Type*} (L : Bool → α → ℕ) (N : ℕ) :
    (Finset.range (N+1) : Set ℕ).PairwiseDisjoint (lastCommonEvent L N) := by
  intro i hi j hj hij
  apply Set.disjoint_left.mpr
  rintro Z ⟨hci,hli⟩ ⟨hcj,hlj⟩
  have hiN : i ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hjN : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rcases lt_or_gt_of_ne hij with h | h
  · exact hli j h hjN hcj
  · exact hlj i h hiN hci

lemma lastCommonEvent_partition {α : Type*} (L : Bool → α → ℕ) (N : ℕ) :
    (⋃ j ∈ Finset.range (N+1), lastCommonEvent L N j) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro Z
  let s := (Finset.range (N+1)).filter (fun j => Z ∈ commonCut L j)
  have h0 : 0 ∈ s := by simp [s,commonCut_zero]
  let j := s.max' ⟨0,h0⟩
  have hj := s.max'_mem ⟨0,h0⟩
  obtain ⟨hjN,hcut⟩ := Finset.mem_filter.mp hj
  refine Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hjN,hcut,?_⟩⟩
  intro k hjk hkN hk
  have hks : k ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hk⟩
  exact (not_le_of_gt hjk) (s.le_max' k hks)

lemma lastCommonEvent_tail {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (N j : ℕ) (hj : j ≤ N) :
    Z ∈ lastCommonEvent L N j ↔
      Z ∈ commonCut L j ∩ afterCommonCut L j ⁻¹' noCommonThrough L (N-j) := by
  constructor
  · rintro ⟨hc,hl⟩
    refine ⟨hc,fun i hi hiN hcut => ?_⟩
    exact hl (j+i) (by omega) (by omega) ((commonCut_add_iff L j Z hZ hc i).mpr hcut)
  · rintro ⟨hc,hl⟩
    refine ⟨hc,fun k hjk hkN hcut => ?_⟩
    apply hl (k-j) (by omega) (by omega)
    apply (commonCut_add_iff L j Z hZ hc (k-j)).mp
    simpa only [Nat.add_sub_of_le hjk.le] using hcut

lemma lastCommonEvent_mass {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a) (N j : ℕ) (hj : j ≤ N) :
    twoTapeLaw ν (lastCommonEvent L N j) =
      twoTapeLaw ν (commonCut L j) * twoTapeLaw ν (noCommonThrough L (N-j)) := by
  rw [← commonCut_tail_factorization ν L hL j _ (measurableSet_noCommonThrough L _)]
  apply measure_congr
  filter_upwards [ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL] with Z hZ
  exact propext (lastCommonEvent_tail L Z hZ N j hj)

lemma common_renewal_tail_identity {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a) (N : ℕ) :
    ∑ j ∈ Finset.range (N+1), twoTapeLaw ν (commonCut L j) *
      twoTapeLaw ν (noCommonThrough L (N-j)) = 1 := by
  calc
    _ = ∑ j ∈ Finset.range (N+1), twoTapeLaw ν (lastCommonEvent L N j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (lastCommonEvent_mass ν L hL N j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).symm
    _ = twoTapeLaw ν (⋃ j ∈ Finset.range (N+1), lastCommonEvent L N j) := by
      exact (measure_biUnion_finset (lastCommonEvent_disjoint L N)
        (fun j _ => measurableSet_lastCommonEvent L N j)).symm
    _ = 1 := by rw [lastCommonEvent_partition,measure_univ]

lemma common_renewal_tail_sum_bound {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a) (c : ℝ≥0∞)
    (hc : ∀ H, c ≤ twoTapeLaw ν (commonCut L H)) :
    c * ∑' N, twoTapeLaw ν (noCommonThrough L N) ≤ 1 := by
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  cases n with
  | zero => simp
  | succ N =>
    have h := common_renewal_tail_identity ν L hL N
    calc
      _ = ∑ j ∈ Finset.range (N+1), c * twoTapeLaw ν (noCommonThrough L (N-j)) := by
        exact (Finset.sum_range_reflect (fun j => c * twoTapeLaw ν (noCommonThrough L j)) (N+1)).symm
      _ ≤ ∑ j ∈ Finset.range (N+1), twoTapeLaw ν (commonCut L j) *
          twoTapeLaw ν (noCommonThrough L (N-j)) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul' (hc j) le_rfl)
      _ = 1 := h

end DirectionalZeroOne

end OAI
