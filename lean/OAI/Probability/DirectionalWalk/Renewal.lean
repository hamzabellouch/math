import OAI.Probability.DirectionalWalk.Axis

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

abbrev TapeList (α : Type*) := Σ n : ℕ, Fin n → α

instance tapeListMeasurableSpace (α : Type*) : MeasurableSpace (TapeList α) := ⊤
instance tapeListMeasurableSingletonClass (α : Type*) : MeasurableSingletonClass (TapeList α) :=
  ⟨fun _ => trivial⟩

def tapePrefix {α : Type*} (n : ℕ) (Z : ℕ → α) : TapeList α := ⟨n,fun i => Z i⟩

def tapeCylinder {α : Type*} (a : TapeList α) : Set (ℕ → α) :=
  {Z | ∀ i : Fin a.1, Z i = a.2 i}

lemma measurableSet_tapeCylinder {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (a : TapeList α) : MeasurableSet (tapeCylinder a) := by
  simp only [tapeCylinder,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => (measurableSet_singleton (a.2 i)).preimage (measurable_pi_apply (i : ℕ)))

lemma tapePrefix_eq_iff {α : Type*} (n : ℕ) (Z : ℕ → α) (a : TapeList α) :
    tapePrefix n Z = a ↔ n = a.1 ∧ Z ∈ tapeCylinder a := by
  rcases a with ⟨m,a⟩
  constructor
  · intro h
    have hn := congrArg Sigma.fst h
    change n = m at hn
    subst m
    have ha : (fun i : Fin n => Z i) = a := by simpa [tapePrefix] using h
    exact ⟨rfl,fun i => congrFun ha i⟩
  · rintro ⟨rfl,ha⟩
    exact congrArg (Sigma.mk n) (funext ha)

lemma measurable_tapePrefix {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (n : ℕ) : Measurable (tapePrefix (α := α) n) := by
  apply measurable_to_countable'
  intro a
  have he : tapePrefix n ⁻¹' {a} = {Z : ℕ → α | n = a.1} ∩ tapeCylinder a := by
    ext Z; exact tapePrefix_eq_iff n Z a
  rw [he]
  exact (MeasurableSet.const _).inter (measurableSet_tapeCylinder a)

lemma tapeCylinder_mass {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν] (a : TapeList α) :
    Measure.infinitePi (fun _ : ℕ => ν) (tapeCylinder a) = ∏ i : Fin a.1, ν {a.2 i} := by
  have hm := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => ν)
    (f := fun i : Fin a.1 => (i : ℕ)) Fin.val_injective
  have he : tapeCylinder a = (fun Z (i : Fin a.1) => Z i) ⁻¹' {a.2} := by
    ext Z
    simp only [tapeCylinder,Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_singleton_iff,funext_iff]
  rw [he,← Measure.map_apply (by fun_prop) (measurableSet_singleton _),hm,
    Measure.infinitePi_singleton_of_fintype]

def tapeHeight {α : Type*} (L : α → ℕ) (Z : ℕ → α) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, L (Z i)

def listHeight {α : Type*} (L : α → ℕ) (a : TapeList α) : ℕ :=
  ∑ i : Fin a.1, L (a.2 i)

lemma listHeight_prefix {α : Type*} (L : α → ℕ) (Z : ℕ → α) (n : ℕ) :
    listHeight L (tapePrefix n Z) = tapeHeight L Z n := by
  exact Fin.sum_univ_eq_sum_range (fun i => L (Z i)) n

lemma tapeHeight_mono {α : Type*} (L : α → ℕ) (Z : ℕ → α) : Monotone (tapeHeight L Z) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [tapeHeight,Finset.sum_range_succ]
  omega

lemma tapeHeight_strictMono {α : Type*} (L : α → ℕ) (Z : ℕ → α)
    (hZ : ∀ i, 0 < L (Z i)) : StrictMono (tapeHeight L Z) := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [tapeHeight,Finset.sum_range_succ]
  have := hZ n
  omega

lemma le_tapeHeight {α : Type*} (L : α → ℕ) (Z : ℕ → α)
    (hZ : ∀ i, 0 < L (Z i)) (n : ℕ) : n ≤ tapeHeight L Z n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    simp only [tapeHeight,Finset.sum_range_succ] at *
    have := hZ n
    omega

lemma measurable_tapeHeight {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : α → ℕ) (n : ℕ) : Measurable (fun Z => tapeHeight L Z n) := by
  exact Finset.measurable_sum _ (fun i _ => (measurable_of_countable L).comp (measurable_pi_apply (i : ℕ)))

noncomputable def cutListIndex {α : Type*} (L : α → ℕ) (H : ℕ) (Z : ℕ → α) : ℕ := by
  classical
  exact Nat.findGreatest (fun n => tapeHeight L Z n = H) H

lemma measurable_cutListIndex {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : α → ℕ) (H : ℕ) : Measurable (cutListIndex L H) := by
  classical
  apply measurable_findGreatest
  intro n _
  exact measurableSet_eq_fun (measurable_tapeHeight L n) measurable_const

lemma cutListIndex_eq {α : Type*} (L : α → ℕ) (H : ℕ) (Z : ℕ → α)
    (hZ : ∀ i, 0 < L (Z i)) {n : ℕ} (hn : tapeHeight L Z n = H) : cutListIndex L H Z = n := by
  classical
  have hnH : n ≤ H := hn ▸ le_tapeHeight L Z hZ n
  have he : tapeHeight L Z (cutListIndex L H Z) = H :=
    Nat.findGreatest_spec (P := fun n => tapeHeight L Z n = H) hnH hn
  exact (tapeHeight_strictMono L Z hZ).injective (he.trans hn.symm)

noncomputable def cutList {α : Type*} (L : α → ℕ) (H : ℕ) (Z : ℕ → α) : TapeList α :=
  tapePrefix (cutListIndex L H Z) Z

lemma measurable_cutList {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : α → ℕ) (H : ℕ) : Measurable (cutList L H) := by
  apply measurable_to_countable'
  intro a
  have he : cutList L H ⁻¹' {a} = {Z | cutListIndex L H Z = a.1} ∩ tapeCylinder a := by
    ext Z; exact tapePrefix_eq_iff (cutListIndex L H Z) Z a
  rw [he]
  exact (measurableSet_eq_fun (measurable_cutListIndex L H) measurable_const).inter
    (measurableSet_tapeCylinder a)

def renewalCut {α : Type*} (L : α → ℕ) (H : ℕ) : Set (ℕ → α) :=
  {Z | ∃ n, tapeHeight L Z n = H}

lemma measurableSet_renewalCut {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : α → ℕ) (H : ℕ) : MeasurableSet (renewalCut L H) := by
  simp only [renewalCut,Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun n => measurableSet_eq_fun (measurable_tapeHeight L n) measurable_const)

lemma cutList_atom_iff {α : Type*} (L : α → ℕ) (H : ℕ) (Z : ℕ → α)
    (hZ : ∀ i, 0 < L (Z i)) (a : TapeList α) :
    (Z ∈ renewalCut L H ∧ cutList L H Z = a) ↔
      (listHeight L a = H ∧ Z ∈ tapeCylinder a) := by
  constructor
  · rintro ⟨⟨n,hn⟩,ha⟩
    have hi := cutListIndex_eq L H Z hZ hn
    have ha' : tapePrefix n Z = a := by simpa only [cutList,hi] using ha
    refine ⟨?_,((tapePrefix_eq_iff n Z a).mp ha').2⟩
    rw [← ha',listHeight_prefix,hn]
  · rintro ⟨hH,ha⟩
    have he : tapePrefix a.1 Z = a := (tapePrefix_eq_iff _ _ _).mpr ⟨rfl,ha⟩
    have hh : tapeHeight L Z a.1 = H := by rw [← listHeight_prefix,he,hH]
    exact ⟨⟨a.1,hh⟩,by rw [cutList,cutListIndex_eq L H Z hZ hh,he]⟩

lemma ae_tape_prop {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (p : α → Prop) (hp : MeasurableSet {a | p a}) (h : ∀ᵐ a ∂ν, p a) :
    ∀ᵐ Z ∂Measure.infinitePi (fun _ : ℕ => ν), ∀ i, p (Z i) := by
  rw [ae_all_iff]
  intro i
  apply (ae_map_iff (measurable_pi_apply i).aemeasurable hp).mp
  rw [Measure.infinitePi_map_eval]
  exact h

noncomputable def bridgeListMeasure {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (L : α → ℕ) (H : ℕ) : Measure (TapeList α) :=
  ((Measure.infinitePi (fun _ : ℕ => ν)).restrict (renewalCut L H)).map (cutList L H)

lemma bridgeListMeasure_mass {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (H : ℕ) :
    bridgeListMeasure ν L H Set.univ = Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H) := by
  rw [bridgeListMeasure,Measure.map_apply (measurable_cutList L H) MeasurableSet.univ]
  simp

lemma bridgeListMeasure_atom {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hL : ∀ᵐ a ∂ν, 0 < L a) (H : ℕ) (a : TapeList α) :
    bridgeListMeasure ν L H {a} =
      if listHeight L a = H then ∏ i : Fin a.1, ν {a.2 i} else 0 := by
  classical
  rw [bridgeListMeasure,Measure.map_apply (measurable_cutList L H) (measurableSet_singleton _),
    Measure.restrict_apply ((measurable_cutList L H) (measurableSet_singleton _))]
  have hZ := ae_tape_prop ν (fun x => 0 < L x)
    (measurableSet_lt measurable_const (measurable_of_countable L)) hL
  by_cases hH : listHeight L a = H
  · rw [ite_eq_left hH,← tapeCylinder_mass ν a]
    apply measure_congr
    filter_upwards [hZ] with Z hZ
    apply propext
    constructor
    · intro h
      exact ((cutList_atom_iff L H Z hZ a).mp ⟨h.2,h.1⟩).2
    · intro h
      have hh := (cutList_atom_iff L H Z hZ a).mpr ⟨hH,h⟩
      exact ⟨hh.2,hh.1⟩
  · rw [ite_eq_right hH]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hZ] with Z hZ hm
    exact hH ((cutList_atom_iff L H Z hZ a).mp ⟨hm.2,hm.1⟩).1

def reverseTapeList {α : Type*} (a : TapeList α) : TapeList α := ⟨a.1,fun i => a.2 i.rev⟩

lemma reverseTapeList_involutive {α : Type*} : Function.Involutive (reverseTapeList (α := α)) := by
  rintro ⟨n,a⟩
  simp only [reverseTapeList,Fin.rev_rev]

lemma listHeight_reverse {α : Type*} (L : α → ℕ) (a : TapeList α) :
    listHeight L (reverseTapeList a) = listHeight L a := by
  exact Equiv.sum_comp Fin.revPerm (fun i => L (a.2 i))

lemma listProduct_reverse {α M : Type*} [CommMonoid M] (f : α → M) (a : TapeList α) :
    (∏ i : Fin (reverseTapeList a).1, f ((reverseTapeList a).2 i)) = ∏ i : Fin a.1, f (a.2 i) := by
  exact Equiv.prod_comp Fin.revPerm (fun i => f (a.2 i))

lemma bridgeListMeasure_reverse {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hL : ∀ᵐ a ∂ν, 0 < L a) (H : ℕ) :
    (bridgeListMeasure ν L H).map reverseTapeList = bridgeListMeasure ν L H := by
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : reverseTapeList ⁻¹' {a} = {reverseTapeList a} := by
    ext b
    exact reverseTapeList_involutive.eq_iff
  rw [he,bridgeListMeasure_atom ν L hL H _,bridgeListMeasure_atom ν L hL H _,
    listHeight_reverse,listProduct_reverse (fun x => ν {x}) a]

noncomputable def bridgeListLaw {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (L : α → ℕ) (H : ℕ) : Measure (TapeList α) :=
  (Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H))⁻¹ • bridgeListMeasure ν L H

lemma bridgeListLaw_probability {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (H : ℕ)
    (hH : Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H) ≠ 0) :
    IsProbabilityMeasure (bridgeListLaw ν L H) := by
  constructor
  rw [bridgeListLaw,Measure.smul_apply,smul_eq_mul,bridgeListMeasure_mass,
    ENNReal.inv_mul_cancel hH (measure_ne_top _ _)]

lemma bridgeListLaw_atom {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hL : ∀ᵐ a ∂ν, 0 < L a) (H : ℕ) (a : TapeList α)
    (ha : listHeight L a = H) : bridgeListLaw ν L H {a} =
      (Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H))⁻¹ * ∏ i : Fin a.1, ν {a.2 i} := by
  rw [bridgeListLaw,Measure.smul_apply,smul_eq_mul,bridgeListMeasure_atom ν L hL H a,ite_eq_left ha]

lemma bridgeListLaw_reverse {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hL : ∀ᵐ a ∂ν, 0 < L a) (H : ℕ) :
    (bridgeListLaw ν L H).map reverseTapeList = bridgeListLaw ν L H := by
  rw [bridgeListLaw,Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    bridgeListMeasure_reverse ν L hL H]

end DirectionalZeroOne

end OAI
