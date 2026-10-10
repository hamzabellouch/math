import Mathlib.Data.List.OfFn
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Local.ConfigurationReuse
import OAI.Combinatorics.BalancedRyser.Local.LocalKernel
import OAI.Combinatorics.BalancedRyser.Local.ReuseScore

namespace OAI

namespace Balanced.ReusePrescription

open Local Local.KernelBridge
open scoped BigOperators

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev Code (F : Type*) := Slot F × Local.TupleCode F

def generators (c : Code F) : Finset (Direction F) :=
  generatorSet (decodeTuple c.2)

def TupleEligible (c : Code F) : Prop :=
  Function.Injective c.2.1 ∧ ∀ i, c.2.1 i ≠ c.1.1

def Eligible (l : List (Code F)) : Prop :=
  (l.map Prod.fst).Nodup ∧ (∀ c ∈ l, TupleEligible c) ∧
    3 ≤ reuseExposureScore generators l

def AlignedExternal (p : Point F) (l : List (Code F)) (M : MergedPairs F) : Prop :=
  ∀ c ∈ l,
    (∀ i, OnLine (tuplePoint M (decodeTuple c.2) i) (lineThrough c.1.1 p)) ∧
    ∀ i, tuplePoint M (decodeTuple c.2) i ≠ p

def Matches (l : List (Code F)) (C : Configuration F) : Prop :=
  ∀ c ∈ l, encodeTuple (C.choice c.1).tuple = c.2

def encode (C : Configuration F) (s : Slot F) : Code F :=
  (s, encodeTuple (C.choice s).tuple)

theorem reuseExposureScore_map {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (A : β → Finset γ) (f : α → β) (l : List α) :
    reuseExposureScore A (l.map f) = reuseExposureScore (fun x => A (f x)) l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hset : (l.map f).toFinset.biUnion A =
        l.toFinset.biUnion (fun x => A (f x)) := by
      ext x
      simp
    simp only [List.map_cons, reuseExposureScore, ih, hset]

theorem exists_of_configuration (C : Configuration F)
    (hv : C.Valid) (hc : C.Compatible) (p : Point F)
    (hb : 2 ≤ C.splitMultiplicity p) (hr : 3 ≤ reuseCount C p) :
    ∃ l : List (Code F), l.length ≤ 6 ∧ Eligible l ∧
      AlignedExternal p l C.merged ∧ Matches l C := by
  obtain ⟨l, hnd, hthrough, hlen, hscore⟩ :=
    C.exists_pencil_reuse_witness hv hc p hr
  refine ⟨l.map (encode C), by simpa using hlen, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simpa [encode, List.map_map, Function.comp_def] using hnd
    · intro c hc'
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc'
      exact ⟨(hv.2 s).2.2.1, (hv.2 s).2.2.2.1⟩
    · simpa [reuseExposureScore_map, generators, encode] using hscore
  · intro c hc'
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc'
    have heq : (C.choice s).line = lineThrough s.1 p := by
      rw [line_eq_lineThrough p _ (hthrough s hs), (hv.2 s).1]
    constructor
    · intro i
      simpa [encode, heq] using (hv.2 s).2.2.2.2.2.1 i
    · intro i
      simpa [encode] using C.tuplePoint_ne_pencil_center hc p hb s i
  · intro c hc'
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc'
    rfl

def slots (l : List (Code F)) : Finset (Slot F) := (l.map Prod.fst).toFinset

def codeAt (l : List (Code F)) (s : Slot F) : TupleCode F :=
  if h : ∃ c ∈ l, c.1 = s then (Classical.choose h).2
  else (fun _ => none, fun _ => false)

omit [Field F] [Fintype F] in
theorem matches_codeAt {l : List (Code F)} {C : Configuration F}
    (h : Matches l C) :
    ∀ s ∈ slots l, encodeTuple (C.choice s).tuple = codeAt l s := by
  intro s hs
  have hex : ∃ c ∈ l, c.1 = s := by
    simpa [slots] using hs
  obtain ⟨hc, heq⟩ := Classical.choose_spec hex
  rw [codeAt, dite_eq_left hex]
  exact (congrArg (fun t => encodeTuple (C.choice t).tuple) heq).symm.trans (h _ hc)

omit [Field F] [Fintype F] in
theorem slots_card {l : List (Code F)} (h : (l.map Prod.fst).Nodup) :
    (slots l).card = l.length := by
  simp [slots, List.toFinset_card_of_nodup h]

theorem selected_list_le (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hw : KernelConditions Q w K) (p : Point F) (l : List (Code F))
    (hnd : (l.map Prod.fst).Nodup) :
    selectedProbability w (fun C => AlignedExternal p l C.merged ∧ Matches l C) ≤
      (K / Fintype.card F) ^ l.length * offsetProbability (AlignedExternal p l) := by
  calc
    _ ≤ selectedProbability w (fun C => AlignedExternal p l C.merged ∧
        ∀ s ∈ slots l, encodeTuple (C.choice s).tuple = codeAt l s) :=
      selectedProbability_mono w hw.1 (fun _ h => ⟨h.1, matches_codeAt h.2⟩)
    _ ≤ (K / Fintype.card F) ^ (slots l).card *
        offsetProbability (AlignedExternal p l) :=
      selected_prescription_and_offset_le Q w K hw (slots l)
        (fun _ => codeAt l) (AlignedExternal p l)
    _ = _ := by rw [slots_card hnd]

theorem selected_union_le {ι : Type*} (S : Finset ι)
    (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v)
    (E : Configuration F → Prop) (A : ι → Configuration F → Prop)
    (hcover : ∀ M v, 0 < w M v → E (configuration M v) →
      ∃ i ∈ S, A i (configuration M v)) :
    selectedProbability w E ≤ ∑ i ∈ S, selectedProbability w (A i) := by
  have hpoint (M : MergedPairs F) (v : Output F) :
      (if E (configuration M v) then w M v else 0) ≤
        ∑ i ∈ S, if A i (configuration M v) then w M v else 0 := by
    have hn i : 0 ≤ if A i (configuration M v) then w M v else 0 := by
      split_ifs <;> simp_all
    by_cases hE : E (configuration M v)
    · simp only [hE, ite_true]
      by_cases hz : w M v = 0
      · simp [hz]
      · obtain ⟨i, hi, hA⟩ := hcover M v (lt_of_le_of_ne (hw M v) (Ne.symm hz)) hE
        calc
          w M v = if A i (configuration M v) then w M v else 0 := by simp [hA]
          _ ≤ ∑ j ∈ S, if A j (configuration M v) then w M v else 0 :=
            Finset.single_le_sum (fun j _ => hn j) hi
    · simp only [hE, ite_false]
      exact Finset.sum_nonneg (fun i _ => hn i)
  unfold selectedProbability
  calc
    _ ≤ (∑ M : MergedPairs F, ∑ v : Output F,
        ∑ i ∈ S, if A i (configuration M v) then w M v else 0) /
        Fintype.card (MergedPairs F) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact Finset.sum_le_sum (fun M _ => Finset.sum_le_sum (fun v _ => hpoint M v))
    _ = _ := by
      simp_rw [Finset.sum_div]
      let f (M : MergedPairs F) (v : Output F) (i : ι) : ℝ :=
        (if A i (configuration M v) then w M v else 0) /
          Fintype.card (MergedPairs F)
      change (∑ M, ∑ v, ∑ i ∈ S, f M v i) = ∑ i ∈ S, ∑ M, ∑ v, f M v i
      calc
        _ = ∑ M, ∑ i ∈ S, ∑ v, f M v i :=
          Finset.sum_congr rfl (fun M _ => Finset.sum_comm)
        _ = _ := Finset.sum_comm

def allLists (α : Type*) [Fintype α] [DecidableEq α] : ℕ → Finset (List α)
  | 0 => {[]}
  | n + 1 => Finset.univ.biUnion (fun a => (allLists α n).image (List.cons a))

@[simp] theorem mem_allLists {α : Type*} [Fintype α] [DecidableEq α]
    (l : List α) (n : ℕ) : l ∈ allLists α n ↔ l.length = n := by
  induction n generalizing l with
  | zero => simp [allLists]
  | succ n ih =>
    cases l with
    | nil => simp [allLists]
    | cons a l => simp [allLists, ih]

def witnesses (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Finset (List (Code F)) :=
  (Finset.range 7).biUnion (fun n => (allLists (Code F) n).filter Eligible)

@[simp] theorem mem_witnesses (l : List (Code F)) :
    l ∈ witnesses F ↔ l.length ≤ 6 ∧ Eligible l := by
  simp only [witnesses, Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter,
    mem_allLists]
  constructor
  · rintro ⟨n, hn, hlen, hel⟩
    exact ⟨by omega, hel⟩
  · rintro ⟨hlen, hel⟩
    exact ⟨l.length, by omega, rfl, hel⟩

theorem selected_reuse_le_witness_sum
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hw : KernelConditions Q w K) (p : Point F) :
    selectedProbability w (fun C => 2 ≤ C.splitMultiplicity p ∧ 3 ≤ reuseCount C p) ≤
      ∑ l ∈ witnesses F,
        (K / Fintype.card F) ^ l.length * offsetProbability (AlignedExternal p l) := by
  calc
    _ ≤ ∑ l ∈ witnesses F,
        selectedProbability w (fun C => AlignedExternal p l C.merged ∧ Matches l C) := by
      apply selected_union_le (witnesses F) w hw.1
      intro M v hpos hevent
      obtain ⟨hv, hc, _⟩ := hw.2.2.1 M v hpos
      obtain ⟨l, hlen, hel, halt, hmatch⟩ :=
        exists_of_configuration (configuration M v) hv hc p hevent.1 hevent.2
      exact ⟨l, mem_witnesses l |>.mpr ⟨hlen, hel⟩, halt, hmatch⟩
    _ ≤ _ := Finset.sum_le_sum (fun l hl =>
      selected_list_le Q w K hw p l ((mem_witnesses l).mp hl).2.1)

theorem allLists_eq_image {α : Type*} [Fintype α] [DecidableEq α] (n : ℕ) :
    allLists α n = (Finset.univ : Finset (Fin n → α)).image List.ofFn := by
  ext l
  rw [mem_allLists, Finset.mem_image]
  constructor
  · intro hlen
    subst n
    exact ⟨l.get, Finset.mem_univ _, List.ofFn_get l⟩
  · rintro ⟨f, _, rfl⟩
    simp

theorem sum_allLists {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (f : List α → ℝ) :
    (∑ l ∈ allLists α n, f l) = ∑ t : Fin n → α, f (List.ofFn t) := by
  rw [allLists_eq_image, Finset.sum_image]
  exact fun a _ b _ h => List.ofFn_injective h

omit [Fintype F] [DecidableEq F] in
theorem alignedExternal_eq_prefixEvent (p : Point F) (l : List (Code F))
    (hel : ∀ c ∈ l, TupleEligible c) :
    AlignedExternal p l = ReuseTower.prefixEvent p l := by
  funext M
  apply propext
  rw [ReuseTower.prefixEvent_iff]
  exact ⟨fun h => ⟨hel, h⟩, fun h => h.2⟩

theorem witness_weight_eq (K : ℝ) (p : Point F) (l : List (Code F))
    (hel : Eligible l) :
    (K / Fintype.card F) ^ l.length * offsetProbability (AlignedExternal p l) =
      ReuseTower.prefixWeight K p l := by
  rw [ReuseTower.prefixWeight, alignedExternal_eq_prefixEvent p l hel.2.1]

theorem selected_reuse_le_prefix_sum
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hw : KernelConditions Q w K) (p : Point F) :
    selectedProbability w (fun C => 2 ≤ C.splitMultiplicity p ∧ 3 ≤ reuseCount C p) ≤
      ∑ l ∈ witnesses F, ReuseTower.prefixWeight K p l := by
  calc
    _ ≤ _ := selected_reuse_le_witness_sum Q w K hw p
    _ = _ := Finset.sum_congr rfl (fun l hl =>
      witness_weight_eq K p l ((mem_witnesses l).mp hl).2)

theorem witness_prefix_sum_le
    (K : ℝ) (hK : 0 ≤ K) (p : Point F) :
    (∑ l ∈ witnesses F, ReuseTower.prefixWeight K p l) ≤
      ∑ n ∈ Finset.range 7, ∑ t : Fin n → Code F,
        if 3 ≤ ReuseTower.prefixScore (List.ofFn t)
        then ReuseTower.prefixWeight K p (List.ofFn t) else 0 := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range 7) : Set ℕ)
      (fun n => (allLists (Code F) n).filter Eligible) := by
    intro n hn m hm hne
    apply Finset.disjoint_left.mpr
    intro l hln hlm
    have hn' := (mem_allLists l n).mp (Finset.mem_filter.mp hln).1
    have hm' := (mem_allLists l m).mp (Finset.mem_filter.mp hlm).1
    exact hne (hn'.symm.trans hm')
  rw [witnesses, Finset.sum_biUnion hdisj]
  apply Finset.sum_le_sum
  intro n hn
  calc
    _ ≤ ∑ l ∈ (allLists (Code F) n).filter
          (fun l => 3 ≤ reuseExposureScore generators l), ReuseTower.prefixWeight K p l := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro l hl
        obtain ⟨hl, hel⟩ := Finset.mem_filter.mp hl
        exact Finset.mem_filter.mpr ⟨hl, hel.2.2⟩
      · intro l _ _
        exact ReuseTower.prefixWeight_nonneg K hK p l
    _ = ∑ t : Fin n → Code F,
        if 3 ≤ reuseExposureScore generators (List.ofFn t)
        then ReuseTower.prefixWeight K p (List.ofFn t) else 0 := by
      rw [Finset.sum_filter, sum_allLists]
    _ = _ := Finset.sum_congr rfl (fun t _ =>
      ReuseTower.score_cutoff_weight_eq K p (List.ofFn t) 3)

theorem selected_reuse_le_function_sum
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ) (hK : 0 ≤ K)
    (hw : KernelConditions Q w K) (p : Point F) :
    selectedProbability w (fun C => 2 ≤ C.splitMultiplicity p ∧ 3 ≤ reuseCount C p) ≤
      ∑ n ∈ Finset.range 7, ∑ t : Fin n → ReuseTower.Prescription F,
        if 3 ≤ ReuseTower.prefixScore (List.ofFn t)
        then ReuseTower.prefixWeight K p (List.ofFn t) else 0 :=
  (selected_reuse_le_prefix_sum Q w K hw p).trans (witness_prefix_sum_le K hK p)

theorem sum_allLists_reverse {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (f : List α → ℝ) :
    (∑ l ∈ allLists α n, f l) = ∑ l ∈ allLists α n, f l.reverse := by
  apply Finset.sum_bij (fun l _ => l.reverse)
  · intro l hl
    simpa using hl
  · intro a ha b hb hab
    exact List.reverse_injective hab
  · intro l hl
    exact ⟨l.reverse, by simpa using hl, by simp⟩
  · intro l hl
    simp

theorem sum_ofFn_eq_sum_reverse {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (f : List α → ℝ) :
    (∑ t : Fin n → α, f (List.ofFn t)) =
      ∑ t : Fin n → α, f (List.ofFn t).reverse := by
  calc
    _ = ∑ l ∈ allLists α n, f l := (sum_allLists n f).symm
    _ = ∑ l ∈ allLists α n, f l.reverse := sum_allLists_reverse n f
    _ = _ := sum_allLists n (fun l => f l.reverse)

theorem selected_reuse_le_reversed_function_sum
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ) (hK : 0 ≤ K)
    (hw : KernelConditions Q w K) (p : Point F) :
    selectedProbability w (fun C => 2 ≤ C.splitMultiplicity p ∧ 3 ≤ reuseCount C p) ≤
      ∑ n ∈ Finset.range 7, ∑ t : Fin n → ReuseTower.Prescription F,
        if 3 ≤ ReuseTower.prefixScore (List.ofFn t).reverse
        then ReuseTower.prefixWeight K p (List.ofFn t).reverse else 0 := by
  calc
    _ ≤ _ := selected_reuse_le_function_sum Q w K hK hw p
    _ = _ := Finset.sum_congr rfl (fun n _ => sum_ofFn_eq_sum_reverse n
      (fun l => if 3 ≤ ReuseTower.prefixScore l then ReuseTower.prefixWeight K p l else 0))

end
end Balanced.ReusePrescription

end OAI
