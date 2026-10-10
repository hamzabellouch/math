import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.FiniteContext
import OAI.Combinatorics.KMedianRecovery.Geometry.AllBadCostBound
import OAI.Combinatorics.KMedianRecovery.Recovery.NatConnection

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalSets
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
def swapWords (x : List Bool) : List Bool := pairBits (discardPrefix x,extractPrefix x)
noncomputable def swapWords_computes : PolyComputes swapWords := discardPrefix_computes.pair extractPrefix_computes
noncomputable def addOne (x : List Bool) : List Bool := BinaryLabel.sort (cons (extractPrefix x) (discardPrefix x))
noncomputable def addOne_computes : PolyComputes addOne :=
  (cons_computes extractPrefix_computes discardPrefix_computes).comp BinaryLabel.sort_computes
lemma addOne_pack {m : ℕ} (a : Label (Fin m)) (S : Finset (Label (Fin m))) :
    addOne (pairBits (BinaryLabel.encode a,setBits S))=setBits (insert a S) := by
  simp only [addOne,extractPrefix_pairBits,discardPrefix_pairBits]
  change BinaryLabel.sort (encode ((a::BinaryLabel.orderedSort S).map BinaryLabel.encode))=setBits (insert a S)
  rw [BinaryLabel.sort_encode]
  simp only [List.toFinset_cons,BinaryLabel.orderedSort,Finset.sort_toFinset,setBits,labels]

noncomputable def without (x : List Bool) : Bool := !BinaryLabel.contains (swapWords x)
noncomputable def without_computes : PolyComputes (fun x=>[without x]) :=
  (swapWords_computes.comp BinaryLabel.contains_computes).not
noncomputable def diff (x : List Bool) : List Bool := BinaryLabel.sort (filterWith without (swapWords x))
noncomputable def diff_computes : PolyComputes diff :=
  (swapWords_computes.comp (filterWith_computes without_computes)).comp BinaryLabel.sort_computes
lemma diff_pack {m : ℕ} (S T : Finset (Label (Fin m))) :
    diff (pairBits (setBits S,setBits T))=setBits (S\T) := by
  simp only [diff,swapWords,extractPrefix_pairBits,discardPrefix_pairBits,setBits,labels,filterWith_encode,
    List.filter_map,Function.comp_def,without,BinaryLabel.contains_encode]
  rw [BinaryLabel.sort_encode]
  apply congrArg (fun S : Finset (Label (Fin m))=>encode ((BinaryLabel.orderedSort S).map BinaryLabel.encode))
  ext a
  simp only [List.mem_toFinset,List.mem_filter,Bool.not_eq_true',decide_eq_false_iff_not,
    BinaryLabel.orderedSort,Finset.mem_sort,Finset.mem_sdiff]
noncomputable def size : List Bool→List Bool := UnaryResources.lengthBits ∘ Count.run
noncomputable def size_computes : PolyComputes size := Count.run_computes.comp UnaryResources.lengthBits_computes
lemma size_pack {m : ℕ} (S : Finset (Label (Fin m))) : size (setBits S)=S.card.bits := by
  simp only [size,Function.comp_apply,setBits,labels,Count.run_encode,UnaryResources.lengthBits_eq,
    List.length_replicate,List.length_map,BinaryLabel.orderedSort,Finset.length_sort]
noncomputable def insertEach : List Bool→List Bool := mapWith addOne ∘ swapWords
noncomputable def insertEach_computes : PolyComputes insertEach := swapWords_computes.comp (mapWith_computes addOne_computes)
lemma insertEach_pack {m : ℕ} (ss : List (Finset (Label (Fin m)))) (a : Label (Fin m)) :
    insertEach (pairBits (encode (ss.map setBits),BinaryLabel.encode a))=encode ((ss.map (insert a)).map setBits) := by
  simp only [insertEach,Function.comp_apply,swapWords,extractPrefix_pairBits,discardPrefix_pairBits,
    mapWith_encode,List.map_map,Function.comp_def,addOne_pack]
end MetricKMedianRecovery.BitMachine.BinaryLocalSets

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [DecidableEq V]

def widthLists (fs : List V) : ℕ → List (Finset V)
  | 0 => [∅]
  | w+1 => widthLists fs w ++ fs.flatMap (fun i => (widthLists fs w).map (insert i))

omit [DecidableEq V] in
lemma sum_map_constant (fs : List V) (n : ℕ) : (fs.map (fun _ => n)).sum = fs.length*n := by
  induction fs with
  | nil => simp
  | cons a fs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.add_mul,Nat.one_mul]
    omega

lemma widthLists_length (fs : List V) (w : ℕ) :
    (widthLists fs w).length = (fs.length+1)^w := by
  induction w with
  | zero => simp [widthLists]
  | succ w ih =>
    simp only [widthLists,List.length_append,List.length_flatMap,List.length_map,ih]
    rw [sum_map_constant]
    simp only [pow_succ]
    ring

lemma mem_widthLists (fs : List V) (w : ℕ) (R : Finset V) :
    R ∈ widthLists fs w ↔ R ⊆ fs.toFinset ∧ R.card ≤ w := by
  induction w generalizing R with
  | zero =>
    constructor
    · intro h
      have he : R = ∅ := by simpa only [widthLists,List.mem_singleton] using h
      subst R
      simp
    · rintro ⟨_,hc⟩
      have he : R = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hc)
      simp only [widthLists,List.mem_singleton,he]
  | succ w ih =>
    simp only [widthLists,List.mem_append,List.mem_flatMap,List.mem_map]
    constructor
    · rintro (h | ⟨i,hi,T,hT,rfl⟩)
      · exact ⟨(ih R).mp h |>.1, Nat.le_succ_of_le ((ih R).mp h |>.2)⟩
      · rcases (ih T).mp hT with ⟨hTF,hTw⟩
        exact ⟨Finset.insert_subset (List.mem_toFinset.mpr hi) hTF,
          (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hTw 1)⟩
    · rintro ⟨hRF,hRw⟩
      by_cases hc : R.card ≤ w
      · exact Or.inl ((ih R).mpr ⟨hRF,hc⟩)
      · have hR : R.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨i,hi⟩ := hR
        refine Or.inr ⟨i,List.mem_toFinset.mp (hRF hi),R.erase i,?_,Finset.insert_erase hi⟩
        apply (ih (R.erase i)).mpr
        exact ⟨Finset.erase_subset _ _ |>.trans hRF,by rw [Finset.card_erase_of_mem hi]; omega⟩

def listBest (rank : V → ℕ) (seed : V) : List V → V
  | [] => seed
  | a::as => listBest rank (if rank a < rank seed then a else seed) as

omit [DecidableEq V] in
lemma listBest_mem (rank : V → ℕ) (seed : V) (xs : List V) :
    listBest rank seed xs = seed ∨ listBest rank seed xs ∈ xs := by
  induction xs generalizing seed with
  | nil => exact Or.inl rfl
  | cons a xs ih =>
    unfold listBest
    rcases ih (if rank a < rank seed then a else seed) with h | h
    · rw [h]
      split_ifs
      · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem _ h)

omit [DecidableEq V] in
lemma listBest_le (rank : V → ℕ) (seed : V) (xs : List V) :
    rank (listBest rank seed xs) ≤ rank seed ∧ ∀ a ∈ xs, rank (listBest rank seed xs) ≤ rank a := by
  induction xs generalizing seed with
  | nil => simp [listBest]
  | cons a xs ih =>
    have hh := ih (if rank a < rank seed then a else seed)
    have hs : rank (if rank a < rank seed then a else seed) ≤ rank seed := by
      split_ifs with h
      · exact h.le
      · exact le_rfl
    have ha : rank (if rank a < rank seed then a else seed) ≤ rank a := by
      split_ifs with h
      · exact le_rfl
      · exact le_of_not_gt h
    refine ⟨hh.1.trans hs,?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hh.1.trans ha
    · exact hh.2 b hb

omit [DecidableEq V] in
lemma listBest_fixed (rank : V → ℕ) (seed : V) (xs : List V)
    (h : ∀ a ∈ xs, rank seed ≤ rank a) : listBest rank seed xs = seed := by
  induction xs generalizing seed with
  | nil => rfl
  | cons a xs ih =>
    have ha : ¬rank a < rank seed := not_lt.mpr (h a (List.mem_cons_self ..))
    simp only [listBest,ite_eq_right ha]
    exact ih seed (fun b hb => h b (List.mem_cons_of_mem _ hb))

def exchangeList (fs : List V) (S : Finset V) (w : ℕ) : List (Finset V) :=
  ((widthLists fs w).flatMap (fun R => (widthLists fs w).map (fun A => (S \ R) ∪ A))).filter
    (fun T => T.card = S.card)

lemma exchangeList_length (fs : List V) (S : Finset V) (w : ℕ) :
    (exchangeList fs S w).length ≤ ((fs.length+1)^w)^2 := by
  apply (List.length_filter_le ..).trans
  simp only [List.length_flatMap,List.length_map,widthLists_length,sum_map_constant,pow_two]
  rfl

lemma mem_exchangeList (fs : List V) (S T : Finset V) (w : ℕ) (hSF : S ⊆ fs.toFinset) :
    T ∈ exchangeList fs S w ↔ T ∈ exchangeCandidates fs.toFinset S w := by
  simp only [exchangeList,List.mem_filter,List.mem_flatMap,List.mem_map,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨R,hR,A,hA,rfl⟩,hcard⟩
    rcases (mem_widthLists fs w R).mp hR with ⟨_,hRw⟩
    rcases (mem_widthLists fs w A).mp hA with ⟨hAF,hAw⟩
    have hd := exchange_diff_bounds S R A
    exact candidate_of_exchange _ _ _ _
      (Finset.union_subset (Finset.sdiff_subset.trans hSF) hAF) hcard
      ((Finset.card_le_card hd.1).trans hRw) ((Finset.card_le_card hd.2).trans hAw)
  · intro h
    have hp := candidate_properties _ _ _ _ hSF h
    refine ⟨⟨S \ T,(mem_widthLists fs w _).mpr ⟨Finset.sdiff_subset.trans hSF,hp.2.2.1⟩,
      T \ S,(mem_widthLists fs w _).mpr ⟨Finset.sdiff_subset.trans hp.1,hp.2.2.2⟩,?_⟩,hp.2.1⟩
    ext i
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto

def executableStep (fs : List V) (rank : Finset V → ℕ) (w : ℕ) (S : Finset V) : Finset V :=
  listBest rank S (exchangeList fs S w)

lemma executableStep_mem (fs : List V) (rank : Finset V → ℕ) (w : ℕ) (S : Finset V)
    (hSF : S ⊆ fs.toFinset) : executableStep fs rank w S ∈ exchangeCandidates fs.toFinset S w := by
  rcases listBest_mem rank S (exchangeList fs S w) with h | h
  · change listBest rank S (exchangeList fs S w) ∈ _
    rw [h]
    exact candidate_mem_self fs.toFinset S w
  · exact (mem_exchangeList fs S _ w hSF).mp h

lemma executableStep_min (fs : List V) (rank : Finset V → ℕ) (w : ℕ) (S T : Finset V)
    (hSF : S ⊆ fs.toFinset) (hT : T ∈ exchangeCandidates fs.toFinset S w) :
    rank (executableStep fs rank w S) ≤ rank T :=
  (listBest_le rank S (exchangeList fs S w)).2 T ((mem_exchangeList fs S T w hSF).mpr hT)

lemma executableStep_mono (fs : List V) (rank : Finset V → ℕ) (w : ℕ) (S : Finset V) :
    rank (executableStep fs rank w S) ≤ rank S := (listBest_le ..).1

lemma executableStep_fixed (fs : List V) (rank : Finset V → ℕ) (w : ℕ) (S : Finset V)
    (hSF : S ⊆ fs.toFinset)
    (h : ∀ T ∈ exchangeCandidates fs.toFinset S w, rank S ≤ rank T) :
    executableStep fs rank w S = S := by
  apply listBest_fixed
  intro T hT
  exact h T ((mem_exchangeList fs S T w hSF).mp hT)

def executableDescent (fs : List V) (rank : Finset V → ℕ) (w : ℕ) : ℕ → Finset V → Finset V
  | 0, S => S
  | n+1, S => executableDescent fs rank w n (executableStep fs rank w S)

lemma executableDescent_properties (fs : List V) (rank : Finset V → ℕ) (w n : ℕ)
    (S : Finset V) (hSF : S ⊆ fs.toFinset) :
    executableDescent fs rank w n S ⊆ fs.toFinset ∧
      (executableDescent fs rank w n S).card = S.card ∧
      rank (executableDescent fs rank w n S) ≤ rank S := by
  induction n generalizing S with
  | zero => exact ⟨hSF,rfl,le_rfl⟩
  | succ n ih =>
    have hp := candidate_properties _ _ _ _ hSF (executableStep_mem fs rank w S hSF)
    have hh := ih (executableStep fs rank w S) hp.1
    exact ⟨hh.1,hh.2.1.trans hp.2.1,hh.2.2.trans (executableStep_mono ..)⟩

lemma executableDescent_fixed (fs : List V) (rank : Finset V → ℕ) (w n : ℕ) (S : Finset V)
    (h : executableStep fs rank w S = S) : executableDescent fs rank w n S = S := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [executableDescent,h] using ih

theorem executableDescent_min (fs : List V) (rank : Finset V → ℕ) (w n : ℕ)
    (S : Finset V) (hSF : S ⊆ fs.toFinset) (hn : rank S ≤ n) :
    ∀ T ∈ exchangeCandidates fs.toFinset (executableDescent fs rank w n S) w,
      rank (executableDescent fs rank w n S) ≤ rank T := by
  induction n generalizing S with
  | zero =>
    intro T _
    change rank S ≤ rank T
    omega
  | succ n ih =>
    by_cases hlocal : ∀ T ∈ exchangeCandidates fs.toFinset S w, rank S ≤ rank T
    · rw [executableDescent_fixed fs rank w (n+1) S (executableStep_fixed fs rank w S hSF hlocal)]
      exact hlocal
    · push Not at hlocal
      obtain ⟨T,hT,ht⟩ := hlocal
      have hs := (executableStep_min fs rank w S T hSF hT).trans_lt ht
      have hp := candidate_properties _ _ _ _ hSF (executableStep_mem fs rank w S hSF)
      exact ih _ hp.1 (by omega)

end MetricKMedianRecovery.LocalSearch

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]

theorem executable_integral_descent (δ : V → V → ℕ) (fs : List V) (D S : Finset V)
    (w M n : ℕ) (hSF : S ⊆ fs.toFinset) (hDn : D.card ≤ n)
    (hδ : ∀ p ∈ D, ∀ i ∈ fs.toFinset, (δ p i : ℝ) = dist p i)
    (hM : ∀ p ∈ D, ∀ i ∈ fs.toFinset, δ p i ≤ M) :
    let T := executableDescent fs (natCost δ D) w (n*M) S
    T ⊆ fs.toFinset ∧ T.card = S.card ∧ cost D T ≤ cost D S ∧ WidthLocalMin fs.toFinset D T w := by
  dsimp only
  have hp := executableDescent_properties fs (natCost δ D) w (n*M) S hSF
  have hr : natCost δ D S ≤ n*M :=
    (natCost_le δ fs.toFinset D S hSF M hM).trans (Nat.mul_le_mul_right M hDn)
  have hm := executableDescent_min fs (natCost δ D) w (n*M) S hSF hr
  refine ⟨hp.1,hp.2.1,?_,?_⟩
  · rw [←natCost_cast δ fs.toFinset D _ hp.1 hδ,←natCost_cast δ fs.toFinset D S hSF hδ]
    exact_mod_cast hp.2.2
  · intro U hUF hcard hrem hadd
    rw [←natCost_cast δ fs.toFinset D _ hp.1 hδ,←natCost_cast δ fs.toFinset D U hUF hδ]
    exact_mod_cast hm U (candidate_of_exchange _ _ _ _ hUF hcard hrem hadd)

def executableAnchor (δ : V → V → ℕ) (fs ds : List V) (r M : ℕ) : Finset V :=
  executableDescent fs (natCost δ ds.toFinset) 5 (ds.length*M) (fs.take r).toFinset

omit [MetricSpace V] in
lemma seed_card (fs : List V) (r : ℕ) (hfs : fs.Nodup) (hr : r ≤ fs.length) :
    (fs.take r).toFinset.card = r := by
  rw [List.toFinset_card_of_nodup (hfs.take),List.length_take,Nat.min_eq_left hr]

omit [MetricSpace V] in
lemma seed_subset (fs : List V) (r : ℕ) : (fs.take r).toFinset ⊆ fs.toFinset := by
  intro i hi
  exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hi))

theorem executableAnchor_spec (δ : V → V → ℕ) (fs ds : List V) (r M : ℕ)
    (hfs : fs.Nodup) (hr : 0 < r) (hrF : r ≤ fs.length)
    (hδ : ∀ p ∈ ds.toFinset, ∀ i ∈ fs.toFinset, (δ p i : ℝ) = dist p i)
    (hM : ∀ p ∈ ds.toFinset, ∀ i ∈ fs.toFinset, δ p i ≤ M) :
    let S := executableAnchor δ fs ds r M
    S ⊆ fs.toFinset ∧ S.Nonempty ∧ S.card = r ∧ WidthLocalMin fs.toFinset ds.toFinset S 5 ∧
      ∀ O : Finset V, O.Nonempty → O ⊆ fs.toFinset → O.card ≤ r → cost ds.toFinset S ≤ 5*cost ds.toFinset O := by
  have hh := executable_integral_descent δ fs ds.toFinset (fs.take r).toFinset 5 M ds.length
    (seed_subset fs r) (List.toFinset_card_le ds) hδ hM
  change executableAnchor δ fs ds r M ⊆ _ ∧ _ at hh
  have hcard : (executableAnchor δ fs ds r M).card = r := hh.2.1.trans (seed_card fs r hfs hrF)
  have hpos : (executableAnchor δ fs ds r M).Nonempty := Finset.card_pos.mp (by rw [hcard]; exact hr)
  dsimp only
  refine ⟨hh.1,hpos,hcard,hh.2.2.2,?_⟩
  intro O hO hOF hOr
  exact local_five_approx _ _ _ O hpos hO hh.1 hh.2.2.2 hOF (by rw [hcard]; exact hOr)

end MetricKMedianRecovery.LocalSearch

end OAI
