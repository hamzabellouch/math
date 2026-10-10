import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.StateBits2
import OAI.Combinatorics.KMedianRecovery.Geometry.LocalCandidates

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalBest
open WordOperations WordList BinaryArithmetic
noncomputable def choose (rank : List Bool→List Bool) (x : List Bool) : List Bool :=
  if value (rank (pairBits (Find.context x,Find.item x))) < value (rank (pairBits (Find.context x,Fold.accum x)))
  then Find.item x else Fold.accum x
noncomputable def choose_computes {rank : List Bool→List Bool} (hr : PolyComputes rank) : PolyComputes (choose rank) := by
  have h := (NatOps.lt ((Find.context_computes.pair Find.item_computes).comp hr)
    ((Find.context_computes.pair Fold.accum_computes).comp hr)).cond Find.item_computes Fold.accum_computes
  unfold choose
  simpa only [decide_eq_true_eq,Function.comp_def] using h
lemma choose_pack {A : Type*} (enc : A→List Bool) (rank : List Bool→List Bool) (ctx : List Bool)
    (r : A→ℕ) (hr : ∀ a,rank (pairBits (ctx,enc a))=(r a).bits) (a s : A) :
    choose rank (pairBits (ctx,pairBits (enc a,enc s)))=enc (if r a<r s then a else s) := by
  simp only [choose,Find.context,Find.item,Fold.accum,Function.comp_apply,extractPrefix_pairBits,
    discardPrefix_pairBits,hr,value_bits]
  split_ifs <;> rfl
lemma listBest_fold {A : Type*} (r : A→ℕ) (s : A) (xs : List A) :
    xs.foldl (fun s a=>if r a<r s then a else s) s=LocalSearch.listBest r s xs := by
  induction xs generalizing s with
  | nil=>rfl
  | cons a xs ih=>exact ih _
def pack (ctx seed : List Bool) (ws : List (List Bool)) : List Bool := pairBits (ctx,pairBits (seed,encode ws))
noncomputable def run (rank : List Bool→List Bool) (x : List Bool) : List Bool :=
  CappedFold.run (choose rank) (pairBits (x,Fold.pack (discardPrefix (discardPrefix x)) (extractPrefix x)
    (extractPrefix (discardPrefix x))))
noncomputable def run_computes {rank : List Bool→List Bool} (hr : PolyComputes rank) : PolyComputes (run rank) :=
  (id_computes.pair (Fold.pack_computes (discardPrefix_computes.comp discardPrefix_computes) extractPrefix_computes
    (discardPrefix_computes.comp extractPrefix_computes))).comp (CappedFold.run_computes (choose_computes hr))
lemma run_pack {A : Type*} [DecidableEq A] (enc : A→List Bool) (rank : List Bool→List Bool) (ctx : List Bool)
    (r : A→ℕ) (hr : ∀ a,rank (pairBits (ctx,enc a))=(r a).bits) (s : A) (xs : List A) :
    run rank (pack ctx (enc s) (xs.map enc))=enc (LocalSearch.listBest r s xs) := by
  unfold run
  simp only [pack,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [CappedFold.run_typed enc enc (fun s a=>if r a<r s then a else s) (choose rank) ctx
    (pairBits (ctx,pairBits (enc s,encode (xs.map enc)))) (fun s a=>choose_pack enc rank ctx r hr a s) s xs]
  · rw [listBest_fold]
  · intro n
    rw [listBest_fold]
    rcases LocalSearch.listBest_mem r s (xs.take n) with he|he
    · rw [he]
      simp only [pairBits_length]
      omega
    · have hh := WordList.length_member_le_encode (ws:=xs.map enc) (w:=enc (LocalSearch.listBest r s (xs.take n))) (List.mem_map.mpr ⟨_,List.mem_of_mem_take he,rfl⟩)
      change (enc (LocalSearch.listBest r s (xs.take n))).length≤(encode (xs.map enc)).length at hh
      simp only [pairBits_length]
      omega
end MetricKMedianRecovery.BitMachine.BinaryLocalBest

namespace MetricKMedianRecovery.BitMachine.BinaryLocalSearch
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
def pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Label (Fin m))) (S : Finset (Label (Fin m))) : List Bool :=
  encode [Rectangular.encode distance,List.replicate d true,labels fs,setBits S]
noncomputable def rank (x : List Bool) : List Bool := BinaryLocalCost.rank
  (encode [field 0 (extractPrefix x),field 1 (extractPrefix x),discardPrefix x])
noncomputable def rank_computes : PolyComputes rank :=
  (list_computes [field 0 ∘ extractPrefix,field 1 ∘ extractPrefix,discardPrefix] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨extractPrefix_computes.comp (field_computes 0)⟩
    · exact ⟨extractPrefix_computes.comp (field_computes 1)⟩
    · exact ⟨discardPrefix_computes⟩)).comp BinaryLocalCost.rank_computes
lemma rank_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Label (Fin m))) (S T : Finset (Label (Fin m))) :
    rank (pairBits (pack distance fs S,setBits T))=(⌈BinaryLocalCost.cost distance T⌉₊).bits := by
  simp only [rank,extractPrefix_pairBits,discardPrefix_pairBits,pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  exact BinaryLocalCost.rank_pack distance T
noncomputable def selected (w : ℕ) (x : List Bool) : List Bool :=
  BinaryLocalBest.run rank (pairBits (x,pairBits (field 3 x,
    BinaryLocalCandidates.run w (pairBits (field 2 x,field 3 x)))))
noncomputable def selected_computes (w : ℕ) : PolyComputes (selected w) :=
  (id_computes.pair ((field_computes 3).pair (((field_computes 2).pair (field_computes 3)).comp
    (BinaryLocalCandidates.run_computes w)))).comp (BinaryLocalBest.run_computes rank_computes)
lemma selected_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Label (Fin m))) (S : Finset (Label (Fin m))) (w : ℕ) :
    selected w (pack distance fs S)=setBits (LocalSearch.executableStep fs (fun T=>⌈BinaryLocalCost.cost distance T⌉₊) w S) := by
  have h2 : field 2 (pack distance fs S)=labels fs := by
    simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  have h3 : field 3 (pack distance fs S)=setBits S := by
    simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [selected,h2,h3,BinaryLocalCandidates.run_pack]
  exact BinaryLocalBest.run_pack setBits rank (pack distance fs S) (fun T=>⌈BinaryLocalCost.cost distance T⌉₊)
    (rank_pack distance fs S) S (LocalSearch.exchangeList fs S w)
noncomputable def step (w : ℕ) (x : List Bool) : List Bool := encode [field 0 x,field 1 x,field 2 x,selected w x]
noncomputable def step_computes (w : ℕ) : PolyComputes (step w) := list_computes
  [field 0,field 1,field 2,selected w] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl
    all_goals first | exact ⟨field_computes _⟩ | exact ⟨selected_computes w⟩)
lemma step_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Label (Fin m))) (S : Finset (Label (Fin m))) (w : ℕ) :
    step w (pack distance fs S)=pack distance fs
      (LocalSearch.executableStep fs (fun T=>⌈BinaryLocalCost.cost distance T⌉₊) w S) := by
  rw [step,selected_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma iterate_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Label (Fin m))) (S : Finset (Label (Fin m))) (w n : ℕ) :
    (step w)^[n] (pack distance fs S)=pack distance fs
      (LocalSearch.executableDescent fs (fun T=>⌈BinaryLocalCost.cost distance T⌉₊) w n S) := by
  induction n generalizing S with
  | zero=>rfl
  | succ n ih=>rw [Function.iterate_succ_apply,step_pack,ih]; rfl
end MetricKMedianRecovery.BitMachine.BinaryLocalSearch

namespace MetricKMedianRecovery.BitMachine.BinaryLocalSearch
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def capPoly : Polynomial ℕ := 10*(Polynomial.X+1)^2
noncomputable def capacity : PolynomialCounter capPoly := PolynomialCounter.choose capPoly
noncomputable def iterationInput (x : List Bool) : List Bool :=
  pairBits (extractPrefix x,pairBits (capacity.word x,discardPrefix x))
noncomputable def iterationInput_computes : PolyComputes iterationInput :=
  extractPrefix_computes.pair (capacity.computes.pair discardPrefix_computes)
noncomputable def run (w : ℕ) : List Bool→List Bool :=
  field 3 ∘ BoundedIteration.run (step w) ∘ iterationInput
noncomputable def run_computes (w : ℕ) : PolyComputes (run w) :=
  iterationInput_computes.comp ((BoundedIteration.run_computes (step_computes w)).comp (field_computes 3))
lemma length_bound {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Label (Fin m)))
    (S T : Finset (Label (Fin m))) (n : ℕ) (hT : T⊆fs.toFinset) :
    (pack distance fs T).length ≤ capPoly.eval (pairBits (List.replicate n true,pack distance fs S)).length := by
  let L := (pairBits (List.replicate n true,pack distance fs S)).length
  have hparts : (Rectangular.encode distance).length ≤ L ∧ d ≤ L ∧ (labels fs).length ≤ L := by
    simp only [L,pack,pairBits_length,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      List.length_cons,List.length_nil,List.length_replicate]
    omega
  have hc : T.card ≤ L :=
    (Finset.card_le_card hT).trans ((List.toFinset_card_le fs).trans ((BinaryFiniteContext.length_labels_le fs).trans hparts.2.2))
  have hs : (setBits T).length ≤ L*(2*L+2) :=
    BinaryFiniteContext.setBits_length T hc (fun i hi=>
      (BinaryFiniteContext.member_labels_length (List.mem_toFinset.mp (hT hi))).trans hparts.2.2)
  change (pack distance fs T).length ≤ capPoly.eval L
  simp only [pack,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil,List.length_replicate,capPoly,
    Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  nlinarith [hparts.1,hparts.2.1,hparts.2.2]
lemma run_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Label (Fin m)))
    (S : Finset (Label (Fin m))) (w n : ℕ) (hS : S⊆fs.toFinset) :
    run w (pairBits (List.replicate n true,pack distance fs S))=setBits
      (LocalSearch.executableDescent fs (fun T=>⌈BinaryLocalCost.cost distance T⌉₊) w n S) := by
  let x := pairBits (List.replicate n true,pack distance fs S)
  have hbound : ∀ j,((step w)^[j] (pack distance fs S)).length ≤ capPoly.eval x.length := by
    intro j
    rw [iterate_pack]
    exact length_bound distance fs S _ n
      (LocalSearch.executableDescent_properties fs (fun T=>⌈BinaryLocalCost.cost distance T⌉₊) w j S hS).1
  simp only [run,Function.comp_apply,iterationInput,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [BoundedIteration.run_eq]
  · rw [List.length_replicate,iterate_pack]
    simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  · intro j _
    rw [capacity.word_length]
    exact hbound j
end MetricKMedianRecovery.BitMachine.BinaryLocalSearch

end OAI
