import Mathlib
import OAI.Algebra.GroupRing.ClusterLocalization

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.BalancedPieces
open scoped Classical BigOperators

def count (h cap : ℕ) : ℕ := (h+cap-1)/cap
def length (h m : ℕ) (i : Fin m) : ℕ := h/m + if i.val<h%m then 1 else 0
lemma sum_length (h m : ℕ) (hm : 0 < m) : (∑ i,length h m i)=h := by
  unfold length
  rw [Finset.sum_add_distrib]
  have hi : (∑ i : Fin m,if i.val<h%m then 1 else 0)=h%m := by
    rw [←Finset.sum_filter]
    have he : (Finset.univ.filter (fun i : Fin m => i.val<h%m))=Finset.Iio ⟨h%m,Nat.mod_lt _ hm⟩ := by
      ext i
      simp [Fin.lt_def]
    rw [he,Finset.sum_const,Fin.card_Iio,smul_eq_mul,mul_one]
  rw [hi,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  exact Nat.div_add_mod h m
lemma length_pos (h m : ℕ) (hm : m≤h) (hm0 : 0 < m) (i : Fin m) : 0<length h m i := by
  have hh : 0<h/m := (Nat.div_pos_iff).mpr ⟨hm0,hm⟩
  unfold length
  omega
lemma count_bounds {h cap : ℕ} (hc : 0<cap) (hh : cap<h) :
    2≤count h cap ∧ h≤count h cap*cap ∧ (count h cap-1)*cap<h := by
  have h1 := Nat.div_mul_le_self (h+cap-1) cap
  have h2 := Nat.lt_div_mul_add (a:=h+cap-1) hc
  dsimp only [count]
  have h3 : 2≤(h+cap-1)/cap := by
    apply (Nat.le_div_iff_mul_le hc).mpr
    omega
  constructor
  · exact h3
  constructor
  · omega
  · rw [Nat.mul_sub_right_distrib]
    omega
lemma count_le {h cap : ℕ} (hc : 1≤cap) (hh : cap<h) : count h cap≤h := by
  have hb := count_bounds (by omega : 0<cap) hh
  have hm := Nat.mul_le_mul_left (count h cap-1) hc
  omega
lemma quotient_bounds {h cap : ℕ} (hc : 6≤cap) (hh : cap<h) :
    cap≤3*(h/count h cap) ∧ (h/count h cap)+(if h%count h cap=0 then 0 else 1)≤cap := by
  obtain ⟨hm,hup,hlo⟩ := count_bounds (by omega : 0<cap) hh
  have hdiv := Nat.div_add_mod h (count h cap)
  have hrem := Nat.mod_lt h (by omega : 0<count h cap)
  have hprod : (count h cap-1)*cap=count h cap*cap-cap := by simp only [Nat.mul_sub_right_distrib,one_mul]
  have hmcap : cap≤count h cap*cap := by nlinarith
  have hlow' : count h cap*cap-cap<h := by rwa [hprod] at hlo
  constructor
  · by_contra hn
    have hq : 3*(h/count h cap)<cap := by omega
    have h2 : 2*(h/count h cap+1)≤cap := by omega
    have h2m := Nat.mul_le_mul_left (count h cap) h2
    have hmc := Nat.mul_le_mul_right cap hm
    have hlow'' : count h cap*cap<h+cap := by omega
    nlinarith only [h2m,hmc,hlow'',hdiv,hrem]
  · split_ifs with hr
    · have hq := Nat.div_le_of_le_mul hup
      simpa using hq
    · have hrp : 0<h%count h cap := by omega
      by_contra hn
      have hq : cap≤h/count h cap := by omega
      nlinarith
lemma length_bounds {h cap : ℕ} (hc : 6≤cap) (hh : cap<h) (i : Fin (count h cap)) :
    cap≤3*length h (count h cap) i ∧ length h (count h cap) i≤cap := by
  obtain ⟨hl,hu⟩ := quotient_bounds hc hh
  unfold length
  constructor
  · split_ifs <;> omega
  · by_cases hr : h%count h cap=0
    · rw [ite_eq_left hr] at hu
      simp only [hr,Nat.not_lt_zero,ite_false,add_zero]
      exact hu
    · rw [ite_eq_right hr] at hu
      split_ifs <;> omega
lemma count_charge {h cap : ℕ} (hc : 6≤cap) (hh : cap<h) : count h cap*cap≤3*h := by
  have hs := sum_length h (count h cap) (by have hb := count_bounds (by omega : 0<cap) hh; omega)
  have hi : (∑ i : Fin (count h cap),cap)≤∑ i : Fin (count h cap),3*length h (count h cap) i :=
    Finset.sum_le_sum fun i _ => (length_bounds hc hh i).1
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,←Finset.mul_sum,hs] using hi

def number (h cap : ℕ) : ℕ := if h≤cap then 1 else count h cap
def sizes (h cap : ℕ) (i : Fin (number h cap)) : ℕ :=
  if h≤cap then h else length h (number h cap) i
lemma number_pos {h cap : ℕ} (hc : 0<cap) : 0<number h cap := by
  by_cases hh : h≤cap
  · simp only [number,ite_eq_left hh]; omega
  · have hb := (count_bounds hc (show cap<h by omega)).1
    simp only [number,ite_eq_right hh]
    omega
lemma sizes_sum {h cap : ℕ} (hc : 0<cap) : (∑ i,sizes h cap i)=h := by
  by_cases hh : h≤cap
  · have hn : number h cap=1 := ite_eq_left hh
    simp only [sizes,ite_eq_left hh,Finset.sum_const,Finset.card_univ,Fintype.card_fin,hn,one_smul]
  · simp only [sizes,ite_eq_right hh]
    exact sum_length h (number h cap) (number_pos hc)
lemma sizes_pos {h cap : ℕ} (hc : 0<cap) (hh : 0<h) (i : Fin (number h cap)) : 0<sizes h cap i := by
  by_cases hle : h≤cap
  · simpa only [sizes,ite_eq_left hle] using hh
  · simp only [sizes,ite_eq_right hle]
    apply length_pos _ _ _ (number_pos hc)
    simp only [number,ite_eq_right hle]
    exact count_le hc (by omega)
lemma sizes_upper {h cap : ℕ} (hc : 6≤cap) (i : Fin (number h cap)) : sizes h cap i≤cap := by
  by_cases hh : h≤cap
  · simpa only [sizes,ite_eq_left hh] using hh
  · simp only [sizes,ite_eq_right hh]
    have he : number h cap=count h cap := ite_eq_right hh
    have hb := (length_bounds hc (show cap<h by omega) (Fin.cast he i)).2
    convert hb using 1
    unfold length
    simp only [Fin.val_cast,he]
lemma sizes_lower_long {h cap : ℕ} (hc : 6≤cap) (hh : cap<h) (i : Fin (number h cap)) :
    cap≤3*sizes h cap i := by
  have hn : ¬h≤cap := by omega
  simp only [sizes,ite_eq_right hn]
  have hi : number h cap=count h cap := ite_eq_right hn
  have hb := (length_bounds hc hh (Fin.cast hi i)).1
  convert hb using 1
  unfold length
  simp only [Fin.val_cast,hi]
lemma number_charge {h cap : ℕ} (hc : 6≤cap) :
    (if cap<h then number h cap else 0)*cap≤3*h := by
  by_cases hh : cap<h
  · simp only [ite_eq_left hh,number,ite_eq_right (show ¬h≤cap by omega)]
    exact count_charge hc hh
  · simp only [ite_eq_right hh,Nat.zero_mul,Nat.zero_le]
lemma sizes_lower {h L U : ℕ} (hU : 3≤U) (hcap : 6≤U*L) (hh : L≤h)
    (i : Fin (number h (U*L))) : L ≤ sizes h (U*L) i := by
  by_cases hle : h≤U*L
  · simpa only [sizes,ite_eq_left hle] using hh
  · have hb := sizes_lower_long hcap (by omega : U*L<h) i
    nlinarith
end TorsionFreeZeroDivisors.BalancedPieces
namespace TorsionFreeZeroDivisors.ConsecutivePieces
open scoped Classical BigOperators
variable {A : Type*} {m : ℕ} (l : List A) (n : Fin m → ℕ) (hs : (∑ i,n i)=l.length)

def index : ((i : Fin m) × Fin (n i)) ≃ Fin l.length := finSigmaFinEquiv.trans (finCongr hs)
def offset (i : Fin m) : ℕ := ∑ j : Fin i.val,n (Fin.castLE i.isLt.le j)
lemma index_val (i : Fin m) (j : Fin (n i)) : (index l n hs ⟨i,j⟩).val=offset n i+j.val := by
  simp only [index,Equiv.trans_apply,finCongr_apply,Fin.val_cast,finSigmaFinEquiv_apply,offset]
def segment (i : Fin m) : List A := List.ofFn fun j : Fin (n i) => l[index l n hs ⟨i,j⟩]
lemma length_segment (i : Fin m) : (segment l n hs i).length=n i := List.length_ofFn
lemma segment_get (i : Fin m) (j : Fin (n i)) :
    (segment l n hs i)[j.val]'(by rw [length_segment]; exact j.isLt)=l[index l n hs ⟨i,j⟩] := by
  simp only [segment,List.getElem_ofFn]
lemma segment_nonempty (i : Fin m) (h : 0<n i) : segment l n hs i≠[] := by
  intro he
  have ht := length_segment l n hs i
  rw [he,List.length_nil] at ht
  omega
lemma successor_index (i : Fin m) (j : ℕ) (hj : j+1<n i) :
    (index l n hs ⟨i,⟨j+1,hj⟩⟩).val=(index l n hs ⟨i,⟨j,by omega⟩⟩).val+1 := by
  rw [index_val,index_val]
  change offset n i+(j+1)=offset n i+j+1
  omega
lemma segment_chain {R : A → A → Prop} (hp : l.IsChain R) (i : Fin m) :
    (segment l n hs i).IsChain R := by
  rw [List.isChain_iff_getElem]
  intro j hj
  have hj' : j+1<n i := by simpa only [length_segment] using hj
  have he := successor_index l n hs i j hj'
  have hb := (index l n hs ⟨i,⟨j+1,hj'⟩⟩).isLt
  have hp' := (List.isChain_iff_getElem.mp hp) (index l n hs ⟨i,⟨j,by omega⟩⟩).val (by omega)
  simp only [segment,List.getElem_ofFn]
  change R l[(index l n hs ⟨i,⟨j,by omega⟩⟩).val] l[(index l n hs ⟨i,⟨j+1,hj'⟩⟩).val]
  simpa only [←he] using hp'
lemma total_length : (∑ i,(segment l n hs i).length)=l.length := by simp only [length_segment,hs]

/-- Every original occurrence is retained exactly once, at its actual index. -/
lemma occurrence_unique (j : Fin l.length) :
    ∃! p : (i : Fin m) × Fin (n i),index l n hs p=j := (index l n hs).bijective.existsUnique j
end TorsionFreeZeroDivisors.ConsecutivePieces
namespace TorsionFreeZeroDivisors.BalancedWords
open scoped Classical BigOperators
variable {T A : Type} (w : T → List A) (cap : ℕ) (hc : 0<cap)
abbrev Piece := (t : T) × Fin (BalancedPieces.number (w t).length cap)
def old (p : Piece w cap) : ℕ := BalancedPieces.sizes (w p.1).length cap p.2
def segment (p : Piece w cap) : List A :=
  ConsecutivePieces.segment (w p.1) (BalancedPieces.sizes (w p.1).length cap)
    (BalancedPieces.sizes_sum (h:=(w p.1).length) hc) p.2
lemma segment_length (p : Piece w cap) : (segment w cap hc p).length=old w cap p :=
  ConsecutivePieces.length_segment _ _ _ _
include hc in
lemma old_pos (hpos : ∀ t,(w t)≠[]) (p : Piece w cap) : 0<old w cap p :=
  BalancedPieces.sizes_pos hc (List.length_pos_iff.mpr (hpos p.1)) p.2
lemma segment_nonempty (hpos : ∀ t,(w t)≠[]) (p : Piece w cap) : segment w cap hc p≠[] := by
  apply List.length_pos_iff.mp
  rw [segment_length]
  exact old_pos w cap hc hpos p
lemma segment_chain {R : A → A → Prop} (h : ∀ t,(w t).IsChain R) (p : Piece w cap) :
    (segment w cap hc p).IsChain R := ConsecutivePieces.segment_chain _ _ _ (h p.1) p.2
lemma old_le (hcap : 6≤cap) (p : Piece w cap) : old w cap p≤cap :=
  BalancedPieces.sizes_upper hcap p.2
lemma intact (p : Piece w cap) (hp : (w p.1).length≤cap) : segment w cap hc p=w p.1 := by
  have hi : p.2.val=0 := by
    have hh := p.2.isLt
    have hh' : p.2.val<1 := by simpa only [BalancedPieces.number,ite_eq_left hp] using hh
    omega
  apply List.ext_getElem
  · rw [segment_length]
    simp only [old,BalancedPieces.sizes,ite_eq_left hp]
  · intro j hj hk
    have hj' : j<BalancedPieces.sizes (w p.1).length cap p.2 := by simpa only [segment_length,old] using hj
    simp only [segment,ConsecutivePieces.segment,List.getElem_ofFn,Fin.getElem_fin]
    congr 1
    rw [ConsecutivePieces.index_val]
    have hz : ConsecutivePieces.offset (BalancedPieces.sizes (w p.1).length cap) p.2=0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hilt := i.isLt
      omega
    rw [hz,zero_add]

variable [Fintype T]
include hc in
lemma old_sum : (∑p : Piece w cap,old w cap p)=∑t,(w t).length := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro t _
  exact BalancedPieces.sizes_sum (h:=(w t).length) hc

/-- Quantitative closing, before identifying the added positions as fixed.
Only genuinely split words get closure terms. -/
lemma closure_charge (tail : Piece w cap → List A) (tailCap : ℕ) (hcap : 6≤cap)
    (hshort : ∀ p,(w p.1).length≤cap → tail p=[])
    (htail : ∀ p,(tail p).length≤tailCap) :
    cap*(∑p,(tail p).length)≤3*tailCap*(∑t,(w t).length) := by
  rw [Fintype.sum_sigma,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  by_cases hs : (w t).length≤cap
  · have he : ∀ i : Fin (BalancedPieces.number (w t).length cap),tail ⟨t,i⟩=[] := fun i=>hshort ⟨t,i⟩ hs
    simp only [he,List.length_nil,Finset.sum_const_zero,Nat.mul_zero,Nat.zero_le]
  · have hsum : (∑i : Fin (BalancedPieces.number (w t).length cap),(tail ⟨t,i⟩).length)≤
        BalancedPieces.number (w t).length cap*tailCap := by
      calc
        _ ≤ ∑_i : Fin (BalancedPieces.number (w t).length cap),tailCap := Finset.sum_le_sum fun i _=>htail ⟨t,i⟩
        _ = _ := by simp
    have hcount := BalancedPieces.number_charge (h:= (w t).length) hcap
    rw [ite_eq_left (show cap<(w t).length by omega)] at hcount
    have ha := Nat.mul_le_mul_left cap hsum
    have hb := Nat.mul_le_mul_right tailCap hcount
    nlinarith
end TorsionFreeZeroDivisors.BalancedWords
namespace TorsionFreeZeroDivisors.ShortClosure
open PortSubdivision WeightedMoore.PortWalk
variable {V D : Type} (Γ : PortGraph V D)
lemma endpoint_cons' (a : V) (d : D) (p : List D) :
    endpoint Γ a (d::p)=endpoint Γ (Γ.origin (Γ.reverse d)) p := by
  cases p with
  | nil => rfl
  | cons e p => simp only [endpoint,List.getLast?_cons,Option.map_some,Option.getD_some]

lemma ReducedPath.exists_walk {a b : V} {p : List D} (hp : ReducedPath Γ a b p) :
    ∃ q : Γ.Walk a b,q.darts=p := by
  induction p generalizing a with
  | nil =>
    have he : a=b := hp.finish
    subst b
    exact ⟨.nil a,rfl⟩
  | cons d p ih =>
    have hc := List.isChain_cons.mp hp.chain
    have ht : ReducedPath Γ (Γ.origin (Γ.reverse d)) b p := {
      chain := hc.2
      start := fun e he=>(hc.1 e he).1.symm
      finish := by rw [←endpoint_cons' Γ a d p]; exact hp.finish }
    obtain ⟨q,hq⟩ := ih ht
    exact ⟨.cons d (hp.start d (by simp)) q,by simp only [PortGraph.Walk.darts,hq]⟩

lemma ReducedPath.length_ge {a : V} {p : List D} (hp : ReducedPath Γ a a p)
    (hn : p≠[]) (L : ℕ) (hg : (3*L:ℕ)≤Γ.subdivision.egirth) : L≤p.length := by
  obtain ⟨q,hq⟩ := hp.exists_walk Γ
  have hr : q.IsReduced := by
    rw [PortGraph.Walk.IsReduced,hq]
    exact hp.chain.imp (fun _ _ h=>h.2)
  have hn' : 0<q.length := by rw [←q.length_darts,hq]; exact List.length_pos_iff.mpr hn
  have hh := TypedGraphs.reduced_circuit_length Γ L hg q hr hn'
  simpa only [←q.length_darts,hq] using hh

lemma of_cyclic {p : List D} (hn : p≠[])
    (hch : p.IsChain (step Γ.origin Γ.reverse))
    (hc : ∀ᵉ (x∈p.getLast?) (y∈p.head?),step Γ.origin Γ.reverse x y) :
    ReducedPath Γ (Γ.origin (p.head hn)) (Γ.origin (p.head hn)) p where
  chain := hch
  start := by
    intro d hd
    rw [List.head?_eq_some_head hn] at hd
    exact congrArg Γ.origin (Option.some.inj hd.symm)
  finish := by
    have h := (hc (p.getLast hn) (List.getLast_mem_getLast? hn) (p.head hn) (List.head_mem_head? hn)).1
    simpa only [endpoint,List.getLast?_eq_some_getLast hn,Option.map_some,Option.getD_some] using h
end TorsionFreeZeroDivisors.ShortClosure
namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (cap : ℕ) (hc : 0<cap)
    (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
abbrev Piece := BalancedWords.Piece s.paths cap
abbrev seg (p : Piece s cap) := BalancedWords.segment s.paths cap hc p
abbrev seg_ne (p : Piece s cap) : seg s cap hc p≠[] :=
  BalancedWords.segment_nonempty s.paths cap hc s.nonempty p
abbrev start (p : Piece s cap) := (graph rep r).origin ((seg s cap hc p).head (seg_ne s cap hc p))
lemma segment_path (p : Piece s cap) :
    ShortClosure.ReducedPath (graph rep r) (start s cap hc p)
      (ShortClosure.endpoint (graph rep r) (start s cap hc p) (seg s cap hc p)) (seg s cap hc p) where
  chain := BalancedWords.segment_chain s.paths cap hc s.path_chain p
  start := by
    intro d hd
    rw [List.head?_eq_some_head (seg_ne s cap hc p)] at hd
    exact congrArg (graph rep r).origin (Option.some.inj hd.symm)
  finish := rfl

abbrev D : ℕ := TypedDiameter.D₀+1608

def chosenTail (p : Piece s cap) : List (DA rep⊕DB rep) :=
  (SampleGraph.short_closure rep r hL hd (segment_path s cap hc p) (seg_ne s cap hc p)).choose
lemma chosenTail_spec (p : Piece s cap) :
    (chosenTail s cap hc hL hd p).length≤ D*L (size rep) ∧
      ShortClosure.ReducedPath (graph rep r) (start s cap hc p) (start s cap hc p)
        (seg s cap hc p++chosenTail s cap hc hL hd p) ∧
      ∀ᵉ (a∈(seg s cap hc p++chosenTail s cap hc hL hd p).getLast?)
          (b∈(seg s cap hc p++chosenTail s cap hc hL hd p).head?),
        PortWalk.step (graph rep r).origin (graph rep r).reverse a b :=
  (SampleGraph.short_closure rep r hL hd (segment_path s cap hc p) (seg_ne s cap hc p)).choose_spec

def tail (p : Piece s cap) : List (DA rep⊕DB rep) :=
  if (s.paths p.1).length≤cap then [] else chosenTail s cap hc hL hd p
def word (p : Piece s cap) : List (DA rep⊕DB rep) := seg s cap hc p++tail s cap hc hL hd p
lemma tail_short (p : Piece s cap) (hp : (s.paths p.1).length≤cap) : tail s cap hc hL hd p=[] := ite_eq_left hp
lemma tail_bound (p : Piece s cap) : (tail s cap hc hL hd p).length≤D*L (size rep) := by
  unfold tail
  split_ifs
  · simp only [List.length_nil,Nat.zero_le]
  · exact (chosenTail_spec s cap hc hL hd p).1
lemma word_short (p : Piece s cap) (hp : (s.paths p.1).length≤cap) : word s cap hc hL hd p=s.paths p.1 := by
  rw [word,tail_short s cap hc hL hd p hp,List.append_nil]
  exact BalancedWords.intact s.paths cap hc p hp
lemma nonempty (p : Piece s cap) : word s cap hc hL hd p≠[] := by
  intro h
  exact seg_ne s cap hc p (List.append_eq_nil_iff.mp h).1
lemma chain (p : Piece s cap) :
    (word s cap hc hL hd p).IsChain (PortWalk.step (graph rep r).origin (graph rep r).reverse) := by
  by_cases hp : (s.paths p.1).length≤cap
  · rw [word_short s cap hc hL hd p hp]
    exact s.path_chain p.1
  · simpa only [word,tail,ite_eq_right hp] using (chosenTail_spec s cap hc hL hd p).2.1.chain
lemma cyclic_of_long (p : Piece s cap) (hp : cap<(s.paths p.1).length) :
    ∀ᵉ (a∈(word s cap hc hL hd p).getLast?) (b∈(word s cap hc hL hd p).head?),
      PortWalk.step (graph rep r).origin (graph rep r).reverse a b := by
  simpa only [word,tail,ite_eq_right (show ¬(s.paths p.1).length≤cap by omega)] using
    (chosenTail_spec s cap hc hL hd p).2.2

lemma original_girth (hr : r∈samples rep) (t : s.P) (ht : s.root≠some t) : L (size rep)≤(s.paths t).length := by
  have hc' := s.cyclic_chain t (by simp only [StageRoot.cyclic,decide_eq_true_eq]; exact ht)
  exact (ShortClosure.of_cyclic (graph rep r) (s.nonempty t) (s.path_chain t) hc').length_ge
    (graph rep r) (s.nonempty t) (L (size rep)) (girth rep r hr)

lemma old_le_word (p : Piece s cap) : BalancedWords.old s.paths cap p≤(word s cap hc hL hd p).length := by
  simp only [word,List.length_append,BalancedWords.segment_length]
  omega
lemma word_bound (hcap : 6≤cap) (p : Piece s cap) : (word s cap hc hL hd p).length≤cap+D*L (size rep) := by
  have ho := BalancedWords.old_le s.paths cap hcap p
  have ht := tail_bound s cap hc hL hd p
  simp only [word,List.length_append,BalancedWords.segment_length]
  omega
lemma total_added (hcap : 6≤cap) : cap*(∑p : Piece s cap,(tail s cap hc hL hd p).length)≤
    3*(D*L (size rep))*(∑t,(s.paths t).length) :=
  BalancedWords.closure_charge s.paths cap (tail s cap hc hL hd) (D*L (size rep)) hcap
    (tail_short s cap hc hL hd) (tail_bound s cap hc hL hd)
end TorsionFreeZeroDivisors.SampleGraph.ClosedWords

end

end OAI
