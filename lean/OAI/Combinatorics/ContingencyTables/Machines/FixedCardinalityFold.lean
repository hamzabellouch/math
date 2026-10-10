import OAI.Combinatorics.ContingencyTables.Machines.FixedCardinalityProgram

namespace OAI

/-! # A polynomial sequential list program for the subset draw

The accumulator retains the remaining population and requested size,
and records one inclusion bit per input word. Both counters decrease;
only the output list grows. The final program reverses that list once.
-/

namespace ContingencyTables.FixedCardinalityProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

abbrev DrawState := (ℕ×ℕ)×List Bool

def advance (z : List Bool×DrawState) : DrawState :=
  let b := includeCode (z.2.1,z.1)
  ((z.2.1.1-1,if b then z.2.1.2-1 else min z.2.1.2 (z.2.1.1-1)),b::z.2.2)

def advanceRealizer : Realizer advance := by
  let N : Realizer (fun z : List Bool×DrawState => z.2.1.1) :=
    composition (composition second first) first
  let K : Realizer (fun z : List Bool×DrawState => z.2.1.2) :=
    composition (composition second first) second
  let B : Realizer (fun z : List Bool×DrawState => includeCode (z.2.1,z.1)) :=
    composition (pair (composition second first) first) includeRealizer
  let R := composition (pair N (constant 1)) subtract
  let T := choose B (composition (pair K (constant 1)) subtract)
    (composition (pair K R) minimum)
  exact pair (pair R T) (composition (pair B (composition second second)) listCons)

theorem polynomial_advance : PolynomialTime advanceRealizer := by
  unfold advanceRealizer
  have hn : PolynomialTime (composition
      (composition (second (A := List Bool) (B := DrawState)) first) first) :=
    polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_first
  have hk : PolynomialTime (composition
      (composition (second (A := List Bool) (B := DrawState)) first) second) :=
    polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_second
  have hb : PolynomialTime (composition
      (pair (composition (second (A := List Bool) (B := DrawState)) first) first)
      includeRealizer) := polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_second polynomial_first) polynomial_first)
    polynomial_include
  have hr := polynomial_composition (polynomial_pair hn (polynomial_constant 1)) polynomial_subtract
  exact polynomial_pair
    (polynomial_pair hr (polynomial_choose hb
      (polynomial_composition (polynomial_pair hk (polynomial_constant 1)) polynomial_subtract)
      (polynomial_composition (polynomial_pair hk hr) polynomial_minimum)))
    (polynomial_composition (polynomial_pair hb
      (polynomial_composition polynomial_second polynomial_second)) polynomial_listCons)

lemma advance_bounds (word : List Bool) (s : DrawState) :
    (advance (word,s)).1.1 ≤ s.1.1 ∧ (advance (word,s)).1.2 ≤ s.1.2 ∧
      weight (advance (word,s)).2 ≤ weight s.2+4 := by
  refine ⟨Nat.sub_le _ _,?_,?_⟩
  · change (if includeCode (s.1,word) then s.1.2-1 else min s.1.2 (s.1.1-1)) ≤ s.1.2
    split_ifs
    · exact Nat.sub_le _ _
    · exact min_le_left _ _
  · change weight (includeCode (s.1,word)::s.2)≤_
    rw [weight_cons]
    have h := weight_bool (includeCode (s.1,word))
    omega

lemma fold_bounds (words : List (List Bool)) (s : DrawState) :
    let out := words.foldl (fun s word => advance (word,s)) s
    out.1.1 ≤ s.1.1 ∧ out.1.2 ≤ s.1.2 ∧ weight out.2 ≤ weight s.2+4*words.length := by
  induction words generalizing s with
  | nil => exact ⟨le_rfl,le_rfl,by simp⟩
  | cons w ws ih =>
    have hs := advance_bounds w s
    have ht := ih (advance (w,s))
    refine ⟨ht.1.trans hs.1,ht.2.1.trans hs.2.1,?_⟩
    simp only [List.foldl_cons,List.length_cons]
    omega

def drawWords (z : (ℕ×ℕ)×List (List Bool)) : List Bool :=
  (z.2.foldl (fun s word => advance (word,s)) (z.1,[])).2.reverse

def prepareWords (z : (ℕ×ℕ)×List (List Bool)) : List (List Bool)×DrawState := (z.2,(z.1,[]))

def prepareWordsRealizer : Realizer prepareWords := pair second (pair first (constant []))

def runWords (z : (ℕ×ℕ)×List (List Bool)) : DrawState :=
  z.2.foldl (fun s word => advance (word,s)) (z.1,[])

def runWordsRealizer : Realizer runWords := composition prepareWordsRealizer (fold advanceRealizer)

def outputRealizer : Realizer (fun s : DrawState => s.2.reverse) := composition second reverse

def drawWordsRealizer : Realizer drawWords :=
  composition (f := runWords) (g := fun s : DrawState => s.2.reverse)
    runWordsRealizer outputRealizer

theorem polynomial_drawWords : PolynomialTime drawWordsRealizer := by
  have hf : PolynomialTime (fold advanceRealizer) := by
    apply polynomial_fold polynomial_advance (20*(X+1))
    intro words s pre post he
    let S := weight (words,s)
    let out := pre.foldl (fun s word => advance (word,s)) s
    have hs : weight s≤S := weight_snd (words,s)
    have hn : s.1.1.size≤S :=
      (size_le_weight _).trans ((weight_fst s.1).trans ((weight_fst s).trans hs))
    have hk : s.1.2.size≤S :=
      (size_le_weight _).trans ((weight_snd s.1).trans ((weight_fst s).trans hs))
    have hb : weight s.2≤S := (weight_snd s).trans hs
    have hp : pre.length≤S := (list_length_le_weight pre).trans
      ((weight_prefix he).trans (weight_fst (words,s)))
    have ht := fold_bounds pre s
    have hon : weight out.1.1≤4*out.1.1.size+1 := weight_nat_le out.1.1
    have hok : weight out.1.2≤4*out.1.2.size+1 := weight_nat_le out.1.2
    have hsn : out.1.1.size≤S := (Nat.size_le_size ht.1).trans hn
    have hsk : out.1.2.size≤S := (Nat.size_le_size ht.2.1).trans hk
    have hlist : weight out.2≤weight s.2+4*pre.length := ht.2.2
    have hnweight : weight out.1.1≤4*S+1 := hon.trans (by omega)
    have hkweight : weight out.1.2≤4*S+1 := hok.trans (by omega)
    have hlweight : weight out.2≤5*S := by omega
    have hw : weight out=weight out.1.1+weight out.1.2+weight out.2+2 := by
      change weight ((out.1.1,out.1.2),out.2)=_
      simp only [weight_prod]
      omega
    simp only [eval_mul,eval_ofNat,eval_add,eval_X,eval_one]
    change weight out≤20*(S+1)
    rw [hw]
    omega
  unfold drawWordsRealizer runWordsRealizer prepareWordsRealizer outputRealizer
  exact polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_second (polynomial_pair polynomial_first (polynomial_constant []))) hf)
    (polynomial_composition polynomial_second polynomial_reverse)

def sampleWords (n k : ℕ) : List (List Bool) → List Bool
  | [] => []
  | w::ws =>
      let b := includeCode ((n,k),w)
      b::sampleWords (n-1) (if b then k-1 else min k (n-1)) ws

lemma fold_output (words : List (List Bool)) (n k : ℕ) (acc : List Bool) :
    (words.foldl (fun s word => advance (word,s)) ((n,k),acc)).2=
      (sampleWords n k words).reverse++acc := by
  induction words generalizing n k acc with
  | nil => simp [sampleWords]
  | cons w ws ih =>
    rw [List.foldl_cons]
    change (ws.foldl (fun s word => advance (word,s))
      ((n-1,if includeCode ((n,k),w) then k-1 else min k (n-1)),
        includeCode ((n,k),w)::acc)).2=_
    rw [ih]
    simp only [sampleWords,List.reverse_cons,List.append_assoc,List.singleton_append]

lemma drawWords_eq (n k : ℕ) (words : List (List Bool)) :
    drawWords ((n,k),words)=sampleWords n k words := by
  unfold drawWords
  rw [fold_output]
  simp

noncomputable section

theorem sampleWords_ofFn (B n k : ℕ) (words : Fin n → Fin B → Bool) :
    sampleWords n k (List.ofFn (fun i => List.ofFn (words i)))=
      List.ofFn (FixedCardinalityBits.draw B n k words) := by
  induction n generalizing k with
  | zero => simp [sampleWords,FixedCardinalityBits.draw]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [sampleWords,includeCode_ofFn,Nat.add_sub_cancel]
    rw [ih]
    simp only [FixedCardinalityBits.draw,FixedCardinalityLaw.remaining,List.ofFn_succ,
      Fin.cons_zero,Fin.cons_succ]
    rfl

/-- The polynomial list program has exactly the proved sequential
finite-word semantics, including empty populations. -/
theorem drawWords_ofFn (B n k : ℕ) (words : Fin n → Fin B → Bool) :
    drawWords ((n,k),List.ofFn (fun i => List.ofFn (words i)))=
      List.ofFn (FixedCardinalityBits.draw B n k words) := by
  rw [drawWords_eq]
  exact sampleWords_ofFn B n k words

end
end ContingencyTables.FixedCardinalityProgram

end OAI
