import OAI.Combinatorics.MatchingCount.Complexity.TreeFractionCosts
import OAI.Combinatorics.MatchingCount.Machines.TreeFastLookup
import OAI.Combinatorics.MatroidCounting.CommonBases

namespace OAI

/-! # Binary fraction median with polynomial running time -/

namespace ContingencyTables.MedianFractionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.TreeFraction Polynomial

abbrev State := Fraction × (List Fraction × List Fraction)

def insertRaw (q : Fraction) : List Fraction → List Fraction
  | [] => [q]
  | x::xs => if TreeFraction.less (x,q) then x::insertRaw q xs else q::x::xs

def step (z : Fraction × State) : State :=
  (z.2.1,(z.1::z.2.2.1,
    if TreeFraction.less (z.1,z.2.1) then z.1::z.2.2.2 else z.2.1::z.1::z.2.2.1))

def stepRealizer : Realizer step := by
  let q : Realizer (fun z : Fraction × State => z.2.1) := composition second first
  let xs : Realizer (fun z : Fraction × State => z.1::z.2.2.1) :=
    composition (pair first (composition (composition second second) first)) listCons
  let yes : Realizer (fun z : Fraction × State => z.1::z.2.2.2) :=
    composition (pair first (composition (composition second second) second)) listCons
  let no : Realizer (fun z : Fraction × State => z.2.1::z.1::z.2.2.1) :=
    composition (pair q xs) listCons
  exact pair q (pair xs (choose (composition (pair first q) TreeFraction.lessRealizer) yes no))

lemma polynomial_step : PolynomialTime stepRealizer := by
  unfold stepRealizer
  exact polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_pair
      (polynomial_composition (polynomial_pair polynomial_first
        (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
          polynomial_first)) polynomial_listCons)
      (polynomial_choose
        (polynomial_composition (polynomial_pair polynomial_first
          (polynomial_composition polynomial_second polynomial_first)) TreeFraction.polynomial_less)
        (polynomial_composition (polynomial_pair polynomial_first
          (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
            polynomial_second)) polynomial_listCons)
        (polynomial_composition (polynomial_pair
          (polynomial_composition polynomial_second polynomial_first)
          (polynomial_composition (polynomial_pair polynomial_first
            (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
              polynomial_first)) polynomial_listCons)) polynomial_listCons)))

def insert (z : Fraction × List Fraction) : List Fraction :=
  (z.2.reverse.foldl (fun s x => step (x,s)) (z.1,([],[z.1]))).2.2

lemma insert_fold (q : Fraction) (xs : List Fraction) :
    xs.reverse.foldl (fun s x => step (x,s)) (q,([],[q])) = (q,(xs,insertRaw q xs)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.reverse_cons,List.foldl_append,ih,List.foldl_cons,List.foldl_nil]
    rfl

lemma insert_eq (q : Fraction) (xs : List Fraction) : insert (q,xs)=insertRaw q xs := by
  unfold insert
  rw [insert_fold]

lemma insert_weight (q : Fraction) (xs : List Fraction) :
    weight (insertRaw q xs)=1+weight q+weight xs := by
  induction xs with
  | nil => simp [insertRaw]
  | cons x xs ih =>
    simp only [insertRaw]
    split <;> simp only [weight_cons,ih]
    all_goals omega

lemma fold_weight (xs : List Fraction) (q : Fraction) (zs ys : List Fraction) :
    let t := xs.foldl (fun s x => step (x,s)) (q,(zs,ys))
    t.1=q ∧ weight t.2.1+1=weight zs+weight xs ∧
      weight t.2.2 ≤ max (weight ys) (weight q+weight zs+1)+weight xs := by
  induction xs generalizing zs ys with
  | nil =>
    exact ⟨rfl,by simp only [List.foldl_nil,weight_nil],by
      simpa only [List.foldl_nil,weight_nil] using
        (Nat.le_max_left (weight ys) (weight q+weight zs+1)).trans (Nat.le_succ _)⟩
  | cons x xs ih =>
    rw [List.foldl_cons]
    change (let t := xs.foldl (fun s x => step (x,s)) (q,(x::zs,if TreeFraction.less (x,q) then x::ys else q::x::zs));
      t.1=q ∧ weight t.2.1+1=weight zs+weight (x::xs) ∧
        weight t.2.2 ≤ max (weight ys) (weight q+weight zs+1)+weight (x::xs))
    have hh := ih (x::zs) (if TreeFraction.less (x,q) then x::ys else q::x::zs)
    dsimp only at hh ⊢
    refine ⟨hh.1,?_,?_⟩
    · simp only [weight_cons] at hh ⊢; omega
    · by_cases h : TreeFraction.less (x,q)=true
      · simp only [h,ite_true,weight_cons] at hh ⊢; omega
      · simp only [h,Bool.false_eq_true,ite_false,weight_cons] at hh ⊢; omega

lemma state_weight (s : State) :
    weight s=1+weight s.1+(1+weight s.2.1+weight s.2.2) := by
  rcases s with ⟨q,xs,ys⟩
  simp only [weight_prod]

lemma polynomial_stepFold : PolynomialTime (fold stepRealizer) := by
  apply polynomial_fold polynomial_step (5*X+5)
  intro xs s pre post he
  rcases s with ⟨q,zs,ys⟩
  have hh := fold_weight pre q zs ys
  have hp := weight_prefix he
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  rw [state_weight,hh.1]
  omega

def insertRealizer : Realizer insert := by
  let prep : Realizer (fun z : Fraction × List Fraction => (z.2.reverse,(z.1,([],[z.1])))) :=
    pair (composition second reverse)
      (pair first (pair (constant ([] : List Fraction)) (composition (pair first (constant ([] : List Fraction))) listCons)))
  let tail : Realizer (fun z : List Fraction × State =>
      (z.1.foldl (fun s x => step (x,s)) z.2).2.2) :=
    composition (f := fun z : List Fraction × State =>
      (z.1.foldl (fun s x => step (x,s)) z.2).2) (g := fun z => z.2)
      (composition (fold stepRealizer) second) second
  exact composition
    (f := fun z : Fraction × List Fraction => (z.2.reverse,(z.1,([],[z.1]))))
    (g := fun z : List Fraction × State =>
      (z.1.foldl (fun s x => step (x,s)) z.2).2.2) prep tail

lemma polynomial_insert : PolynomialTime insertRealizer := by
  unfold insertRealizer
  exact polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_second polynomial_reverse)
      (polynomial_pair polynomial_first (polynomial_pair (polynomial_constant ([] : List Fraction))
        (polynomial_composition (polynomial_pair polynomial_first (polynomial_constant ([] : List Fraction)))
          polynomial_listCons))))
    (polynomial_composition (polynomial_composition polynomial_stepFold polynomial_second)
      polynomial_second)

def sort (xs : List Fraction) : List Fraction :=
  xs.reverse.foldl (fun s x => insert (x,s)) []

def sortRealizer : Realizer sort :=
  composition (f := fun xs : List Fraction => (xs.reverse,([] : List Fraction)))
    (g := fun z : List Fraction × List Fraction => z.1.foldl (fun s x => insert (x,s)) z.2)
    (pair reverse (constant [])) (fold insertRealizer)

lemma sortFold_weight (xs zs : List Fraction) :
    weight (xs.foldl (fun s x => insert (x,s)) zs)+1=weight zs+weight xs := by
  induction xs generalizing zs with
  | nil => simp
  | cons x xs ih =>
    have hh := ih (insert (x,zs))
    simp only [List.foldl_cons,insert_eq,insert_weight,weight_cons] at hh ⊢
    omega

lemma polynomial_insertFold : PolynomialTime (fold insertRealizer) := by
  apply polynomial_fold polynomial_insert (2*X)
  intro xs zs pre post he
  have hh := sortFold_weight pre zs
  have hp := weight_prefix he
  simp only [eval_mul,eval_ofNat,eval_X,weight_prod]
  omega

lemma polynomial_sort : PolynomialTime sortRealizer :=
  polynomial_composition (polynomial_pair polynomial_reverse (polynomial_constant ([] : List Fraction)))
    polynomial_insertFold

lemma insert_pos (q : Fraction) (xs : List Fraction) (hq : 0 < q.2)
    (hx : ∀ x∈xs,0 < x.2) : ∀ y∈insertRaw q xs,0 < y.2 := by
  induction xs with
  | nil => simpa only [insertRaw,List.mem_singleton] using fun y hy => hy ▸ hq
  | cons x xs ih =>
    have hxx := hx x (by simp)
    have ht := ih (fun y hy => hx y (by simp [hy]))
    simp only [insertRaw]
    split <;> intro y hy <;> simp only [List.mem_cons] at hy
    · rcases hy with rfl|hy
      · exact hxx
      · exact ht y hy
    · rcases hy with rfl|rfl|hy
      · exact hq
      · exact hxx
      · exact hx y (by simp [hy])

lemma insert_map (q : Fraction) (xs : List Fraction) (hq : 0 < q.2)
    (hx : ∀ x∈xs,0 < x.2) :
    (insertRaw q xs).map val=(xs.map val).orderedInsert (·≤·) (val q) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hxx := hx x (by simp)
    have ht := ih (fun y hy => hx y (by simp [hy]))
    simp only [insertRaw,List.map_cons,List.orderedInsert_cons,TreeFraction.less_val x q hxx hq]
    by_cases h : val x < val q
    · simp [h,not_le.mpr h,ht]
    · simp [h,le_of_not_gt h]

lemma sort_cons (x : Fraction) (xs : List Fraction) : sort (x::xs)=insert (x,sort xs) := by
  simp only [sort,List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]

lemma sort_pos (xs : List Fraction) (hx : ∀ x∈xs,0 < x.2) : ∀ y∈sort xs,0 < y.2 := by
  induction xs with
  | nil => simp [sort]
  | cons x xs ih =>
    rw [sort_cons,insert_eq]
    exact insert_pos x (sort xs) (hx x (by simp))
      (ih (fun y hy => hx y (by simp [hy])))

lemma sort_map (xs : List Fraction) (hx : ∀ x∈xs,0 < x.2) :
    (sort xs).map val=(xs.map val).mergeSort (·≤·) := by
  rw [List.mergeSort_eq_insertionSort]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have ht : ∀ y∈xs,0 < y.2 := fun y hy => hx y (by simp [hy])
    rw [sort_cons,insert_eq,insert_map x (sort xs) (hx x (by simp)) (sort_pos xs ht),ih ht]
    rfl

def median (xs : List Fraction) : Fraction :=
  (sort (xs.map TreeFraction.normalize)).getD (xs.length/2) (0,1)

def medianRealizer : Realizer median :=
  composition (f := fun xs : List Fraction => (sort (xs.map TreeFraction.normalize),xs.length/2))
    (g := fun z : List Fraction × ℕ => z.1.getD z.2 (0,1)) (pair (composition (f := fun xs : List Fraction => xs.map TreeFraction.normalize)
      (g := sort) (TreeTyped.map normalizeRealizer) sortRealizer)
    (composition (pair listLength (constant 2)) quotient)) (getDFast (0,1))

lemma polynomial_median : PolynomialTime medianRealizer :=
  polynomial_composition
    (polynomial_pair (polynomial_composition (polynomial_map TreeFraction.polynomial_normalize)
      polynomial_sort)
      (polynomial_composition (polynomial_pair polynomial_listLength (polynomial_constant 2))
        polynomial_quotient)) (polynomial_getDFast (0,1))

lemma median_val (xs : List Fraction) :
    val (median xs)=CommonBasesFPRAS.rationalMedian (xs.map val) := by
  have hs := sort_map (xs.map TreeFraction.normalize) (by
    intro y hy
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hy
    exact normalize_den_pos x)
  have hm : (xs.map TreeFraction.normalize).map val=xs.map val := by
    simp only [List.map_map,Function.comp_def,normalize_val]
  rw [hm] at hs
  unfold median CommonBasesFPRAS.rationalMedian
  rw [←hs,List.length_map]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases (sort (xs.map TreeFraction.normalize))[xs.length/2]? <;> simp only [Option.getD_none,Option.map_none,Option.getD_some,Option.map_some,val, Nat.cast_zero,zero_div]

end ContingencyTables.MedianFractionProgram

end OAI
