import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section

noncomputable section
namespace SKGap.Noncrossing
universe u v

inductive Letter (D : Type*) where
  | diag : D → Letter D
  | noise : Letter D
  deriving DecidableEq

inductive Diagram (D : Type*) where
  | nil : Diagram D
  | diag : D → Diagram D → Diagram D
  | arch : Diagram D → Diagram D → Diagram D
  deriving DecidableEq

namespace Diagram
variable {D : Type*}

def word : Diagram D → List (Letter D)
  | nil => []
  | diag a d => .diag a :: d.word
  | arch a b => .noise :: (a.word ++ (.noise :: b.word))

def size : Diagram D → ℕ
  | nil => 0
  | diag _ d => d.size+1
  | arch a b => a.size+b.size+2

@[simp] lemma word_length (d : Diagram D) : d.word.length = d.size := by
  induction d with
  | nil => rfl
  | diag a d ih => simp [word, size, ih]
  | arch a b ia ib => simp [word, size, ia, ib]; omega

def insert (outer : Diagram D) (p : ℕ) (inside : Diagram D) : Diagram D :=
  if p=0 then .arch inside outer else
    match outer with
    | nil => .arch inside .nil
    | diag a d => .diag a (d.insert (p-1) inside)
    | arch a b =>
      if p ≤ a.size+1 then .arch (a.insert (p-1) inside) b
      else .arch a (b.insert (p-(a.size+2)) inside)

@[simp] lemma insert_zero (d e : Diagram D) : d.insert 0 e = .arch e d := by
  cases d <;> simp [insert]

lemma insert_size (d e : Diagram D) (p : ℕ) :
    (d.insert p e).size = d.size+e.size+2 := by
  induction d generalizing p with
  | nil => simp [insert, size]
  | diag a d ih =>
    by_cases hp : p=0
    · simp [insert, hp, size]; omega
    · simp [insert, hp, size, ih]; omega
  | arch a b ia ib =>
    by_cases hp : p=0
    · simp [insert, hp, size]; omega
    · simp only [insert, hp, ↓reduceIte]
      split_ifs <;> simp only [size, ia, ib] <;> omega

lemma insert_word (d e : Diagram D) (p : ℕ) (hp : p≤d.size) :
    (d.insert p e).word = d.word.take p ++
      (.noise :: (e.word ++ (.noise :: d.word.drop p))) := by
  induction d generalizing p with
  | nil => have : p=0 := by simpa [size] using hp
           subst p; simp [insert, word]
  | diag a d ih =>
    cases p with
    | zero => simp [word]
    | succ p =>
      have h : p≤d.size := by simpa [size] using hp
      simpa [insert, word, List.take_succ_cons, List.drop_succ_cons] using
        congrArg (List.cons (.diag a)) (ih p h)
  | arch a b ia ib =>
    cases p with
    | zero => simp [word]
    | succ p =>
      by_cases h : p≤a.size
      · have he := ia p h
        simp only [insert, Nat.succ_ne_zero, ↓reduceIte, Nat.add_one_sub_one]
        rw [ite_eq_left (by omega), word, he]
        simp [word, List.take_append_of_le_length (l₁ := a.word) (i := p) (by simpa using h),
          List.drop_append_of_le_length (l₁ := a.word) (i := p) (by simpa using h), List.append_assoc]
      · have h' : p-(a.size+1)≤b.size := by simp only [size] at hp; omega
        have he := ib (p-(a.size+1)) h'
        simp only [insert, Nat.succ_ne_zero, ↓reduceIte]
        rw [ite_eq_right (by omega)]
        have hh : p+1-(a.size+2)=p-(a.size+1) := by omega
        rw [hh, word, he]
        simp only [word, List.take_succ_cons, List.drop_succ_cons]
        rw [List.take_append, List.drop_append]
        have hle : a.word.length≤p := by simp; omega
        rw [List.take_of_length_le hle, List.drop_eq_nil_of_le hle]
        simp only [List.nil_append, word_length]
        have hk : p-a.size = (p-(a.size+1))+1 := by omega
        rw [hk]
        simp [List.append_assoc]

structure Cut (D : Type*) where
  start : ℕ
  inside : Diagram D
  outside : Diagram D
  closing : Bool
  deriving DecidableEq

def Cut.diag (a : D) (c : Cut D) : Cut D :=
  ⟨c.start+1,c.inside,.diag a c.outside,c.closing⟩
def Cut.inner (b : Diagram D) (c : Cut D) : Cut D :=
  ⟨c.start+1,c.inside,.arch c.outside b,c.closing⟩
def Cut.tail (a : Diagram D) (c : Cut D) : Cut D :=
  ⟨a.size+2+c.start,c.inside,.arch a c.outside,c.closing⟩

def cut : Diagram D → ℕ → Option (Cut D)
  | nil, _ => none
  | diag _ _, 0 => none
  | diag a d, i+1 => (d.cut i).map (Cut.diag a)
  | arch a b, 0 => some ⟨0,a,b,false⟩
  | arch a b, i+1 =>
      if i<a.size then (a.cut i).map (Cut.inner b)
      else if i=a.size then some ⟨0,a,b,true⟩
      else (b.cut (i-(a.size+1))).map (Cut.tail a)

lemma cut_spec (d : Diagram D) (i : ℕ) (c : Cut D) (hc : d.cut i=some c) :
    c.start≤c.outside.size ∧
    i=c.start+(if c.closing then c.inside.size+1 else 0) ∧
    c.outside.insert c.start c.inside = d := by
  induction d generalizing i c with
  | nil => simp [cut] at hc
  | diag a d ih =>
    cases i with
    | zero => simp [cut] at hc
    | succ i =>
      simp only [cut, Option.map_eq_some_iff] at hc
      obtain ⟨e,he,rfl⟩ := hc
      obtain ⟨h1,h2,h3⟩ := ih i e he
      refine ⟨by simpa [Cut.diag,size] using h1, ?_, ?_⟩
      · cases hcl : e.closing <;>
          simp only [Cut.diag, hcl, Bool.false_eq_true, ↓reduceIte] at h2 ⊢ <;> omega
      · simpa [Cut.diag,insert] using congrArg (Diagram.diag a) h3
  | arch a b ia ib =>
    cases i with
    | zero =>
      simp only [cut,Option.some.injEq] at hc
      subst c; simp
    | succ i =>
      simp only [cut] at hc
      split_ifs at hc with hi he
      · obtain ⟨e,he,rfl⟩ := Option.map_eq_some_iff.mp hc
        obtain ⟨h1,h2,h3⟩ := ia i e he
        refine ⟨by simp only [Cut.inner,size]; omega, ?_, ?_⟩
        · cases hcl : e.closing <;>
          simp only [Cut.inner, hcl, Bool.false_eq_true, ↓reduceIte] at h2 ⊢ <;> omega
        · simp only [Cut.inner,insert,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,
            ↓reduceIte,Nat.add_one_sub_one]
          rw [ite_eq_left (by omega),h3]
      · simp only [Option.some.injEq] at hc
        subst c; simp [he]
      · obtain ⟨e,he',rfl⟩ := Option.map_eq_some_iff.mp hc
        obtain ⟨h1,h2,h3⟩ := ib (i-(a.size+1)) e he'
        refine ⟨by simp only [Cut.tail,size]; omega, ?_, ?_⟩
        · cases hcl : e.closing <;>
          simp only [Cut.tail, hcl, Bool.false_eq_true, ↓reduceIte] at h2 ⊢ <;> omega
        · simp only [Cut.tail,insert]
          rw [ite_eq_right (by omega), ite_eq_right (by omega)]
          rw [show a.size+2+e.start-(a.size+2)=e.start by omega, h3]

lemma cut_insert (d e : Diagram D) (p : ℕ) (hp : p≤d.size) (cl : Bool) :
    (d.insert p e).cut (p+(if cl then e.size+1 else 0)) =
      some ⟨p,e,d,cl⟩ := by
  induction d generalizing p with
  | nil =>
    have hh : p=0 := by simpa [size] using hp
    subst p
    cases cl <;> simp [insert,cut]
  | diag a d ih =>
    cases p with
    | zero => cases cl <;> simp [cut]
    | succ p =>
      have h : p≤d.size := by simpa [size] using hp
      have he := ih p h
      rw [show (Diagram.diag a d).insert (p+1) e = .diag a (d.insert p e) by simp [insert]]
      have hi : p+1+(if cl then e.size+1 else 0) = (p+(if cl then e.size+1 else 0))+1 := by omega
      rw [hi, cut, he]
      simp [Cut.diag]
  | arch a b ia ib =>
    cases p with
    | zero => cases cl <;> simp [cut]
    | succ p =>
      by_cases h : p≤a.size
      · have he := ia p h
        rw [show (a.arch b).insert (p+1) e = .arch (a.insert p e) b by
          simp [insert, show p+1≤a.size+1 by omega]]
        have hi : p+1+(if cl then e.size+1 else 0) = (p+(if cl then e.size+1 else 0))+1 := by omega
        rw [hi,cut,ite_eq_left]
        · rw [he]; simp [Cut.inner]
        · rw [insert_size]; cases cl <;> simp <;> omega
      · have hp' : p-(a.size+1)≤b.size := by simp only [size] at hp; omega
        have he := ib (p-(a.size+1)) hp'
        rw [show (a.arch b).insert (p+1) e = .arch a (b.insert (p-(a.size+1)) e) by
          simp [insert, show ¬p+1≤a.size+1 by omega,
            show p+1-(a.size+2)=p-(a.size+1) by omega]]
        have hi : p+1+(if cl then e.size+1 else 0) = (p+(if cl then e.size+1 else 0))+1 := by omega
        rw [hi,cut,ite_eq_right (by omega),ite_eq_right (by omega)]
        have hh : p+(if cl then e.size+1 else 0)-(a.size+1) =
            p-(a.size+1)+(if cl then e.size+1 else 0) := by omega
        rw [hh,he]
        simp only [Option.map_some,Cut.tail]
        congr 2
        omega

lemma cut_exists_iff (d : Diagram D) (i : ℕ) :
    (∃ c, d.cut i=some c) ↔ d.word[i]?=some .noise := by
  induction d generalizing i with
  | nil => simp [cut, word]
  | diag a d ih =>
    cases i with
    | zero => simp [cut,word]
    | succ i => simpa [cut,word,Option.map_eq_some_iff] using ih i
  | arch a b ia ib =>
    cases i with
    | zero => simp [cut,word]
    | succ i =>
      by_cases hi : i<a.size
      · have hi' : i<a.word.length := by simpa using hi
        simp only [cut,hi,↓reduceIte,word,List.getElem?_cons_succ]
        rw [List.getElem?_append_left hi']
        simpa [Option.map_eq_some_iff] using ia i
      · by_cases he : i=a.size
        · subst i
          simp [cut,word]
        · have hr : a.word.length ≤ i := by simp; omega
          have hh : i-a.size = (i-(a.size+1))+1 := by omega
          simp [cut,hi,he,word,List.getElem?_append_right hr,hh,ib,
            Option.map_eq_some_iff]

def labels (F : List (Letter D)) : Finset D := by
  classical
  exact (F.filterMap (fun l => match l with | .diag a => some a | .noise => none)).toFinset

@[simp] lemma labels_nil : labels ([] : List (Letter D)) = ∅ := rfl
@[simp] lemma labels_diag [DecidableEq D] (a : D) (F : List (Letter D)) :
    labels (.diag a::F) = Insert.insert a (labels F) := by
  ext x
  simp [labels]
@[simp] lemma labels_noise (F : List (Letter D)) : labels (.noise::F)=labels F := by
  simp [labels]
@[simp] lemma labels_append [DecidableEq D] (F G : List (Letter D)) : labels (F++G)=labels F∪labels G := by
  ext x
  simp [labels,List.filterMap_append]

def supply (A : Finset D) : ℕ → Finset (Diagram D)
  | 0 => {.nil}
  | n+1 => by
      classical
      exact {.nil} ∪ A.biUnion (fun a => (supply A n).image (.diag a)) ∪
        (supply A n).biUnion (fun a => (supply A n).image (.arch a))

lemma mem_supply (A : Finset D) (n : ℕ) (d : Diagram D)
    (hn : d.size≤n) (hA : labels d.word⊆A) : d∈supply A n := by
  classical
  induction n generalizing d with
  | zero =>
    cases d with
    | nil => simp [supply]
    | diag a d => simp [size] at hn
    | arch a b => simp [size] at hn
  | succ n ih =>
    cases d with
    | nil => simp [supply]
    | diag a d =>
      have ha : a∈A := hA (by simp [word])
      have hd : labels d.word⊆A := by
        intro x hx; apply hA; simp [word,hx]
      have hs : d.size≤n := by simpa [size] using hn
      simp only [supply,Finset.mem_union,Finset.mem_singleton,Finset.mem_biUnion,Finset.mem_image]
      exact Or.inl (Or.inr ⟨a,ha,d,ih d hs hd,rfl⟩)
    | arch a b =>
      have ha : labels a.word⊆A := by
        intro x hx; apply hA; simp [word,hx]
      have hb : labels b.word⊆A := by
        intro x hx; apply hA; simp [word,hx]
      have hs : a.size≤n ∧ b.size≤n := by simp only [size] at hn; omega
      simp only [supply,Finset.mem_union,Finset.mem_biUnion,Finset.mem_image]
      exact Or.inr ⟨a,ih a hs.1 ha,b,ih b hs.2 hb,rfl⟩

def enumerate (F : List (Letter D)) : Finset (Diagram D) := by
  classical
  exact (supply (labels F) F.length).filter (fun d => d.word=F)

@[simp] theorem mem_enumerate (F : List (Letter D)) (d : Diagram D) :
    d∈enumerate F ↔ d.word=F := by
  classical
  simp only [enumerate,Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨mem_supply _ _ d (by rw [← word_length,h]) (by rw [h]),h⟩⟩

def Paired (F : List (Letter D)) := {d : Diagram D // d.word=F}

instance pairedFintype (F : List (Letter D)) : Fintype (Paired F) :=
  Fintype.ofFinset (enumerate F) (fun d => mem_enumerate F d)

def CutAt (F : List (Letter D)) (k : ℕ) :=
  {c : Cut D // c.start≤c.outside.size ∧
    k=c.start+(if c.closing then c.inside.size+1 else 0) ∧
    (c.outside.insert c.start c.inside).word=F}

def markedCut (d : Diagram D) (k : ℕ) (hk : d.word[k]?=some .noise) : Cut D :=
  Classical.choose ((cut_exists_iff d k).mpr hk)
lemma cut_markedCut (d : Diagram D) (k : ℕ) (hk : d.word[k]?=some .noise) :
    d.cut k=some (d.markedCut k hk) :=
  Classical.choose_spec ((cut_exists_iff d k).mpr hk)

def cutEquiv (F : List (Letter D)) (k : ℕ) (hk : F[k]?=some .noise) :
    Paired F ≃ CutAt F k where
  toFun d := by
    have hd : d.val.word[k]?=some .noise := by rw [d.property]; exact hk
    let c := d.val.markedCut k hd
    have hs := cut_spec d.val k c (cut_markedCut _ _ _)
    exact ⟨c,hs.1,hs.2.1,by rw [hs.2.2]; exact d.property⟩
  invFun c := ⟨c.val.outside.insert c.val.start c.val.inside,c.property.2.2⟩
  left_inv d := by
    apply Subtype.ext
    have hd : d.val.word[k]?=some .noise := by rw [d.property]; exact hk
    exact (cut_spec d.val k _ (cut_markedCut d.val k hd)).2.2
  right_inv c := by
    apply Subtype.ext
    have hc := cut_insert c.val.outside c.val.inside c.val.start c.property.1 c.val.closing
    rw [← c.property.2.1] at hc
    have hd : (c.val.outside.insert c.val.start c.val.inside).word[k]?=some .noise := by
      rw [c.property.2.2]; exact hk
    exact Option.some.inj ((cut_markedCut _ k hd).symm.trans hc)

@[ext]
structure PairShape (F : List (Letter D)) (k : ℕ) where
  before : List (Letter D)
  between : List (Letter D)
  after : List (Letter D)
  closing : Bool
  word_eq : F = before ++ (.noise :: (between ++ (.noise :: after)))
  mark_eq : k = before.length+(if closing then between.length+1 else 0)

lemma PairShape.length_bound {F : List (Letter D)} {k : ℕ} (s : PairShape F k) :
    s.before.length<F.length ∧ s.between.length<F.length := by
  rcases s with ⟨U,V,Q,cl,hF,hk⟩
  subst F
  simp only [List.length_append,List.length_cons]
  omega

lemma PairShape.before_eq_take {F : List (Letter D)} {k : ℕ} (s : PairShape F k) :
    s.before=F.take s.before.length := by
  rcases s with ⟨U,V,Q,cl,hF,hk⟩
  subst F
  simp
lemma PairShape.between_eq_take {F : List (Letter D)} {k : ℕ} (s : PairShape F k) :
    s.between=(F.drop (s.before.length+1)).take s.between.length := by
  rcases s with ⟨U,V,Q,cl,hF,hk⟩
  subst F
  simp
lemma PairShape.after_eq_drop {F : List (Letter D)} {k : ℕ} (s : PairShape F k) :
    s.after=F.drop (s.before.length+s.between.length+2) := by
  rcases s with ⟨U,V,Q,cl,hF,hk⟩
  subst F
  dsimp
  simp [show U.length+V.length+2=U.length+(V.length+2) by omega]

def PairShape.code {F : List (Letter D)} {k : ℕ} (s : PairShape F k) :
    Fin F.length × Fin F.length × Bool :=
  (⟨s.before.length,s.length_bound.1⟩,⟨s.between.length,s.length_bound.2⟩,s.closing)

lemma PairShape.code_injective (F : List (Letter D)) (k : ℕ) :
    Function.Injective (PairShape.code (F := F) (k := k)) := by
  intro a b h
  have h1 : a.before.length=b.before.length := congrArg (fun x => x.1.val) h
  have h2 : a.between.length=b.between.length := congrArg (fun x => x.2.1.val) h
  have h3 : a.closing=b.closing := congrArg (fun x => x.2.2) h
  apply PairShape.ext
  · rw [a.before_eq_take,b.before_eq_take,h1]
  · rw [a.between_eq_take,b.between_eq_take,h1,h2]
  · rw [a.after_eq_drop,b.after_eq_drop,h1,h2]
  · exact h3

instance pairShapeFinite (F : List (Letter D)) (k : ℕ) : Finite (PairShape F k) :=
  Finite.of_injective _ (PairShape.code_injective F k)
instance pairShapeFintype (F : List (Letter D)) (k : ℕ) : Fintype (PairShape F k) :=
  Fintype.ofFinite _

def Separated (F : List (Letter D)) (k : ℕ) :=
  Σ s : PairShape F k, Paired s.between × Paired (s.before++s.after)

instance separatedFintype (F : List (Letter D)) (k : ℕ) : Fintype (Separated F k) :=
  inferInstanceAs (Fintype (Σ s : PairShape F k, Paired s.between × Paired (s.before++s.after)))

def shapeOfCut {F : List (Letter D)} {k : ℕ} (c : CutAt F k) : PairShape F k where
  before := c.val.outside.word.take c.val.start
  between := c.val.inside.word
  after := c.val.outside.word.drop c.val.start
  closing := c.val.closing
  word_eq := c.property.2.2.symm.trans (insert_word _ _ _ c.property.1)
  mark_eq := by
    simp only [List.length_take,word_length,Nat.min_eq_left c.property.1]
    exact c.property.2.1

end Diagram
end SKGap.Noncrossing
end
end

end OAI
