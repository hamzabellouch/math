import OAI.Probability.DilutedSpin.MarkerJointHistory

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n : ℕ}

noncomputable def stemLeafEquiv (A : PrescribedTree n) (r : ℕ) : A.Leaf ≃ (stem A r).Leaf :=
  Equiv.ofBijective (stemLeaf A r) (stemLeaf_bijective A r)

@[simp] lemma stemLeafEquiv_apply (A : PrescribedTree n) (r : ℕ) (a : A.Leaf) :
    stemLeafEquiv A r a=stemLeaf A r a := rfl

def unaryLeafEquiv (A : PrescribedTree n) : A.Leaf ≃ (unary A).Leaf where
  toFun a := ⟨0,a⟩
  invFun a := a.2
  left_inv _ := rfl
  right_inv a := by rcases a with ⟨i,a⟩; have hi := Fin.eq_zero i; subst i; rfl

def markerFork (A : PrescribedTree n) : PrescribedTree (n+1) :=
  .node 2 (fun i : Fin 2 => Fin.cases (motive := fun _ => PrescribedTree n) (single n) (fun _ : Fin 1 => A) i)

def markerLeaf (A : PrescribedTree n) : Option A.Leaf → (markerFork A).Leaf
  | none => ⟨0,singleLeaf n⟩
  | some a => ⟨1,a⟩

lemma markerLeaf_bijective (A : PrescribedTree n) : Function.Bijective (markerLeaf A) := by
  constructor
  · intro x y h
    cases x with
    | none => cases y with
      | none => rfl
      | some b => have hh := congrArg Sigma.fst h; norm_num [markerLeaf] at hh
    | some a => cases y with
      | none => have hh := congrArg Sigma.fst h; norm_num [markerLeaf] at hh
      | some b => exact congrArg some ((Sigma.mk.inj h).2.eq)
  · rintro ⟨i,b⟩
    fin_cases i
    · have hb := leaf_single_unique n b
      subst b
      exact ⟨none,rfl⟩
    · exact ⟨some b,rfl⟩

def doubledLeaf (A : PrescribedTree n) : A.Leaf ⊕ A.Leaf → (doubled A).Leaf
  | .inl a => ⟨0,a⟩
  | .inr a => ⟨1,a⟩

lemma doubledLeaf_bijective (A : PrescribedTree n) : Function.Bijective (doubledLeaf A) := by
  constructor
  · intro x y h
    cases x with
    | inl a => cases y with
      | inl b => exact congrArg Sum.inl ((Sigma.mk.inj h).2.eq)
      | inr b => have hh := congrArg Sigma.fst h; norm_num [markerLeaf,doubledLeaf] at hh
    | inr a => cases y with
      | inl b => have hh := congrArg Sigma.fst h; norm_num [markerLeaf,doubledLeaf] at hh
      | inr b => exact congrArg Sum.inr ((Sigma.mk.inj h).2.eq)
  · rintro ⟨i,b⟩
    fin_cases i
    · exact ⟨Sum.inl b,rfl⟩
    · exact ⟨Sum.inr b,rfl⟩

noncomputable def markerOldIndex (A : PrescribedTree n) (r : ℕ) :
    (stem (unary A) r).Leaf ≃ A.Leaf :=
  (stemLeafEquiv (unary A) r).symm.trans (unaryLeafEquiv A).symm

noncomputable def markerOld (A : PrescribedTree n) (r : ℕ)
    (a : (stem (unary A) r).Leaf) : (stem (doubled A) r).Leaf :=
  stemLeaf (doubled A) r ⟨0,markerOldIndex A r a⟩

def markerFresh (A : PrescribedTree n) (r : ℕ) (a : A.Leaf) :
    (stem (doubled A) r).Leaf := stemLeaf (doubled A) r ⟨1,a⟩

def markerTarget (A : PrescribedTree n) (r : ℕ) : Option A.Leaf → (stem (markerFork A) r).Leaf :=
  stemLeaf (markerFork A) r ∘ markerLeaf A

lemma markerTarget_bijective (A : PrescribedTree n) (r : ℕ) :
    Function.Bijective (markerTarget A r) :=
  (stemLeaf_bijective _ r).comp (markerLeaf_bijective A)

lemma markerJoint_bijective (A : PrescribedTree n) (r : ℕ) :
    Function.Bijective (Sum.elim (markerOld A r) (markerFresh A r)) := by
  have h := (stemLeaf_bijective (doubled A) r).comp ((doubledLeaf_bijective A).comp
    (Equiv.sumCongr (markerOldIndex A r) (Equiv.refl A.Leaf)).bijective)
  convert h using 1
  funext x
  cases x <;> rfl

lemma split_unary (A : PrescribedTree n) (a b : A.Leaf) :
    splitDepth (unary A) (unaryLeafEquiv A a) (unaryLeafEquiv A b)=1+splitDepth A a b :=
  @splitDepth_same_child n (1:ℕ+) (fun _ : Fin 1 => A) 0 a b

lemma split_doubled_same (A : PrescribedTree n) (a b : A.Leaf) (i : Fin 2) :
    splitDepth (doubled A) ⟨i,a⟩ ⟨i,b⟩=1+splitDepth A a b :=
  @splitDepth_same_child n (2:ℕ+) (fun _ : Fin 2 => A) i a b

lemma split_doubled_diff (A : PrescribedTree n) (a b : A.Leaf) (i j : Fin 2) (h : i ≠ j) :
    splitDepth (doubled A) ⟨i,a⟩ ⟨j,b⟩=0 :=
  @splitDepth_diff_child n (2:ℕ+) (fun _ : Fin 2 => A) i j h a b

lemma split_marker_none_some (A : PrescribedTree n) (b : A.Leaf) :
    splitDepth (markerFork A) (markerLeaf A none) (markerLeaf A (some b))=0 :=
  @splitDepth_diff_child n (2:ℕ+) (fun i : Fin 2 => Fin.cases (motive := fun _ => PrescribedTree n) (single n) (fun _ : Fin 1 => A) i) 0 1 (by decide) _ _

lemma split_marker_some_none (A : PrescribedTree n) (b : A.Leaf) :
    splitDepth (markerFork A) (markerLeaf A (some b)) (markerLeaf A none)=0 :=
  @splitDepth_diff_child n (2:ℕ+) (fun i : Fin 2 => Fin.cases (motive := fun _ => PrescribedTree n) (single n) (fun _ : Fin 1 => A) i) 1 0 (by decide) _ _

lemma split_marker_some_some (A : PrescribedTree n) (b c : A.Leaf) :
    splitDepth (markerFork A) (markerLeaf A (some b)) (markerLeaf A (some c))=1+splitDepth A b c :=
  @splitDepth_same_child n (2:ℕ+) (fun i : Fin 2 => Fin.cases (motive := fun _ => PrescribedTree n) (single n) (fun _ : Fin 1 => A) i) 1 b c

lemma markerOldIndex_stem (A : PrescribedTree n) (r : ℕ) (c : A.Leaf) :
    markerOldIndex A r (stemLeaf (unary A) r (unaryLeafEquiv A c))=c := by
  exact congrArg (unaryLeafEquiv A).symm
    ((stemLeafEquiv (unary A) r).symm_apply_apply (unaryLeafEquiv A c))

lemma markerOld_split (A : PrescribedTree n) (r : ℕ) (a b : (stem (unary A) r).Leaf) :
    splitDepth (stem (unary A) r) a b=
      splitDepth (stem (doubled A) r) (markerOld A r a) (markerOld A r b) := by
  obtain ⟨a,rfl⟩ := ((unaryLeafEquiv A).trans (stemLeafEquiv (unary A) r)).surjective a
  obtain ⟨b,rfl⟩ := ((unaryLeafEquiv A).trans (stemLeafEquiv (unary A) r)).surjective b
  have hS := splitDepth_stem (unary A) r (unaryLeafEquiv A a) (unaryLeafEquiv A b)
  have hQ := splitDepth_stem (doubled A) r
    ⟨0,markerOldIndex A r (stemLeaf (unary A) r (unaryLeafEquiv A a))⟩
    ⟨0,markerOldIndex A r (stemLeaf (unary A) r (unaryLeafEquiv A b))⟩
  have heq : splitDepth (unary A) (unaryLeafEquiv A a) (unaryLeafEquiv A b)=
      splitDepth (doubled A)
        ⟨0,markerOldIndex A r (stemLeaf (unary A) r (unaryLeafEquiv A a))⟩
        ⟨0,markerOldIndex A r (stemLeaf (unary A) r (unaryLeafEquiv A b))⟩ := by
    exact (split_unary A a b).trans ((congrArg (fun x => 1+x)
      (congrArg₂ (splitDepth A) (markerOldIndex_stem A r a).symm
        (markerOldIndex_stem A r b).symm)).trans
        (split_doubled_same A _ _ 0).symm)
  exact hS.trans ((congrArg (fun x => x+r) heq).trans hQ.symm)

lemma markerTarget_split (A : PrescribedTree n) (r : ℕ) (a : (stem (unary A) r).Leaf)
    (x y : Option A.Leaf) :
    splitDepth (stem (markerFork A) r) (markerTarget A r x) (markerTarget A r y)=
      splitDepth (stem (doubled A) r)
        (Option.elim' (markerOld A r a) (markerFresh A r) x)
        (Option.elim' (markerOld A r a) (markerFresh A r) y) := by
  have hT := splitDepth_stem (markerFork A) r (markerLeaf A x) (markerLeaf A y)
  cases x with
  | none => cases y with
    | none => simp only [Option.elim',splitDepth_self]
    | some b =>
      have hQ := splitDepth_stem (doubled A) r ⟨0,markerOldIndex A r a⟩ ⟨1,b⟩
      have ht := split_marker_none_some A b
      have hq := split_doubled_diff A (markerOldIndex A r a) b 0 1 (by decide)
      exact hT.trans ((congrArg (fun x => x+r) (ht.trans hq.symm)).trans hQ.symm)
  | some b => cases y with
    | none =>
      have hQ := splitDepth_stem (doubled A) r ⟨1,b⟩ ⟨0,markerOldIndex A r a⟩
      have ht := split_marker_some_none A b
      have hq := split_doubled_diff A b (markerOldIndex A r a) 1 0 (by decide)
      exact hT.trans ((congrArg (fun x => x+r) (ht.trans hq.symm)).trans hQ.symm)
    | some c =>
      have hQ := splitDepth_stem (doubled A) r ⟨1,b⟩ ⟨1,c⟩
      have ht := split_marker_some_some A b c
      have hq := split_doubled_same A b c 1
      exact hT.trans ((congrArg (fun x => x+r) (ht.trans hq.symm)).trans hQ.symm)

lemma marker_split_separation (A : PrescribedTree n) (r : ℕ)
    (a d : (stem (unary A) r).Leaf) (c : A.Leaf) :
    splitDepth (stem (doubled A) r) (markerFresh A r c) (markerOld A r a) <
      splitDepth (stem (doubled A) r) (markerOld A r a) (markerOld A r d) := by
  have hL := splitDepth_stem (doubled A) r ⟨1,c⟩ ⟨0,markerOldIndex A r a⟩
  have hR := splitDepth_stem (doubled A) r ⟨0,markerOldIndex A r a⟩ ⟨0,markerOldIndex A r d⟩
  have hl := split_doubled_diff A c (markerOldIndex A r a) 1 0 (by decide)
  have hr := split_doubled_same A (markerOldIndex A r a) (markerOldIndex A r d) 0
  have hL' := hL.trans (congrArg (fun x => x+r) hl)
  have hR' := hR.trans (congrArg (fun x => x+r) hr)
  have hh : 0+r < (1+splitDepth A (markerOldIndex A r a) (markerOldIndex A r d))+r := by omega
  exact lt_of_eq_of_lt hL' (lt_of_lt_of_eq hh hR'.symm)

end DilutedSpinGlass.PrescribedTree

end

end OAI
