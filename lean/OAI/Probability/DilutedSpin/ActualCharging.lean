import OAI.Probability.DilutedSpin.HistoryGeometry

namespace OAI

section
section
namespace DilutedSpinGlass.MarkSelector
open scoped BigOperators

/-- Each mark coordinate is a genuine independent fair Rademacher variable. -/
noncomputable def rademacher : FiniteLaw Bool where
  weight _ := 1 / 2
  nonneg _ := by norm_num
  total := by rw [Fintype.sum_bool]; norm_num

def sign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem sign_sq (b : Bool) : sign b * sign b = 1 := by cases b <;> norm_num [sign]
@[simp] theorem abs_sign (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]
@[simp] theorem mean_sign : rademacher.expect sign = 0 := by
  rw [FiniteLaw.expect,Fintype.sum_bool]
  norm_num [rademacher,sign]

/-- Independent vertex marks select sharing of the vertex, not equality of spins. -/
theorem pair_selector {V : Type*} [Fintype V] [DecidableEq V] (a b : V) :
    (FiniteLaw.pi (fun _ : V => rademacher)).expect
      (fun x => sign (x a) * sign (x b)) = if a = b then 1 else 0 := by
  by_cases hab : a = b
  · subst b
    simp only [sign_sq,FiniteLaw.expect_const,ite_true]
  · rw [ite_eq_right hab]
    let f (v : V) (x : Bool) : ℝ :=
      (if v = a then sign x else 1) * (if v = b then sign x else 1)
    have he (x : V → Bool) : (∏ v, f v (x v)) = sign (x a) * sign (x b) := by
      simp only [f,Finset.prod_mul_distrib,Finset.prod_ite_eq',Finset.mem_univ,ite_true]
    simp_rw [← he]
    rw [FiniteLaw.expect_pi_product]
    apply Finset.prod_eq_zero (i := a) (Finset.mem_univ _)
    simp only [f,ite_true,ite_eq_right hab,mul_one,mean_sign]

/-- Different requested color pairs use separate independent coordinates. -/
theorem requirements_selector {R V : Type*} [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V] (a b : R → V) :
    (FiniteLaw.pi (fun _ : R => FiniteLaw.pi (fun _ : V => rademacher))).expect
      (fun x => ∏ r, sign (x r (a r)) * sign (x r (b r))) =
      ∏ r, if a r = b r then (1 : ℝ) else 0 := by
  calc
    _ = ∏ r, (FiniteLaw.pi (fun _ : V => rademacher)).expect
        (fun y => sign (y (a r)) * sign (y (b r))) :=
      FiniteLaw.expect_pi_product (α := fun _ : R => V → Bool)
        (fun _ : R => FiniteLaw.pi (fun _ : V => rademacher))
        (fun (r : R) (y : V → Bool) => sign (y (a r)) * sign (y (b r)))
    _ = _ := Finset.prod_congr rfl (fun r _ => pair_selector (a r) (b r))

/-- Factor assigned to one color from a pair requirement. Pair endpoints are
assumed distinct colors, as stipulated in the canceled-anchor expansion. -/
noncomputable def colorMark {C R V : Type*} [Fintype R] [DecidableEq C]
    (a b : R → C) (pos : C → V) (x : R → V → Bool) (c : C) : ℝ :=
  ∏ r, (if c = a r then sign (x r (pos c)) else 1) *
    (if c = b r then sign (x r (pos c)) else 1)

theorem colorMark_abs {C R V : Type*} [Fintype R] [DecidableEq C]
    (a b : R → C) (pos : C → V) (x : R → V → Bool) (c : C) :
    |colorMark a b pos x c| = 1 := by
  unfold colorMark
  rw [Finset.abs_prod]
  apply Finset.prod_eq_one
  intro r _
  rw [abs_mul]
  split_ifs <;> simp only [abs_sign,abs_one,mul_one]

/-- Regrouping the factors assigned to colors gives precisely the selector. -/
theorem colored_selector {C R V : Type*} [Fintype C] [DecidableEq C]
    [Fintype R] [DecidableEq R] [Fintype V] [DecidableEq V]
    (a b : R → C) (pos : C → V) :
    (FiniteLaw.pi (fun _ : R => FiniteLaw.pi (fun _ : V => rademacher))).expect
      (fun x => ∏ c, colorMark a b pos x c) =
      ∏ r, if pos (a r) = pos (b r) then (1 : ℝ) else 0 := by
  have he (x : R → V → Bool) : (∏ c, colorMark a b pos x c) =
      ∏ r, sign (x r (pos (a r))) * sign (x r (pos (b r))) := by
    simp only [colorMark]
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro r _
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_ite_eq',Finset.mem_univ,ite_true]
  simp_rw [he]
  exact requirements_selector (fun r => pos (a r)) (fun r => pos (b r))

end DilutedSpinGlass.MarkSelector

namespace DilutedSpinGlass.PrescribedTree
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p
noncomputable local instance {n : ℕ} (S : PrescribedTree n) : DecidableEq (Leaf S) := Classical.decEq _

/-- The actual depth-d vertex is represented by its set of descendant leaf
positions. Depths range from the root through the terminal leaf positions. -/
noncomputable def cluster {n : ℕ} (S : PrescribedTree n) (d : ℕ) (a : Leaf S) :
    Finset (Leaf S) := Finset.univ.filter (fun b => d ≤ splitDepth S a b)

@[simp] theorem mem_cluster {n : ℕ} (S : PrescribedTree n) (d : ℕ) (a b : Leaf S) :
    b ∈ cluster S d a ↔ d ≤ splitDepth S a b := by simp [cluster]

/-- Equality of depth vertices is exactly sharing of the prefix. -/
theorem cluster_eq_iff {n : ℕ} (S : PrescribedTree n) {d : ℕ} (hd : d ≤ n)
    (a b : Leaf S) : cluster S d a = cluster S d b ↔ d ≤ splitDepth S a b := by
  constructor
  · intro h
    have hb : b ∈ cluster S d b := by rw [mem_cluster,splitDepth_self]; exact hd
    rw [← h,mem_cluster] at hb
    exact hb
  · intro h
    ext c
    simp only [mem_cluster]
    constructor
    · intro hc
      have ht := splitDepth_ultrametric S b a c
      rw [splitDepth_symm S b a] at ht
      exact (le_min h hc).trans ht
    · intro hc
      exact (le_min h hc).trans (splitDepth_ultrametric S a b c)

/-- The marker projector in pert:mark-selector on actual tree positions. -/
theorem tree_mark_selector {n : ℕ} (S : PrescribedTree n) {C R : Type*}
    [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
    (a b : R → C) (pos : C → Leaf S) (d : R → ℕ) (hd : ∀ r, d r ≤ n) :
    (FiniteLaw.pi (fun _ : R => FiniteLaw.pi
      (fun _ : Finset (Leaf S) => MarkSelector.rademacher))).expect
      (fun x => ∏ r, MarkSelector.sign (x r (cluster S (d r) (pos (a r)))) *
        MarkSelector.sign (x r (cluster S (d r) (pos (b r))))) =
      ∏ r, if d r ≤ splitDepth S (pos (a r)) (pos (b r)) then (1 : ℝ) else 0 := by
  rw [MarkSelector.requirements_selector]
  apply Finset.prod_congr rfl
  intro r _
  simp only [cluster_eq_iff S (hd r)]

/-- Exact splitting is the difference of consecutive sharing projectors. -/
theorem exact_split_selector {n : ℕ} (S : PrescribedTree n) (a b : Leaf S) (d : ℕ) :
    (if d ≤ splitDepth S a b then (1 : ℝ) else 0) -
      (if d+1 ≤ splitDepth S a b then 1 else 0) =
      if splitDepth S a b = d then 1 else 0 := by
  split_ifs <;> norm_num <;> omega

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance (priority := 2000) {n : ℕ} (S : PrescribedTree n) : DecidableEq (Leaf S) := Classical.decEq _
noncomputable local instance (priority := 2000) {α : Type*} (β : α → Type*) : DecidableEq (Sigma β) := Classical.decEq _

/-- The local product of reference factors for k represented children. The
empty and unary induced vertices contribute no factor. -/
noncomputable def branchProduct (x y : ℝ) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range (k-1), (x-((j:ℝ)+1)*y)

@[simp] theorem branchProduct_zero (x y : ℝ) : branchProduct x y 0 = 1 := by
  classical
  simp [branchProduct]
@[simp] theorem branchProduct_one (x y : ℝ) : branchProduct x y 1 = 1 := by
  classical
  simp [branchProduct]

theorem branchProduct_succ (x y : ℝ) {k : ℕ} (hk : 0 < k) :
    branchProduct x y (k+1) = branchProduct x y k * (x-(k:ℝ)*y) := by
  classical
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  simp [branchProduct, Finset.prod_range_succ, Nat.cast_add, Nat.cast_one]

 
noncomputable def partialKappa : {n : ℕ} → (S : PrescribedTree n) →
    (Fin (n+1) → ℝ) → Finset (Leaf S) → ℝ
  | 0, .leaf, _, _ => 1
  | _+1, .node _ C, m, R =>
      branchProduct (m 0) (m 1) (R.image (fun a => a.1)).card *
        ∏ i, partialKappa (C i) (fun j => m j.succ) (childRefs R i)

@[simp] theorem childRefs_empty {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (i : Fin k) : childRefs (∅ : Finset (Leaf (.node k C))) i = ∅ := by
  classical
  ext a
  rw [mem_childRefs]
  exact iff_of_false (Finset.notMem_empty _) (Finset.notMem_empty _)

@[simp] theorem childRefs_insert_same {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (R : Finset (Leaf (.node k C))) (i : Fin k) (a : Leaf (C i)) :
    childRefs (insert (⟨i,a⟩ : Leaf (.node k C)) R) i = insert a (childRefs R i) := by
  classical
  ext b
  constructor
  · intro h
    have hh := (mem_childRefs _ i b).mp h
    rcases (Finset.mem_insert.mp hh) with hab | hb
    · exact Finset.mem_insert.mpr (Or.inl (eq_of_heq ((Sigma.mk.inj_iff.mp hab).2)))
    · exact Finset.mem_insert.mpr (Or.inr ((mem_childRefs R i b).mpr hb))
  · intro h
    apply (mem_childRefs _ i b).mpr
    rcases Finset.mem_insert.mp h with hab | hb
    · subst b
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem ((mem_childRefs R i b).mp hb)

theorem childRefs_insert_other {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (R : Finset (Leaf (.node k C))) (i j : Fin k) (hij : j ≠ i) (a : Leaf (C i)) :
    childRefs (insert (⟨i,a⟩ : Leaf (.node k C)) R) j = childRefs R j := by
  classical
  ext b
  constructor
  · intro h
    have hh := (mem_childRefs _ j b).mp h
    rcases Finset.mem_insert.mp hh with hab | hb
    · exact (hij (congrArg Sigma.fst hab)).elim
    · exact (mem_childRefs R j b).mpr hb
  · intro h
    apply (mem_childRefs _ j b).mpr
    exact Finset.mem_insert_of_mem ((mem_childRefs R j b).mp h)

@[simp] theorem childRefs_singleton_same {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (i : Fin k) (a : Leaf (C i)) :
    childRefs (C := C) ({⟨i,a⟩} : Finset (Leaf (.node k C))) i = {a} := by
  classical
  ext b
  constructor
  · intro h
    have hh := Finset.mem_singleton.mp ((mem_childRefs _ i b).mp h)
    exact Finset.mem_singleton.mpr (eq_of_heq ((Sigma.mk.inj_iff.mp hh).2))
  · intro h
    have hb := Finset.mem_singleton.mp h
    subst b
    exact (mem_childRefs _ i a).mpr (Finset.mem_singleton_self _)

theorem childRefs_singleton_other {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (i j : Fin k) (hij : j ≠ i) (a : Leaf (C i)) :
    childRefs (C := C) ({⟨i,a⟩} : Finset (Leaf (.node k C))) j = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hh := Finset.mem_singleton.mp ((mem_childRefs _ j b).mp hb)
  exact hij (congrArg Sigma.fst hh)

@[simp] theorem partialKappa_empty {n : ℕ} (S : PrescribedTree n)
    (m : Fin (n+1) → ℝ) : partialKappa S m ∅ = 1 := by
  classical
  induction S with
  | leaf => rfl
  | @node n k C ih => simp [partialKappa,ih]

@[simp] theorem partialKappa_singleton {n : ℕ} (S : PrescribedTree n)
    (m : Fin (n+1) → ℝ) (a : Leaf S) : partialKappa S m {a} = 1 := by
  classical
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    obtain ⟨i,a⟩ := a
    change branchProduct (m 0) (m 1) (Finset.image (fun a : Sigma (fun j => Leaf (C j)) => a.1) {⟨i,a⟩}).card * _ = 1
    rw [Finset.image_singleton,Finset.card_singleton,branchProduct_one,one_mul]
    apply Finset.prod_eq_one
    intro j _
    by_cases hji : j = i
    · subst j
      rw [childRefs_singleton_same]
      exact ih i (fun j => m j.succ) a
    · rw [childRefs_singleton_other i j hji,partialKappa_empty]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance (priority := 2000) {n : ℕ} (S : PrescribedTree n) : DecidableEq (Leaf S) := Classical.decEq _
noncomputable local instance (priority := 2000) {α : Type*} (β : α → Type*) : DecidableEq (Sigma β) := Classical.decEq _

private theorem prod_local_factor {α : Type*} [Fintype α] (f g : α → ℝ) (i : α) (c : ℝ)
    (hi : f i = c*g i) (ho : ∀ j, j ≠ i → f j = g j) :
    (∏ j, f j) = c*∏ j, g j := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),hi]
  have he : (∏ j ∈ Finset.univ.erase i, f j) = ∏ j ∈ Finset.univ.erase i, g j :=
    Finset.prod_congr rfl (fun j hj => ho j (Finset.mem_erase.mp hj).1)
  rw [he,mul_assoc]

private theorem childRefs_eq_empty_of_unoccupied {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (R : Finset (Leaf (.node k C))) (i : Fin k) (hi : i ∉ R.image (fun a => a.1)) :
    childRefs R i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact hi (Finset.mem_image.mpr ⟨⟨i,a⟩,(mem_childRefs R i a).mp ha,rfl⟩)

 
theorem partialKappa_insert {n : ℕ} (S : PrescribedTree n)
    (m : Fin (n+1) → ℝ) (R : Finset (Leaf S)) (a b : Leaf S)
    (ha : a ∈ R) (hb : b ∉ R)
    (hmax : ∀ r ∈ R, splitDepth S b r ≤ splitDepth S b a) :
    partialKappa S m (insert b R) =
      (referenceDivergence S a (splitDepth S b a)
        (splitDepth_lt_of_ne S b a (fun h => hb (h ▸ ha))) R).coefficient m *
        partialKappa S m R := by
  classical
  induction S with
  | leaf =>
    have he : a = b := @Subsingleton.elim Unit (inferInstanceAs (Subsingleton Unit)) a b
    exact (hb (he ▸ ha)).elim
  | @node n k C ih =>
    obtain ⟨i,a⟩ := a
    obtain ⟨j,b⟩ := b
    by_cases hji : j = i
    · subst j
      have hai : a ∈ childRefs R i := (mem_childRefs R i a).mpr ha
      have hbi : b ∉ childRefs R i := fun h => hb ((mem_childRefs R i b).mp h)
      have hmi : ∀ r ∈ childRefs R i, splitDepth (C i) b r ≤ splitDepth (C i) b a := by
        intro r hr
        have hh := hmax ⟨i,r⟩ ((mem_childRefs R i r).mp hr)
        rw [splitDepth_same_child,splitDepth_same_child] at hh
        omega
      have hei : i ∈ R.image (fun r => r.1) := Finset.mem_image.mpr ⟨⟨i,a⟩,ha,rfl⟩
      have hroot : (insert (⟨i,b⟩ : Leaf (.node k C)) R).image (fun r => r.1) =
          R.image (fun r => r.1) := by
        erw [Finset.image_insert]
        exact Finset.insert_eq_of_mem hei
      let c := (referenceDivergence (C i) a (splitDepth (C i) b a)
        (splitDepth_lt_of_ne _ b a (fun h => hbi (h ▸ hai))) (childRefs R i)).coefficient
          (fun z => m z.succ)
      have hprod : (∏ t, partialKappa (C t) (fun z => m z.succ)
          (childRefs (insert (⟨i,b⟩ : Leaf (.node k C)) R) t)) =
          c*∏ t, partialKappa (C t) (fun z => m z.succ) (childRefs R t) := by
        apply prod_local_factor _ _ i c
        · rw [childRefs_insert_same]
          exact ih i (fun z => m z.succ) (childRefs R i) a b hai hbi hmi
        · intro t hti
          rw [childRefs_insert_other R i t hti]
      change branchProduct (m 0) (m 1) ((insert (⟨i,b⟩ : Leaf (.node k C)) R).image
        (fun r => r.1)).card * _ = _
      erw [hroot,hprod]
      simp only [splitDepth_same_child,Nat.add_comm 1]
      change branchProduct (m 0) (m 1) (R.image (fun r => r.1)).card * (c*_) =
        c*(branchProduct (m 0) (m 1) (R.image (fun r => r.1)).card * _)
      ring
    · have hz : splitDepth (.node k C) (⟨j,b⟩ : Leaf (.node k C)) ⟨i,a⟩ = 0 :=
        splitDepth_diff_child C j i hji b a
      have hj : j ∉ R.image (fun r => r.1) := by
        intro h
        obtain ⟨⟨t,r⟩,hr,ht⟩ := Finset.mem_image.mp h
        change t = j at ht
        subst t
        have hh := hmax ⟨j,r⟩ hr
        rw [hz,splitDepth_same_child] at hh
        omega
      have hchild := childRefs_eq_empty_of_unoccupied R j hj
      have hcard : 0 < (R.image (fun r => r.1)).card :=
        Finset.card_pos.mpr ⟨i,Finset.mem_image.mpr ⟨⟨i,a⟩,ha,rfl⟩⟩
      have hroot : ((insert (⟨j,b⟩ : Leaf (.node k C)) R).image (fun r => r.1)).card =
          (R.image (fun r => r.1)).card+1 := by
        erw [Finset.image_insert,Finset.card_insert_of_notMem hj]
      have hprod : (∏ t, partialKappa (C t) (fun z => m z.succ)
          (childRefs (insert (⟨j,b⟩ : Leaf (.node k C)) R) t)) =
          ∏ t, partialKappa (C t) (fun z => m z.succ) (childRefs R t) := by
        apply Finset.prod_congr rfl
        intro t _
        by_cases ht : t = j
        · subst t
          rw [childRefs_insert_same,hchild,Finset.insert_empty,partialKappa_singleton,
            partialKappa_empty]
        · rw [childRefs_insert_other R j t ht]
      change branchProduct (m 0) (m 1) ((insert (⟨j,b⟩ : Leaf (.node k C)) R).image
        (fun r => r.1)).card * _ = _
      erw [hroot,hprod,branchProduct_succ _ _ hcard]
      simp only [hz]
      change (_ * (m 0-((R.image (fun r => r.1)).card : ℝ)*m 1))*_ =
        (m 0-((R.image (fun r => r.1)).card : ℝ)*m 1)*(_*_)
      ring

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance (priority := 2000) {n : ℕ} (S : PrescribedTree n) : DecidableEq (Leaf S) := Classical.decEq _
noncomputable local instance (priority := 2000) {α : Type*} (β : α → Type*) : DecidableEq (Sigma β) := Classical.decEq _

/-- The actual final set of leaf positions in a finite reference prescription. -/
noncomputable def referencePlanRefs {n : ℕ} (T : PrescribedTree n) :
    {p : ℕ} → {s : Fin (p+1) → Leaf T} → ReferencePlan T s → Finset (Leaf T)
  | _, s, .nil => Finset.univ.image s
  | _, _, .cons _ _ _ _ next => referencePlanRefs T next

@[simp] theorem image_cons_refs {n p : ℕ} (T : PrescribedTree n)
    (s : Fin (p+1) → Leaf T) (b : Leaf T) :
    Finset.univ.image (Fin.cons b s) = insert b (Finset.univ.image s) := by
  classical
  ext a
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_insert]
  constructor
  · rintro ⟨i,hi⟩
    refine Fin.cases ?_ (fun j => ?_) i hi
    · intro h
      exact Or.inl h.symm
    · intro h
      exact Or.inr ⟨j,h⟩
  · rintro (rfl | ⟨i,hi⟩)
    · exact ⟨0,rfl⟩
    · exact ⟨i.succ,hi⟩

/-- The history's reference normalization is the unordered branching-vertex
product, independently of the order in which the colors were added. -/
theorem partialKappa_referencePlan {n p : ℕ} (T : PrescribedTree n)
    (m : Fin (n+1) → ℝ) {s : Fin (p+1) → Leaf T} (P : ReferencePlan T s) :
    partialKappa T m (referencePlanRefs T P) =
      referencePlanNormalizer T m P * partialKappa T m (Finset.univ.image s) := by
  classical
  induction P with
  | nil => simp [referencePlanRefs,referencePlanNormalizer]
  | @cons p s b a hf hd next ih =>
    rw [referencePlanRefs,ih,image_cons_refs]
    have ha : s a ∈ Finset.univ.image s := Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
    have hb : b ∉ Finset.univ.image s := by
      rintro hb
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hb
      exact hf i hi.symm
    have hm : ∀ r ∈ Finset.univ.image s, splitDepth T b r ≤ splitDepth T b (s a) := by
      intro r hr
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hr
      exact hd i
    rw [partialKappa_insert T m _ (s a) b ha hb hm]
    change _ = (_ * referencePlanNormalizer T m next) * _
    ring

 
theorem reference_history_kappa {n : ℕ} (T : PrescribedTree n)
    (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1)
    (a : Leaf T) (P : ReferencePlan T (fun _ : Fin 1 => a))
    (hP : referencePlanRefs T P = Finset.univ)
    (S : PrescribedTree n) (r : Fin 1 → Leaf S) :
    referenceHistoryTotal T m P S r = partialKappa T m Finset.univ := by
  classical
  have he : ∀ i j, splitDepth S (r i) (r j) = splitDepth T a a := by
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    rw [splitDepth_self,splitDepth_self]
  rw [reference_history_total T m hend P S r he]
  have h := partialKappa_referencePlan T m P
  rw [hP] at h
  have hi : Finset.univ.image (fun _ : Fin 1 => a) = {a} := by simp
  rw [hi,partialKappa_singleton,mul_one] at h
  exact h.symm

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Depth and arity refer to the genuine internal vertices, not their sampled values. -/
def vertexDepth : {n : ℕ} → (S : PrescribedTree n) → Internal S → ℕ
  | 0, .leaf, v => nomatch v
  | _+1, .node _ C, v =>
    match (v : Option ((i : _) × Internal (C i))) with
    | none => 0
    | some ⟨i,v⟩ => vertexDepth (C i) v + 1

def vertexArity : {n : ℕ} → (S : PrescribedTree n) → Internal S → ℕ
  | 0, .leaf, v => nomatch v
  | _+1, .node k C, v =>
    match (v : Option ((i : _) × Internal (C i))) with
    | none => k
    | some ⟨i,v⟩ => vertexArity (C i) v

noncomputable def branchingCount : {n : ℕ} → PrescribedTree n → (ℕ → Prop) → ℕ
  | 0, .leaf, _ => 0
  | _+1, .node k C, P => by
      classical
      exact (if P 0 ∧ 1 < (k:ℕ) then 1 else 0) +
        ∑ i, branchingCount (C i) (fun d => P (d+1))

-- Predicates in the count are decidable by classical logic, not extra model data.

@[simp] theorem leaves_single (n : ℕ) : leaves (single n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (∑ _i : Fin (1:ℕ+), leaves (single n)) = 1
    simp only [ih, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rfl

theorem leaves_pos {n : ℕ} (S : PrescribedTree n) : 0 < leaves S := by
  induction S with
  | leaf => decide
  | @node n k C ih =>
    exact Finset.sum_pos (fun i _ => ih i) Finset.univ_nonempty

@[simp] theorem branchingCount_single (n : ℕ) (P : ℕ → Prop) :
    branchingCount (single n) P = 0 := by
  classical
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    change (if P 0 ∧ 1 < (1:ℕ) then 1 else 0) +
      (∑ _i : Fin (1:ℕ+), branchingCount (single n) (fun d => P (d+1))) = 0
    simp [ih]

/-- One fresh growth creates at most one branching vertex; new continuations
are unary. This holds even at coincident depths elsewhere in the tree. -/
theorem branchingCount_grow {n : ℕ} (S : PrescribedTree n) (v : Internal S)
    (P : ℕ → Prop) :
    branchingCount (grow S v) P = branchingCount S P +
      (if P (vertexDepth S v) ∧ vertexArity S v = 1 then 1 else 0) := by
  classical
  induction S generalizing P with
  | leaf => nomatch v
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      change (if P 0 ∧ 1 < (k:ℕ)+1 then 1 else 0) +
        (∑ j : Fin ((k:ℕ)+1), branchingCount (Fin.cases (single n) C j) (fun d => P (d+1))) =
        ((if P 0 ∧ 1 < (k:ℕ) then 1 else 0) +
          ∑ j : Fin k, branchingCount (C j) (fun d => P (d+1))) +
            (if P 0 ∧ (k:ℕ)=1 then 1 else 0)
      rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ, branchingCount_single, zero_add]
      have hk : 0 < (k:ℕ) := k.property
      by_cases hP : P 0 <;> by_cases hk1 : (k:ℕ) = 1 <;>
        simp [hP, hk1, show ¬1 < (k:ℕ) ↔ (k:ℕ)=1 by omega, Nat.add_comm]
    | some v =>
      obtain ⟨i,v⟩ := v
      simp only [grow, branchingCount, vertexDepth, vertexArity]
      have hsum : (∑ j, branchingCount (Function.update C i (grow (C i) v) j)
          (fun d => P (d+1))) =
          (∑ j, branchingCount (C j) (fun d => P (d+1))) +
            (if P (vertexDepth (C i) v + 1) ∧ vertexArity (C i) v = 1 then 1 else 0) := by
        calc
          _ = ∑ j, (branchingCount (C j) (fun d => P (d+1)) +
                if j = i then
                  (if P (vertexDepth (C i) v + 1) ∧ vertexArity (C i) v = 1 then 1 else 0)
                else 0) := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hji : j = i
              · subst j
                simp only [Function.update_self, ite_true]
                exact ih i v (fun d => P (d+1))
              · simp [hji]
          _ = _ := by simp [Finset.sum_add_distrib]
      rw [hsum, Nat.add_assoc]

/-- Count of vertices at one depth, including unary vertices. -/
noncomputable def depthCount : {n : ℕ} → PrescribedTree n → ℕ → ℕ
  | 0, .leaf, _ => 0
  | _+1, .node _ _, 0 => 1
  | _+1, .node _ C, d+1 => ∑ i, depthCount (C i) d

theorem depthCount_le_leaves {n : ℕ} (S : PrescribedTree n) (d : ℕ) :
    depthCount S d ≤ leaves S := by
  induction S generalizing d with
  | leaf => simp [depthCount, leaves]
  | @node n k C ih =>
    cases d with
    | zero => exact leaves_pos (.node k C)
    | succ d => exact Finset.sum_le_sum (fun i _ => ih i d)

/-- Identification with the actual finite internal-vertex index type. -/
theorem depthCount_eq_sum {n : ℕ} (S : PrescribedTree n) (d : ℕ) :
    (∑ v : Internal S, if vertexDepth S v = d then (1:ℕ) else 0) = depthCount S d := by
  classical
  induction S generalizing d with
  | leaf => exact Finset.sum_eq_zero (fun v _ => nomatch v)
  | @node n k C ih =>
    change (∑ v : Option ((i : Fin k) × Internal (C i)), _) = _
    rw [Fintype.sum_option, Fintype.sum_sigma]
    cases d with
    | zero => simp [vertexDepth, depthCount]
    | succ d => simpa [vertexDepth, depthCount] using congrArg (Finset.sum Finset.univ) (funext (fun i => ih i d))

/-- Equally spaced exponents, with an arbitrary incoming depth. -/
noncomputable def grid (n d L : ℕ) : Fin (n+1) → ℝ := fun i => (d+i.val:ℕ) / (L:ℝ)

theorem gamma_grid_unary {n : ℕ} (S : PrescribedTree n) (v : Internal S)
    (d L : ℕ) (hv : vertexArity S v = 1) :
    gamma S (grid n d L) v = -(L:ℝ)⁻¹ := by
  induction S generalizing d with
  | leaf => nomatch v
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      change (k:ℕ) = 1 at hv
      simp [gamma, grid, hv, Nat.cast_add, Nat.cast_one, add_div]
    | some v =>
      obtain ⟨i,v⟩ := v
      change gamma (C i) (fun j => grid (n+1) d L j.succ) v = _
      have heq : (fun j : Fin (n+1) => grid (n+1) d L j.succ) = grid n (d+1) L := by
        funext j
        simp [grid, Fin.val_succ, Nat.add_comm, Nat.add_left_comm]
      rw [heq]
      exact ih i v (d+1) hv

/-- The sum of coefficients of unary splits at a specified depth is at most
`leaves/L`, uniformly in the total number of levels. -/
theorem unary_depth_budget {n : ℕ} (S : PrescribedTree n) (d L q : ℕ) :
    (∑ v : Internal S, if vertexDepth S v = q ∧ vertexArity S v = 1 then
      |gamma S (grid n d L) v| else 0) ≤ (leaves S:ℝ) * (L:ℝ)⁻¹ := by
  classical
  calc
    _ ≤ ∑ v : Internal S, (if vertexDepth S v = q then (1:ℝ) else 0) * (L:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : vertexDepth S v = q ∧ vertexArity S v = 1
      · rw [ite_eq_left hv, gamma_grid_unary S v d L hv.2, abs_neg,
          abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)), ite_eq_left hv.1, one_mul]
      · rw [ite_eq_right hv]
        positivity
    _ = (depthCount S q:ℝ) * (L:ℝ)⁻¹ := by
      rw [← Finset.sum_mul, ← depthCount_eq_sum S q]
      push_cast
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast depthCount_le_leaves S q)
      (inv_nonneg.mpr (Nat.cast_nonneg _))

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A charged step is precisely the first branching at a designated depth. -/
def charged {n : ℕ} (S : PrescribedTree n) (Q : Finset ℕ) (v : Internal S) : Prop :=
  vertexDepth S v ∈ Q ∧ vertexArity S v = 1

theorem unary_set_budget {n : ℕ} (S : PrescribedTree n) (d L : ℕ) (Q : Finset ℕ) :
    (∑ v : Internal S, if charged S Q v then |gamma S (grid n d L) v| else 0) ≤
      (Q.card:ℝ) * (leaves S:ℝ) * (L:ℝ)⁻¹ := by
  classical
  calc
    _ = ∑ q ∈ Q, ∑ v : Internal S,
        if vertexDepth S v = q ∧ vertexArity S v = 1 then
          |gamma S (grid n d L) v| else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      by_cases ha : vertexArity S v = 1
      · simp [charged, ha]
      · simp [charged, ha]
    _ ≤ ∑ _q ∈ Q, (leaves S:ℝ) * (L:ℝ)⁻¹ :=
      Finset.sum_le_sum (fun q _ => unary_depth_budget S d L q)
    _ = _ := by simp [mul_assoc]

theorem sum_abs_gamma_grid {L : ℕ} (hL : 0 < L) (S : PrescribedTree L) :
    (∑ v : Internal S, |gamma S (grid L 0 L) v|) = (leaves S:ℝ) := by
  apply sum_abs_gamma
  · intro i j hij
    simp only [grid, Nat.zero_add]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (Nat.cast_nonneg _)
  · intro i
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · simp [grid]
  · simp [grid, ne_of_gt hL]

/-- The absolute history sum with a terminal test. The old-leaf multiplier is
exactly the number of eligible leaves (each contributes coefficient one).
Fresh histories keep the genuine grow operation and coefficient at every step. -/
noncomputable def historyMass {L : ℕ} (F : PrescribedTree L → ℝ) :
    ℕ → (S : PrescribedTree L) → ℕ → ℝ
  | 0, S, _ => F S
  | k+1, S, a => (a:ℝ) * historyMass F k S (a-1) +
      ∑ v : Internal S, |gamma S (grid L 0 L) v| * historyMass F k (grow S v) a

/-- Histories having at least b charged steps, preserving their multiplicities. -/
noncomputable def chargeMass {L : ℕ} (Q : Finset ℕ) :
    ℕ → (S : PrescribedTree L) → ℕ → ℕ → ℝ
  | 0, _, _, b => if b = 0 then 1 else 0
  | k+1, S, a, b => (a:ℝ) * chargeMass Q k S (a-1) b +
      ∑ v : Internal S, |gamma S (grid L 0 L) v| *
        chargeMass Q k (grow S v) a (b - if charged S Q v then 1 else 0)

/-- Exact correspondence between charging steps and actual terminal branching
vertices. Distinct vertices at the same depth are counted separately. -/
theorem chargeMass_eq_historyMass {L : ℕ} (Q : Finset ℕ) (B k a : ℕ)
    (S : PrescribedTree L) :
    chargeMass Q k S a (B - branchingCount S (· ∈ Q)) =
      historyMass (fun T => if B ≤ branchingCount T (· ∈ Q) then 1 else 0) k S a := by
  classical
  induction k generalizing S a with
  | zero => simp [chargeMass, historyMass, Nat.sub_eq_zero_iff_le]
  | succ k ih =>
    simp only [chargeMass, historyMass, ih]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    congr 1
    have heq : B - branchingCount (grow S v) (· ∈ Q) =
        B - branchingCount S (· ∈ Q) - (if charged S Q v then 1 else 0) := by
      rw [branchingCount_grow, Nat.sub_add_eq]
      by_cases hh : charged S Q v
      · have h := hh
        simp only [charged] at h
        simp [h, hh]
      · have h : ¬ (vertexDepth S v ∈ Q ∧ vertexArity S v = 1) := hh
        simp [h, hh]
    rw [← heq, ih]

noncomputable def chargeBound (C D : ℝ) : ℕ → ℕ → ℝ
  | 0, b => if b = 0 then 1 else 0
  | k+1, 0 => C * chargeBound C D k 0
  | k+1, b+1 => C * chargeBound C D k (b+1) + D * chargeBound C D k b

theorem chargeBound_nonneg {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (k b : ℕ) :
    0 ≤ chargeBound C D k b := by
  induction k generalizing b with
  | zero => simp only [chargeBound]; split <;> norm_num
  | succ k ih =>
    cases b with
    | zero => exact mul_nonneg hC (ih 0)
    | succ b => exact add_nonneg (mul_nonneg hC (ih _)) (mul_nonneg hD (ih _))

/-- Every specified split contributes one factor delta; constants are independent
of the grid denominator. This also handles arbitrarily repeated target depths. -/
theorem chargeBound_scale (C D δ : ℝ) (k b : ℕ) :
    chargeBound C (D*δ) k b = chargeBound C D k b * δ^b := by
  induction k generalizing b with
  | zero =>
    cases b <;> simp [chargeBound]
  | succ k ih =>
    cases b with
    | zero => simp only [chargeBound, ih, pow_zero, mul_one]
    | succ b => simp only [chargeBound, ih, pow_succ]; ring

/-- A genuine history estimate, not a distribution postulated from the desired
identity. R bounds the leaves during all the remaining growth steps. -/
theorem chargeMass_bound {L : ℕ} (hL : 0 < L) (Q : Finset ℕ) (R k b a : ℕ)
    (S : PrescribedTree L) (ha : a ≤ leaves S) (hR : leaves S + k ≤ R) :
    chargeMass Q k S a b ≤
      chargeBound (2*(R:ℝ)) ((Q.card:ℝ)*(R:ℝ)*(L:ℝ)⁻¹) k b := by
  classical
  let C : ℝ := 2*(R:ℝ)
  let D : ℝ := (Q.card:ℝ)*(R:ℝ)*(L:ℝ)⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  change chargeMass Q k S a b ≤ chargeBound C D k b
  induction k generalizing S a b with
  | zero => rfl
  | succ k ih =>
    have ho := fun b => ih b (a-1) S (Nat.le_trans (Nat.sub_le _ _) ha) (by omega)
    have hf := fun b (v : Internal S) => ih b a (grow S v) (by rw [leaves_grow]; omega)
      (by rw [leaves_grow]; omega)
    have hle : (leaves S:ℝ) ≤ (R:ℝ) := by exact_mod_cast (show leaves S ≤ R by omega)
    have haR : (a:ℝ) + (leaves S:ℝ) ≤ C := by
      have haa : (a:ℝ) ≤ (leaves S:ℝ) := by exact_mod_cast ha
      dsimp [C]
      linarith
    have hsum := sum_abs_gamma_grid hL S
    have hgood : (∑ v : Internal S, if charged S Q v then
        |gamma S (grid L 0 L) v| else 0) ≤ D :=
      (unary_set_budget S 0 L Q).trans (by
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Nat.cast_nonneg _))
        exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _))
    cases b with
    | zero =>
      simp only [chargeMass, Nat.zero_sub, chargeBound]
      calc
        _ ≤ (a:ℝ) * chargeBound C D k 0 +
            ∑ v : Internal S, |gamma S (grid L 0 L) v| * chargeBound C D k 0 := by
          apply add_le_add (mul_le_mul_of_nonneg_left (ho 0) (Nat.cast_nonneg _))
          exact Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hf 0 v) (abs_nonneg _))
        _ = ((a:ℝ)+(leaves S:ℝ))*chargeBound C D k 0 := by
          rw [← Finset.sum_mul, hsum]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right haR (chargeBound_nonneg hC hD _ _)
    | succ b =>
      have hf' (v : Internal S) :
          chargeMass Q k (grow S v) a (b+1 - if charged S Q v then 1 else 0) ≤
            chargeBound C D k (b+1) +
              (if charged S Q v then chargeBound C D k b else 0) := by
        by_cases hv : charged S Q v
        · simp only [ite_eq_left hv, Nat.add_sub_cancel]
          exact (hf b v).trans (le_add_of_nonneg_left (chargeBound_nonneg hC hD _ _))
        · simp only [ite_eq_right hv, Nat.sub_zero, add_zero]
          exact hf (b+1) v
      change (a:ℝ)*chargeMass Q k S (a-1) (b+1) + _ ≤
        C*chargeBound C D k (b+1) + D*chargeBound C D k b
      calc
        _ ≤ (a:ℝ) * chargeBound C D k (b+1) +
            ∑ v : Internal S, |gamma S (grid L 0 L) v| *
              (chargeBound C D k (b+1) +
                if charged S Q v then chargeBound C D k b else 0) := by
          exact add_le_add (mul_le_mul_of_nonneg_left (ho _) (Nat.cast_nonneg _))
            (Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hf' v) (abs_nonneg _)))
        _ = ((a:ℝ)+(leaves S:ℝ))*chargeBound C D k (b+1) +
            (∑ v : Internal S, if charged S Q v then
              |gamma S (grid L 0 L) v| else 0) * chargeBound C D k b := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum]
          rw [Finset.sum_mul]
          have heq : (∑ v : Internal S, |gamma S (grid L 0 L) v| *
              (if charged S Q v then chargeBound C D k b else 0)) =
              ∑ v : Internal S, (if charged S Q v then |gamma S (grid L 0 L) v| else 0) *
                chargeBound C D k b := by
            apply Finset.sum_congr rfl
            intro v _
            split <;> simp_all only [mul_zero, zero_mul]
          rw [heq]
          ring
        _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_right haR (chargeBound_nonneg hC hD _ _))
          (mul_le_mul_of_nonneg_right hgood (chargeBound_nonneg hC hD _ _))

 
theorem charging_final_shape {L : ℕ} (hL : 0 < L) (Q : Finset ℕ) (k b a : ℕ)
    (S : PrescribedTree L) (ha : a ≤ leaves S) :
    historyMass (fun T => if branchingCount S (· ∈ Q) + b ≤
        branchingCount T (· ∈ Q) then 1 else 0) k S a ≤
      chargeBound (2*(leaves S+k:ℕ)) ((Q.card:ℝ)*(leaves S+k:ℕ)) k b *
        (L:ℝ)⁻¹^b := by
  rw [← chargeMass_eq_historyMass Q, Nat.add_sub_cancel_left]
  have hh := chargeMass_bound hL Q (leaves S+k) k b a S ha le_rfl
  rw [chargeBound_scale] at hh
  exact hh

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
