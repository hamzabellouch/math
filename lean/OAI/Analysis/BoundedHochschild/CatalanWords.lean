import Mathlib

namespace OAI

/-! Binary-tree enumeration of return words and normalized Catalan moments. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildCatalanWords
noncomputable section
open List BinaryTree
variable {α : Type*}

 
def word : BinaryTree α → List α
  | .nil => []
  | .node a l r => a :: (word l ++ a :: word r)

@[simp] lemma length_word (t : BinaryTree α) : (word t).length = 2*t.numNodes := by
  induction t with
  | nil => simp [word]
  | node a l r hl hr => simp [word, hl, hr]; omega

 
def unorientedReduce [DecidableEq α] : List α → List α
  | [] => []
  | a::l => match unorientedReduce l with
    | [] => [a]
    | b::k => if a=b then k else a::b::k

 
def signed : Bool → List α → List (α × Bool)
  | _, [] => []
  | b, a::l => (a,b)::signed (!b) l

@[simp] lemma signed_eq_nil (b : Bool) (l : List α) : signed b l = [] ↔ l = [] := by
  cases l <;> simp [signed]

lemma reduce_signed [DecidableEq α] (b : Bool) (l : List α) :
    FreeGroup.reduce (signed b l) = signed b (unorientedReduce l) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    simp only [signed, FreeGroup.reduce.cons, ih, unorientedReduce]
    cases h : unorientedReduce l with
    | nil => simp [signed]
    | cons c l =>
      simp only [signed]
      by_cases hac : a=c
      · simp [hac, Bool.not_not]
      · simp [hac, signed]

def render (p : BinaryTree α × List (α × BinaryTree α)) : List α :=
  word p.1 ++ p.2.flatMap (fun p => p.1 :: word p.2)

 
def parse [DecidableEq α] : List α → BinaryTree α × List (α × BinaryTree α)
  | [] => (.nil, [])
  | a::l => match parse l with
    | (t,[]) => (.nil,[(a,t)])
    | (t,(b,u)::xs) => if a=b then (.node a t u,xs) else (.nil,(a,t)::(b,u)::xs)

lemma render_parse [DecidableEq α] (l : List α) : render (parse l) = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [parse]
    cases hp : parse l with
    | mk t xs =>
      rw [hp] at ih
      cases xs with
      | nil => simpa [render, word] using congrArg (a :: ·) ih
      | cons p xs =>
        rcases p with ⟨b,u⟩
        by_cases hab : a=b
        · simp only [hab]
          simpa [render, word, List.append_assoc] using congrArg (b :: ·) ih
        · simp only [hab, ite_false]
          simpa [render, word, List.append_assoc] using congrArg (a :: ·) ih

lemma unmatched_parse [DecidableEq α] (l : List α) :
    (parse l).2.map Prod.fst = unorientedReduce l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [parse, unorientedReduce, ← ih]
    cases hp : parse l with
    | mk t xs =>
      cases xs with
      | nil => rfl
      | cons p xs =>
        rcases p with ⟨b,u⟩
        by_cases hab : a=b <;> simp [hab]

 
theorem exists_tree_of_reduce_signed_eq_nil [DecidableEq α]
    (l : List α) (b : Bool) (hl : FreeGroup.reduce (signed b l) = []) :
    ∃ t : BinaryTree α, word t = l := by
  rw [reduce_signed, signed_eq_nil] at hl
  have h := unmatched_parse l
  rw [hl, List.map_eq_nil_iff] at h
  refine ⟨(parse l).1, ?_⟩
  have hp := render_parse l
  simpa only [render, h, flatMap_nil, append_nil] using hp

lemma signed_append_even {l : List α} (hl : 2 ∣ l.length) (k : List α) (b : Bool) :
    signed b (l++k) = signed b l ++ signed b k := by
  induction l using List.twoStepInduction generalizing b with
  | nil => simp [signed]
  | singleton a => simp at hl
  | cons_cons a c l ih _ =>
    have hl' : 2 ∣ l.length := by simpa using hl
    simpa [signed] using congrArg ((a,b) :: (c,!b) :: ·) (ih hl' b)

lemma signed_word_node (a : α) (l r : BinaryTree α) (b : Bool) :
    signed b (word (.node a l r)) =
      (a,b) :: (signed (!b) (word l) ++ (a,!b) :: signed b (word r)) := by
  simp only [word, signed]
  rw [signed_append_even (by simp)]; simp [signed]

lemma reduce_signed_word [DecidableEq α] (t : BinaryTree α) (b : Bool) :
    FreeGroup.reduce (signed b (word t)) = [] := by
  induction t generalizing b with
  | nil => simp [word, signed]
  | node a l r hl hr =>
    rw [signed_word_node]
    have happ : FreeGroup.reduce (signed (!b) (word l) ++ (a,!b) :: signed b (word r)) =
        [(a,!b)] := by
      rw [← FreeGroup.reduce_append_reduce_reduce, hl]
      simp [FreeGroup.reduce.cons, hr]
    simp only [FreeGroup.reduce.cons, happ, Bool.not_not, and_self, ite_true]

 
def labels : BinaryTree α → List α
  | .nil => []
  | .node a l r => a :: (labels l ++ labels r)

@[simp] lemma length_labels (t : BinaryTree α) : (labels t).length = t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simp [labels, hl, hr]

@[simp] lemma mem_word_iff (a : α) (t : BinaryTree α) : a ∈ word t ↔ a ∈ labels t := by
  induction t with
  | nil => rfl
  | node b l r hl hr => simp [word, labels, hl, hr, or_left_comm]

lemma delimiter_split {a : α} {l r l' r' : List α}
    (hl : a ∉ l) (hl' : a ∉ l') (he : l ++ a::r = l' ++ a::r') :
    l=l' ∧ r=r' := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => simpa using he
    | cons b l' =>
      have hab : a=b := List.head_eq_of_cons_eq he
      subst b
      simp at hl'
  | cons b l ih =>
    cases l' with
    | nil =>
      have hba : b=a := List.head_eq_of_cons_eq he
      subst b
      simp at hl
    | cons c l' =>
      have hbc : b=c := List.head_eq_of_cons_eq he
      subst c
      have he' := List.tail_eq_of_cons_eq he
      obtain ⟨rfl, rfl⟩ := ih (by simpa using fun h => hl (List.mem_cons_of_mem _ h))
        (by simpa using fun h => hl' (List.mem_cons_of_mem _ h)) he'
      exact ⟨rfl,rfl⟩

 
theorem word_injective_on_nodup {t u : BinaryTree α}
    (ht : (labels t).Nodup) (hu : (labels u).Nodup) (he : word t = word u) : t=u := by
  induction t generalizing u with
  | nil =>
    cases u with
    | nil => rfl
    | node b l r => simp [word] at he
  | node a l r ihl ihr =>
    cases u with
    | nil => simp [word] at he
    | node b l' r' =>
      simp only [word, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      have ht' := List.nodup_cons.mp ht
      have hu' := List.nodup_cons.mp hu
      have htl := List.nodup_append.mp ht'.2
      have hul := List.nodup_append.mp hu'.2
      obtain ⟨hel, her⟩ := delimiter_split
        (fun h => ht'.1 (List.mem_append_left _ ((mem_word_iff _ _).mp h)))
        (fun h => hu'.1 (List.mem_append_left _ ((mem_word_iff _ _).mp h))) he
      rw [ihl htl.1 hul.1 hel, ihr htl.2.1 hul.2.1 her]

 
def shape : BinaryTree α → BinaryTree Unit := BinaryTree.map (fun _ => ())

@[simp] lemma numNodes_shape (t : BinaryTree α) : (shape t).numNodes = t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simpa [shape, BinaryTree.map] using congrArg₂ (fun x y=> x+y) hl hr

 
def decorate : BinaryTree Unit → List α → BinaryTree α
  | .nil, _ => .nil
  | .node _ _ _, [] => .nil
  | .node _ l r, a::as => .node a (decorate l (as.take l.numNodes))
      (decorate r (as.drop l.numNodes))

lemma decorate_spec (t : BinaryTree Unit) (as : List α) (h : as.length=t.numNodes) :
    shape (decorate t as) = t ∧ labels (decorate t as) = as := by
  induction t generalizing as with
  | nil => simp only [BinaryTree.numNodes] at h; have := List.length_eq_zero_iff.mp h
           subst as; exact ⟨rfl,rfl⟩
  | node a l r hl hr =>
    cases a
    cases as with
    | nil => simp at h
    | cons a as =>
      have llen : l.numNodes ≤ as.length := by simp at h; omega
      obtain ⟨hls,hll⟩ := hl (as.take l.numNodes) (by simp [llen])
      obtain ⟨hrs,hrl⟩ := hr (as.drop l.numNodes) (by simp; simp at h; omega)
      constructor
      · simp only [decorate, shape, BinaryTree.map]
        change BinaryTree.node () (shape _) (shape _) = _
        rw [hls, hrs]
      · simp only [decorate, labels, hll, hrl, List.take_append_drop]

lemma decorate_shape_labels (t : BinaryTree α) : decorate (shape t) (labels t) = t := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    change BinaryTree.node a (decorate (shape l) ((labels l ++ labels r).take (shape l).numNodes))
      (decorate (shape r) ((labels l ++ labels r).drop (shape l).numNodes)) = _
    rw [numNodes_shape, ← length_labels, List.take_left, List.drop_left, hl, hr]

abbrev Shapes (n : ℕ) := ↥(BinaryTree.treesOfNumNodesEq n)

@[simp] lemma card_shapes (n : ℕ) : Fintype.card (Shapes n) = catalan n := by
  rw [Fintype.card_coe, treesOfNumNodesEq_card_eq_catalan]

@[simp] lemma nodes_shape (n : ℕ) (t : Shapes n) : t.val.numNodes = n :=
  BinaryTree.mem_treesOfNumNodesEq.mp t.property

def listFunction {n : ℕ} (l : List α) (h : l.length=n) : Fin n → α :=
  fun i => l.get (i.cast h.symm)

@[simp] lemma ofFn_listFunction {n : ℕ} (l : List α) (h : l.length=n) :
    List.ofFn (listFunction l h) = l := by
  subst n
  exact List.ofFn_get l

abbrev ReturnWords (α : Type*) [DecidableEq α] (n : ℕ) :=
  {f : Fin (2*n) → α // FreeGroup.reduce (signed false (List.ofFn f)) = []}

def treeFrom {n : ℕ} (t : Shapes n) (f : Fin n → α) : BinaryTree α :=
  decorate t.val (List.ofFn f)

@[simp] lemma shape_treeFrom {n : ℕ} (t : Shapes n) (f : Fin n → α) :
    shape (treeFrom t f) = t.val :=
  (decorate_spec _ _ (by simp)).1

@[simp] lemma labels_treeFrom {n : ℕ} (t : Shapes n) (f : Fin n → α) :
    labels (treeFrom t f) = List.ofFn f :=
  (decorate_spec _ _ (by simp)).2

@[simp] lemma nodes_treeFrom {n : ℕ} (t : Shapes n) (f : Fin n → α) :
    (treeFrom t f).numNodes = n := by
  rw [← numNodes_shape, shape_treeFrom, nodes_shape]

variable [DecidableEq α]

def fromTree {n : ℕ} (p : Shapes n × (Fin n → α)) : ReturnWords α n :=
  ⟨listFunction (word (treeFrom p.1 p.2)) (by simp), by
    rw [ofFn_listFunction]; exact reduce_signed_word _ _⟩

@[simp] lemma ofFn_fromTree {n : ℕ} (p : Shapes n × (Fin n → α)) :
    List.ofFn (fromTree p).val = word (treeFrom p.1 p.2) := by
  exact ofFn_listFunction _ (by simp)

lemma fromTree_surjective (n : ℕ) : Function.Surjective (@fromTree α _ n) := by
  intro f
  obtain ⟨t,ht⟩ := exists_tree_of_reduce_signed_eq_nil _ _ f.property
  have hn : t.numNodes = n := by
    have h := congrArg List.length ht
    simp only [length_word, List.length_ofFn] at h
    omega
  let s : Shapes n := ⟨shape t, by simp [hn]⟩
  let g : Fin n → α := listFunction (labels t) (by simp [hn])
  refine ⟨(s,g), Subtype.ext ?_⟩
  apply List.ofFn_injective
  rw [ofFn_fromTree]
  change word (decorate (shape t) (List.ofFn g)) = List.ofFn f.val
  rw [ofFn_listFunction, decorate_shape_labels, ht]

def fromDistinctTree {n : ℕ} (p : Shapes n × (Fin n ↪ α)) : ReturnWords α n :=
  fromTree (p.1, p.2)

lemma fromDistinctTree_injective (n : ℕ) :
    Function.Injective (@fromDistinctTree α _ n) := by
  rintro ⟨s,f⟩ ⟨t,g⟩ h
  have hw : word (treeFrom s f) = word (treeFrom t g) := by
    have h' := congrArg (fun x : ReturnWords α n => List.ofFn x.val) h
    simpa only [fromDistinctTree, ofFn_fromTree] using h'
  have he := word_injective_on_nodup
    (by rw [labels_treeFrom]; exact List.nodup_ofFn_ofInjective f.injective)
    (by rw [labels_treeFrom]; exact List.nodup_ofFn_ofInjective g.injective) hw
  have hs : s=t := Subtype.ext (by simpa only [shape_treeFrom] using congrArg shape he)
  have hf : f=g := by
    apply DFunLike.ext
    intro i
    have hh : (f : Fin n → α) = g := List.ofFn_injective
      (by simpa only [labels_treeFrom] using congrArg labels he)
    exact congrFun hh i
  subst t; subst g; rfl

 

theorem returnWord_count_bounds [Fintype α] (n : ℕ) :
    catalan n * (Fintype.card α).descFactorial n ≤ Fintype.card (ReturnWords α n) ∧
    Fintype.card (ReturnWords α n) ≤ catalan n * (Fintype.card α)^n := by
  constructor
  · have h := Fintype.card_le_of_injective _ (fromDistinctTree_injective (α:=α) n)
    simpa only [Fintype.card_prod, card_shapes, Fintype.card_embedding_eq,
      Fintype.card_fin] using h
  · have h := Fintype.card_le_of_surjective _ (fromTree_surjective (α:=α) n)
    simpa only [Fintype.card_prod, card_shapes, Fintype.card_fun, Fintype.card_fin] using h

open Filter Topology Asymptotics in
 
theorem normalized_returnWord_count_tendsto (n : ℕ) :
    Tendsto (fun r : ℕ => (Fintype.card (ReturnWords (Fin r) n) : ℝ) / (r:ℝ)^n)
      atTop (𝓝 (catalan n : ℝ)) := by
  have hz : ∀ᶠ r : ℕ in atTop, (r:ℝ)^n ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with r hr
    exact pow_ne_zero _ (by exact_mod_cast (show r≠0 by omega))
  have hd := (isEquivalent_iff_tendsto_one hz).mp (isEquivalent_descFactorial n)
  have hlo : Tendsto (fun r : ℕ => (catalan n : ℝ) * (r.descFactorial n : ℝ) / (r:ℝ)^n)
      atTop (𝓝 (catalan n : ℝ)) := by
    simpa only [Pi.div_apply, mul_one, mul_div_assoc] using hd.const_mul (catalan n : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · exact Filter.Eventually.of_forall fun r => by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast (by simpa only [Fintype.card_fin] using
        (returnWord_count_bounds (α:=Fin r) n).1 :
        catalan n * r.descFactorial n ≤ Fintype.card (ReturnWords (Fin r) n))
  · filter_upwards [hz] with r hr
    rw [div_le_iff₀ (lt_of_le_of_ne (by positivity) (Ne.symm hr))]
    exact_mod_cast (by simpa only [Fintype.card_fin] using
      (returnWord_count_bounds (α:=Fin r) n).2 :
      Fintype.card (ReturnWords (Fin r) n) ≤ catalan n * r^n)

end
end HochschildCatalanWords

namespace HochschildCatalanMoments
open HochschildCatalanWords Finset
noncomputable section
variable {α A : Type*} [Fintype α] [Ring A]
variable (u : FreeGroup α →* A)

def signedSum (b : Bool) (n : ℕ) : A :=
  ∑ f : Fin n → α, u (FreeGroup.mk (signed b (List.ofFn f)))

lemma signedSum_succ (b : Bool) (n : ℕ) :
    signedSum u b (n+1) = (∑ a : α, u (FreeGroup.mk [(a,b)])) * signedSum u (!b) n := by
  unfold signedSum
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => α)).sum_comp, Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, signed]
  change u (FreeGroup.mk ([(a,b)] ++ signed (!b) (List.ofFn f))) = _
  rw [← FreeGroup.mul_mk, map_mul]

@[simp] lemma signedSum_zero (b : Bool) : signedSum u b 0 = 1 := by
  simp [signedSum, signed, ← FreeGroup.one_eq_mk]

lemma signedSum_even (n : ℕ) :
    signedSum u false (2*n) =
      ((∑ a : α, u (FreeGroup.mk [(a,false)])) * (∑ a : α, u (FreeGroup.of a)))^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega, signedSum_succ, signedSum_succ]
    simp only [Bool.not_false, Bool.not_true, ih, pow_succ']
    change (∑ a : α, u (FreeGroup.mk [(a,false)])) *
      ((∑ a : α, u (FreeGroup.of a)) *
        ((∑ a : α, u (FreeGroup.mk [(a,false)])) * (∑ a : α, u (FreeGroup.of a)))^n) = _
    exact (mul_assoc _ _ _).symm

variable [StarRing A] (hu : ∀ g, star (u g) = u g⁻¹)
include hu

lemma sum_star : (∑ a : α, u (FreeGroup.mk [(a,false)])) = star (∑ a : α, u (FreeGroup.of a)) := by
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [hu]
  rfl

lemma sum_pow_expansion (n : ℕ) :
    (star (∑ a : α, u (FreeGroup.of a)) * (∑ a : α, u (FreeGroup.of a)))^n =
      signedSum u false (2*n) := by
  rw [signedSum_even, sum_star u hu]

variable [DecidableEq α] [Algebra ℂ A] (τ : A →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
  (hfree : ∀ g : FreeGroup α, g ≠ 1 → τ (u g) = 0)

omit hu [Fintype α] [StarRing A] in
include hτ hfree in
lemma trace_word (l : List (α × Bool)) :
    τ (u (FreeGroup.mk l)) = if FreeGroup.reduce l = [] then 1 else 0 := by
  have he : FreeGroup.reduce l = [] ↔ FreeGroup.mk l = 1 :=
    by simpa only [FreeGroup.toWord_mk] using
      (@FreeGroup.toWord_eq_nil_iff α _ (FreeGroup.mk l))
  by_cases h : FreeGroup.reduce l = []
  · simp [h, he.mp h, hτ]
  · rw [ite_eq_right h]
    exact hfree _ (fun hg => h (he.mpr hg))

include hτ hfree in
lemma trace_sum_pow (n : ℕ) :
    τ ((star (∑ a : α, u (FreeGroup.of a)) * (∑ a : α, u (FreeGroup.of a)))^n) =
      (Fintype.card (ReturnWords α n) : ℂ) := by
  rw [sum_pow_expansion u hu, signedSum, map_sum]
  simp only [trace_word u τ hτ hfree]
  simp [Fintype.card_subtype, ReturnWords]

 
def positiveSum : A := (Fintype.card α : ℂ)⁻¹ •
  (star (∑ a : α, u (FreeGroup.of a)) * (∑ a : α, u (FreeGroup.of a)))

include hτ hfree in
lemma trace_positiveSum_pow (n : ℕ) :
    τ ((positiveSum u)^n) =
      (Fintype.card (ReturnWords α n) : ℂ) / (Fintype.card α : ℂ)^n := by
  rw [positiveSum, smul_pow, map_smul, trace_sum_pow u hu τ hτ hfree]
  simp only [smul_eq_mul, inv_pow, div_eq_mul_inv, mul_comm]

include hτ hfree in
lemma re_trace_positiveSum_pow (n : ℕ) :
    (τ ((positiveSum u)^n)).re =
      (Fintype.card (ReturnWords α n) : ℝ) / (Fintype.card α : ℝ)^n := by
  rw [trace_positiveSum_pow u hu τ hτ hfree]
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]

omit [Fintype α] hu [DecidableEq α] in
open Filter Topology in
 
theorem normalized_moments_tendsto
    (v : (r : ℕ) → FreeGroup (Fin r) →* A)
    (hv : ∀ r g, star (v r g) = v r g⁻¹)
    (hτ : τ 1 = 1) (hfree : ∀ r g, g ≠ 1 → τ (v r g) = 0) (n : ℕ) :
    Tendsto (fun r : ℕ => (τ ((positiveSum (v r))^n)).re)
      atTop (𝓝 (catalan n : ℝ)) := by
  simp_rw [re_trace_positiveSum_pow _ (hv _) τ hτ (hfree _), Fintype.card_fin]
  exact normalized_returnWord_count_tendsto n

end
end HochschildCatalanMoments
end

end OAI
