import Mathlib
import OAI.Analysis.BoundedHochschild.CatalanWords
import OAI.Analysis.BoundedHochschild.Haagerup

namespace OAI

/-! Repeated indices, block words, range counts and normalized collision errors. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildCollision
noncomputable section
open Finset
variable {α : Type*} [DecidableEq α]

 
def count (a : α) (l : List (α × Bool)) : ℕ := (l.map Prod.fst).count a

@[simp] lemma count_cons (a c : α) (b : Bool) (l : List (α × Bool)) :
    count a ((c,b)::l) = (if c=a then 1 else 0) + count a l := by
  by_cases h : c=a <;> simp [count, h, Nat.add_comm]

lemma count_parity (a : α) (l : List (α × Bool)) :
    Multiplicative.toAdd ((FreeGroup.lift
      (fun c : α => Multiplicative.ofAdd (if c=a then (1 : ZMod 2) else 0)))
        (FreeGroup.mk l)) = (count a l : ZMod 2) := by
  induction l with
  | nil => simp [count, ← FreeGroup.one_eq_mk]
  | cons p l ih =>
    rcases p with ⟨c,b⟩
    change Multiplicative.toAdd ((FreeGroup.lift _)
      (FreeGroup.mk ([(c,b)] ++ l))) = _
    rw [← FreeGroup.mul_mk, map_mul, toAdd_mul, ih, count_cons, Nat.cast_add]
    congr 1
    cases b
    · change Multiplicative.toAdd ((FreeGroup.lift _)
        (FreeGroup.of c)⁻¹) = _
      rw [map_inv, toAdd_inv, FreeGroup.lift_apply_of]
      by_cases h : c=a <;> simp [h]
    · change Multiplicative.toAdd ((FreeGroup.lift _) (FreeGroup.of c)) = _
      rw [FreeGroup.lift_apply_of]
      by_cases h : c=a <;> simp [h]

 
lemma combined_count_ne_one {l k : List (α × Bool)} (h : FreeGroup.mk l = FreeGroup.mk k)
    (a : α) : count a l + count a k ≠ 1 := by
  have hp : (count a l : ZMod 2) = (count a k : ZMod 2) := by
    simpa only [count_parity] using congrArg (fun g => Multiplicative.toAdd
      ((FreeGroup.lift (fun c : α => Multiplicative.ofAdd
        (if c=a then (1 : ZMod 2) else 0))) g)) h
  intro hc
  have hc' : count a l=1 ∧ count a k=0 ∨ count a l=0 ∧ count a k=1 := by omega
  rcases hc' with ⟨hl,hk⟩|⟨hl,hk⟩ <;> simp [hl,hk] at hp

lemma count_reduce_le (a : α) (l : List (α × Bool)) :
    count a (FreeGroup.reduce l) ≤ count a l := by
  exact (((FreeGroup.reduce.red (L:=l)).sublist).map Prod.fst).count_le a

lemma exists_repeat_of_not_nodup (l : List α) (h : ¬ l.Nodup) :
    ∃ a, 2 ≤ l.count a := by
  by_contra! hn
  apply h
  rw [List.nodup_iff_count_le_one]
  intro a
  exact Nat.le_of_lt_succ (hn a)

variable [Fintype α]

lemma sum_count (l : List (α × Bool)) : ∑ a : α, count a l = l.length := by
  induction l with
  | nil => simp [count]
  | cons p l ih =>
    rcases p with ⟨a,b⟩
    simp only [count_cons, sum_add_distrib, ih, List.length_cons]
    simp [Nat.add_comm]

 

theorem range_card_le_of_repeated_reduction {l k : List (α × Bool)} {L : ℕ}
    (hl : l.length=L) (hk : k.length=L)
    (he : FreeGroup.mk l = FreeGroup.mk k)
    (hbad : ¬ ((FreeGroup.reduce l).map Prod.fst).Nodup) :
    ((l.map Prod.fst ++ k.map Prod.fst).toFinset).card + 1 ≤ L := by
  obtain ⟨a, ha⟩ := exists_repeat_of_not_nodup _ hbad
  change 2 ≤ count a (FreeGroup.reduce l) at ha
  have hal : 2 ≤ count a l := ha.trans (count_reduce_le a l)
  have hred : FreeGroup.reduce l = FreeGroup.reduce k := congrArg FreeGroup.toWord he
  have hak : 2 ≤ count a k := by rw [hred] at ha; exact ha.trans (count_reduce_le a k)
  let s := (l.map Prod.fst ++ k.map Prod.fst).toFinset
  have has : a∈s := by
    simp only [s, List.mem_toFinset, List.mem_append]
    left
    exact List.count_pos_iff.mp (show 0 < count a l by omega)
  have hs (b : α) (hb : b∈s) : 2 ≤ count b l + count b k := by
    have hpos : 0 < count b l + count b k := by
      change 0 < (l.map Prod.fst).count b + (k.map Prod.fst).count b
      rw [← List.count_append]
      exact List.count_pos_iff.mpr (List.mem_toFinset.mp hb)
    have hne := combined_count_ne_one he b
    omega
  have hsum : ∑ b ∈ s, (count b l + count b k) = 2*L := by
    rw [sum_subset (subset_univ s)]
    · rw [sum_add_distrib, sum_count, sum_count, hl, hk]; omega
    · intro b _ hb
      have hb' : b ∉ l.map Prod.fst ∧ b ∉ k.map Prod.fst := by
        simpa only [s, List.mem_toFinset, List.mem_append, not_or] using hb
      simp [count, List.count_eq_zero.mpr hb'.1, List.count_eq_zero.mpr hb'.2]
  have hlower : 2*s.card + 2 ≤ ∑ b ∈ s, (count b l + count b k) := by
    calc
      2*s.card+2 = ∑ b ∈ s, (2 + if b=a then 2 else 0) := by
        simp [sum_add_distrib, has, Nat.mul_comm]
      _ ≤ _ := sum_le_sum fun b hb => by
        by_cases hba : b=a
        · subst b; simp; omega
        · simpa [hba] using hs b hb
  rw [hsum] at hlower
  change s.card + 1 ≤ L
  omega

end
end HochschildCollision

namespace HochschildBlockWords
noncomputable section
open List FreeGroup HochschildCatalanWords
variable {α : Type*}

@[simp] lemma length_signed (b : Bool) (l : List α) : (signed b l).length = l.length := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => simp [signed, ih]

def Ends (b : Bool) (w : List (α × Bool)) : Prop :=
  (∃ a l, w = (a,b)::l) ∧ (∃ l a, w = l ++ [(a,b)])

lemma signed_odd_ends (l : List α) (hl : l.length % 2 = 1) (b : Bool) :
    Ends b (signed b l) := by
  induction l using List.twoStepInduction generalizing b with
  | nil => simp at hl
  | singleton a => exact ⟨⟨a, [], rfl⟩, ⟨[], a, rfl⟩⟩
  | cons_cons a c l ih _ =>
    have hl' : l.length % 2 = 1 := by simp only [List.length_cons] at hl; omega
    obtain ⟨_, ⟨k,d,hk⟩⟩ := ih hl' b
    exact ⟨⟨a, (c,!b) :: signed b l, by simp [signed]⟩,
      ⟨(a,b)::(c,!b)::k, d, by simp [signed, hk]⟩⟩

variable [DecidableEq α]

lemma reduce_signed_odd_ends (l : List α) (hl : l.length % 2 = 1) (b : Bool) :
    Ends b (reduce (signed b l)) := by
  have hr := (reduce.red (L:=signed b l)).length
  rw [reduce_signed, length_signed, length_signed] at hr
  obtain ⟨n,hn⟩ := hr
  have hp : (unorientedReduce l).length % 2 = 1 := by omega
  rw [reduce_signed]
  exact signed_odd_ends _ hp b

omit [DecidableEq α] in
lemma ends_append {l k : List (α × Bool)} {b : Bool} (hl : Ends b l) (hk : Ends b k) :
    Ends b (l++k) := by
  obtain ⟨⟨a,v,rfl⟩,_⟩ := hl
  obtain ⟨_,⟨w,c,rfl⟩⟩ := hk
  exact ⟨⟨a,v++(w++[(c,b)]),rfl⟩,
    ⟨((a,b)::v)++w,c, by simp [List.append_assoc]⟩⟩

omit [DecidableEq α] in
lemma reduced_append_of_ends {l k : List (α × Bool)} {b : Bool}
    (hl : IsReduced l) (hk : IsReduced k) (hel : Ends b l) (hek : Ends b k) :
    IsReduced (l++k) := by
  obtain ⟨_,⟨v,a,rfl⟩⟩ := hel
  obtain ⟨⟨c,w,rfl⟩,_⟩ := hek
  change List.IsChain _ _
  rw [List.append_assoc, List.singleton_append, List.isChain_append_cons_cons]
  exact ⟨hl,fun _ => rfl,hk⟩

 

theorem reduce_append_odd_blocks (l k : List (α × Bool)) {b : Bool}
    (hl : Ends b (reduce l)) (hk : Ends b (reduce k)) :
    reduce (l++k) = reduce l ++ reduce k ∧ Ends b (reduce (l++k)) := by
  have hr : IsReduced (reduce l ++ reduce k) := reduced_append_of_ends
    (IsReduced.of_reduce_eq (by simp)) (IsReduced.of_reduce_eq (by simp)) hl hk
  have he : reduce (l++k) = reduce l ++ reduce k := by
    rw [← reduce_append_reduce_reduce, hr.reduce_eq]
  exact ⟨he,he ▸ ends_append hl hk⟩

end
end HochschildBlockWords

namespace HochschildIndexedHaagerup
noncomputable section
open Finset
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {G : Type*} [Group G] [DecidableEq G]
variable (τ : A →ₚ[ℂ] ℂ) (u : G →* A)
variable (hτ : τ 1 = 1) (hu : ∀ g, star (u g) = u g⁻¹)
variable (hfree : ∀ g : G, g ≠ 1 → τ (u g) = 0)
include hτ hu hfree

 

lemma norm_sum_sq {I : Type*} [Fintype I] (g : I → G) :
    ‖τ.toPreGNS (∑ i, u (g i))‖^2 =
      Fintype.card {p : I × I // g p.1 = g p.2} := by
  classical
  have hi : inner ℂ (τ.toPreGNS (∑ i, u (g i)))
      (τ.toPreGNS (∑ i, u (g i))) =
      (Fintype.card {p : I × I // g p.1 = g p.2} : ℂ) := by
    simp only [map_sum, sum_inner, inner_sum,
      HochschildTracePolynomial.inner_word τ u hτ hu hfree]
    simp only [Fintype.card_subtype, Finset.card_filter, Nat.cast_sum, apply_ite,
      Nat.cast_one, Nat.cast_zero, Fintype.sum_prod_type]
    exact Finset.sum_comm
  apply Complex.ofReal_injective
  simpa [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow] using hi

end
end HochschildIndexedHaagerup

namespace HochschildIndexedHaagerup
noncomputable section
open Finset HochschildTransfer
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (u : FreeGroup α →* A)
variable (hτ : τ 1 = 1) (hu : ∀ g, star (u g) = u g⁻¹)
variable (hfree : ∀ g : FreeGroup α, g ≠ 1 → τ (u g) = 0)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
variable (hfaith : ∀ a : A, τ (star a*a) = 0 → a = 0)
include hτ hu hfree htr hfaith

lemma norm_sum_le {I : Type*} [Fintype I] (g : I → FreeGroup α) (q : ℕ)
    (hq : ∀ i, (g i).toWord.length = q) :
    ‖∑ i, u (g i)‖ ≤ (q+1:ℝ) *
      Real.sqrt (Fintype.card {p : I × I // g p.1 = g p.2}) := by
  classical
  let p : Polynomial α := ∑ i, MonoidAlgebra.single (g i) (1:ℂ)
  have hp : ∀ x ∈ p.coeff.support, x.toWord.length = q := by
    intro x hx
    have hx' : (∑ i : I, if g i = x then (1:ℂ) else 0) ≠ 0 := by
      simpa only [p, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
        MonoidAlgebra.coeff_single, Finsupp.single_apply] using Finsupp.mem_support_iff.mp hx
    obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx'
    have he : g i = x := by by_contra h; simp [h] at hi
    simpa only [← he] using hq i
  have he : MonoidAlgebra.lift ℂ A (FreeGroup α) u p = ∑ i, u (g i) := by
    simp only [p,map_sum,MonoidAlgebra.lift_single,one_smul]
  have h := norm_eval_homogeneous_le τ u hτ hu hfree htr hfaith p q hp
  rw [he] at h
  have hn := norm_sum_sq τ u hτ hu hfree g
  have he' : ‖τ.toPreGNS (∑ i, u (g i))‖ =
      Real.sqrt (Fintype.card {p : I × I // g p.1 = g p.2}) := by
    rw [← hn, Real.sqrt_sq (norm_nonneg _)]
  simpa only [he'] using h

end
end HochschildIndexedHaagerup

namespace HochschildRangeCount
noncomputable section
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev SmallRange (n k : ℕ) :=
  {f : Fin n → α // (Finset.univ.image f).card ≤ k}

def composeSmall {n k : ℕ} (p : (Fin k → α) × (Fin n → Fin k)) : SmallRange (α:=α) n k :=
  ⟨p.1 ∘ p.2, (card_le_card (by
    intro a ha
    obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    exact mem_image.mpr ⟨p.2 i, mem_univ _, rfl⟩ :
    univ.image (p.1 ∘ p.2) ⊆ univ.image p.1)).trans
      (card_image_le.trans (by simp))⟩

omit [Fintype α] in
lemma composeSmall_surjective [Nonempty α] (n k : ℕ) :
    Function.Surjective (composeSmall (α:=α) (n:=n) (k:=k)) := by
  classical
  let : Inhabited α := Classical.inhabited_of_nonempty ‹Nonempty α›
  intro h
  let s := Finset.univ.image h.val
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card ↥s ≤ Fintype.card (Fin k) by simpa only [Fintype.card_coe, Fintype.card_fin] using h.property)
  let f : Fin k → α := Function.extend e Subtype.val (fun _ => default)
  let g : Fin n → Fin k := fun i => e ⟨h.val i, by simp [s]⟩
  refine ⟨(f,g), Subtype.ext ?_⟩
  funext i
  exact e.injective.extend_apply Subtype.val (fun _ => default) ⟨h.val i, by simp [s]⟩

 
theorem card_smallRange_le [Nonempty α] (n k : ℕ) :
    Fintype.card (SmallRange (α:=α) n k) ≤ (Fintype.card α)^k * k^n := by
  have h := Fintype.card_le_of_surjective _ (composeSmall_surjective (α:=α) n k)
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] using h

end
end HochschildRangeCount

namespace HochschildCollision
noncomputable section
open Finset HochschildRangeCount
variable {α : Type*} [Fintype α] [DecidableEq α]

def tupleWord {L : ℕ} (σ : Fin L → Bool) (f : Fin L → α) : List (α × Bool) :=
  List.ofFn fun i => (f i, σ i)

omit [Fintype α] [DecidableEq α] in
@[simp] lemma tupleWord_length {L : ℕ} (σ : Fin L → Bool) (f : Fin L → α) :
    (tupleWord σ f).length = L := by simp [tupleWord]

omit [Fintype α] [DecidableEq α] in
@[simp] lemma tupleWord_map {L : ℕ} (σ : Fin L → Bool) (f : Fin L → α) :
    (tupleWord σ f).map Prod.fst = List.ofFn f := by simp [tupleWord, List.map_ofFn, Function.comp_def]

abbrev BadPairs {L : ℕ} (σ : Fin L → Bool) :=
  {p : (Fin L → α) × (Fin L → α) //
    FreeGroup.mk (tupleWord σ p.1) = FreeGroup.mk (tupleWord σ p.2) ∧
      ¬ ((FreeGroup.reduce (tupleWord σ p.1)).map Prod.fst).Nodup}

omit [Fintype α] in
lemma ofFn_toFinset {n : ℕ} (f : Fin n → α) :
    (List.ofFn f).toFinset = univ.image f := by
  ext a
  simp

def pairToSmall {L : ℕ} (σ : Fin L → Bool) (p : BadPairs (α:=α) σ) :
    SmallRange (α:=α) (L+L) (L-1) := by
  refine ⟨Fin.append p.val.1 p.val.2, ?_⟩
  have h := range_card_le_of_repeated_reduction
    (tupleWord_length σ p.val.1) (tupleWord_length σ p.val.2) p.property.1 p.property.2
  rw [tupleWord_map,tupleWord_map, ← List.ofFn_fin_append, ofFn_toFinset] at h
  omega

lemma pairToSmall_injective {L : ℕ} (σ : Fin L → Bool) :
    Function.Injective (pairToSmall (α:=α) σ) := by
  intro p q hpq
  have h : Fin.append p.val.1 p.val.2 = Fin.append q.val.1 q.val.2 :=
    congrArg Subtype.val hpq
  apply Subtype.ext
  apply Prod.ext
  · funext i
    simpa only [Fin.append_left] using congrFun h (Fin.castAdd L i)
  · funext i
    simpa only [Fin.append_right] using congrFun h (Fin.natAdd L i)

 

theorem card_badPairs_le [Nonempty α] {L : ℕ} (σ : Fin L → Bool) :
    Fintype.card (BadPairs (α:=α) σ) ≤ (Fintype.card α)^(L-1) * (L-1)^(2*L) := by
  have h := Fintype.card_le_of_injective (pairToSmall (α:=α) σ) (pairToSmall_injective (α:=α) σ)
  exact h.trans (by simpa only [two_mul] using card_smallRange_le (α:=α) (L+L) (L-1))

end
end HochschildCollision

namespace HochschildBlockError
noncomputable section
open Finset HochschildCollision HochschildIndexedHaagerup
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev BadTerms {L : ℕ} (σ : Fin L → Bool) (q : ℕ) :=
  {f : Fin L → α // (FreeGroup.mk (tupleWord σ f)).toWord.length = q ∧
    ¬ ((FreeGroup.reduce (tupleWord σ f)).map Prod.fst).Nodup}

def wordOf {L : ℕ} (σ : Fin L → Bool) (f : Fin L → α) : FreeGroup α :=
  FreeGroup.mk (tupleWord σ f)

def pairToBad {L : ℕ} (σ : Fin L → Bool) (q : ℕ)
    (p : {p : BadTerms (α:=α) σ q × BadTerms (α:=α) σ q //
      wordOf σ p.1.val = wordOf σ p.2.val}) : BadPairs (α:=α) σ :=
  ⟨(p.val.1.val,p.val.2.val),p.property,p.val.1.property.2⟩

omit [Fintype α] in
lemma pairToBad_injective {L : ℕ} (σ : Fin L → Bool) (q : ℕ) :
    Function.Injective (pairToBad (α:=α) σ q) := by
  intro p z hpz
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun p : BadPairs (α:=α) σ => p.val.1) hpz
  · apply Subtype.ext
    exact congrArg (fun p : BadPairs (α:=α) σ => p.val.2) hpz

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (u : FreeGroup α →* A)
variable (hτ : τ 1 = 1) (hu : ∀ g, star (u g) = u g⁻¹)
variable (hfree : ∀ g : FreeGroup α, g ≠ 1 → τ (u g) = 0)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
variable (hfaith : ∀ a : A, τ (star a*a) = 0 → a = 0)

 
def badSum {L : ℕ} (σ : Fin L → Bool) (q : ℕ) : A :=
  ∑ f : BadTerms (α:=α) σ q, u (wordOf σ f.val)

include hτ hu hfree htr hfaith in
lemma badSum_norm_le [Nonempty α] {L : ℕ} (σ : Fin L → Bool) (q : ℕ) :
    ‖badSum u σ q‖ ≤ (q+1:ℝ) *
      Real.sqrt ((Fintype.card α:ℝ)^(L-1) * (L-1:ℕ)^(2*L)) := by
  have hb := norm_sum_le τ u hτ hu hfree htr hfaith
    (fun f : BadTerms (α:=α) σ q => wordOf σ f.val) q (fun f => f.property.1)
  have hc := Fintype.card_le_of_injective (pairToBad (α:=α) σ q) (pairToBad_injective σ q)
  have hc' := hc.trans (card_badPairs_le (α:=α) σ)
  have hreal : (Fintype.card {p : BadTerms (α:=α) σ q × BadTerms (α:=α) σ q //
      wordOf σ p.1.val = wordOf σ p.2.val} : ℝ) ≤
      (Fintype.card α:ℝ)^(L-1)*(L-1:ℕ)^(2*L) := by exact_mod_cast hc'
  exact hb.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hreal) (by positivity))

 
def normalizer (r L : ℕ) : ℝ := (Real.sqrt r)⁻¹ ^ L

lemma normalizer_nonneg (r L : ℕ) : 0 ≤ normalizer r L := by unfold normalizer; positivity

lemma normalizer_sq (r L : ℕ) : normalizer r L ^ 2 = ((r:ℝ)^L)⁻¹ := by
  unfold normalizer
  rw [← pow_mul, Nat.mul_comm L 2, pow_mul, inv_pow,
    Real.sq_sqrt (by positivity), inv_pow]

lemma normalizer_cancel {r L : ℕ} (hr : 0 < r) (hL : 0 < L) :
    normalizer r L ^ 2 * (r:ℝ)^(L-1) = (r:ℝ)⁻¹ := by
  rw [normalizer_sq]
  have hr' : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hp : (r:ℝ)^L = (r:ℝ)^(L-1) * r := by
    simpa only [pow_succ] using congrArg (fun n : ℕ => (r:ℝ)^n) (show L = (L-1)+1 by omega)
  rw [hp]
  field_simp

include hτ hu hfree htr hfaith in
 

theorem normalized_badSum_sq_le [Nonempty α] {L : ℕ} (hL : 0 < L)
    (σ : Fin L → Bool) (q : ℕ) :
    ‖normalizer (Fintype.card α) L • badSum u σ q‖^2 ≤
      ((q+1:ℝ)^2 * (L-1:ℕ)^(2*L)) / Fintype.card α := by
  have hn := badSum_norm_le τ u hτ hu hfree htr hfaith σ q
  have hc : 0 ≤ (Fintype.card α:ℝ)^(L-1) * (L-1:ℕ)^(2*L) := by positivity
  have hn' : ‖badSum u σ q‖^2 ≤
      (q+1:ℝ)^2 * ((Fintype.card α:ℝ)^(L-1)*(L-1:ℕ)^(2*L)) := by
    have h := sq_le_sq₀ (norm_nonneg (badSum u σ q)) (by positivity :
      0 ≤ (q+1:ℝ)*Real.sqrt ((Fintype.card α:ℝ)^(L-1)*(L-1:ℕ)^(2*L)))
    have h' := h.mpr hn
    simpa only [mul_pow, Real.sq_sqrt hc] using h'
  calc
    _ = normalizer (Fintype.card α) L ^ 2 * ‖badSum u σ q‖^2 := by
      rw [norm_smul, Real.norm_of_nonneg (normalizer_nonneg _ _),mul_pow]
    _ ≤ normalizer (Fintype.card α) L ^ 2 *
        ((q+1:ℝ)^2 * ((Fintype.card α:ℝ)^(L-1)*(L-1:ℕ)^(2*L))) :=
      mul_le_mul_of_nonneg_left hn' (sq_nonneg _)
    _ = (normalizer (Fintype.card α) L ^ 2 * (Fintype.card α:ℝ)^(L-1)) *
        ((q+1:ℝ)^2*(L-1:ℕ)^(2*L)) := by ring
    _ = _ := by rw [normalizer_cancel Fintype.card_pos hL]; ring

end

noncomputable section
open Filter
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (u : (r : ℕ) → FreeGroup (Fin (r+1)) →* A)
variable (hτ : τ 1 = 1) (hu : ∀ r g, star (u r g) = u r g⁻¹)
variable (hfree : ∀ r (g : FreeGroup (Fin (r+1))), g ≠ 1 → τ (u r g) = 0)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
variable (hfaith : ∀ a : A, τ (star a*a) = 0 → a = 0)
include hτ hu hfree htr hfaith

 
theorem tendsto_normalized_badSum {L : ℕ} (hL : 0 < L) (σ : Fin L → Bool) (q : ℕ) :
    Tendsto (fun r => normalizer (r+1) L • badSum (u r) σ q) atTop (𝓝 0) := by
  have hsq : Tendsto (fun r => ‖normalizer (r+1) L • badSum (u r) σ q‖^2)
      atTop (𝓝 0) := by
    have hb (r : ℕ) : ‖normalizer (r+1) L • badSum (u r) σ q‖^2 ≤
        ((q+1:ℝ)^2 * (L-1:ℕ)^(2*L)) / ((r:ℝ)+1) := by
      simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
        normalized_badSum_sq_le τ (u r) hτ (hu r) (hfree r) htr hfaith hL σ q
    exact squeeze_zero (fun r => sq_nonneg _) hb
      (tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt

 
theorem tendsto_total_badSum {L : ℕ} (hL : 0 < L) (σ : Fin L → Bool) :
    Tendsto (fun r => ∑ q ∈ Finset.range (L+1),
      normalizer (r+1) L • badSum (u r) σ q) atTop (𝓝 0) := by
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.range (L+1))
      (fun q _ => tendsto_normalized_badSum τ u hτ hu hfree htr hfaith hL σ q)

end
end HochschildBlockError
end

end OAI
