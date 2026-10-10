import OAI.Combinatorics.BooleanFunctions.SoftEvent

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

attribute [local instance] Classical.propDecidable

namespace SquareRootDegree
namespace FiniteRounding

/-- Real-valued finite probabilities; used only to select a deterministic finite table. -/
def productWeight {ι α : Type*} [Fintype ι] (p : ι → α → ℝ) (x : ι → α) : ℝ :=
  ∏ i, p i (x i)

theorem sum_productWeight {ι α : Type*} [Fintype ι] [Fintype α]
    (p : ι → α → ℝ) (hp : ∀ i, ∑ a, p i a = 1) :
    ∑ x, productWeight p x = 1 := by
  classical
  simp only [productWeight]
  rw [← Fintype.prod_sum]
  simp [hp]

theorem productWeight_nonneg {ι α : Type*} [Fintype ι]
    (p : ι → α → ℝ) (hp : ∀ i a, 0 ≤ p i a) (x : ι → α) :
    0 ≤ productWeight p x := Finset.prod_nonneg (fun i _ => hp i (x i))

theorem weighted_product {ι α : Type*} [Fintype ι] [Fintype α]
    (p f : ι → α → ℝ) :
    ∑ x, productWeight p x * ∏ i, f i (x i) = ∏ i, ∑ a, p i a * f i a := by
  classical
  simp only [productWeight, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => p i a * f i a)).symm

theorem weighted_evaluation {ι α : Type*} [Fintype ι] [Fintype α]
    (p : ι → α → ℝ) (hp : ∀ i, ∑ a, p i a = 1) (j : ι) (g : α → ℝ) :
    ∑ x, productWeight p x * g (x j) = ∑ a, p j a * g a := by
  classical
  have h := weighted_product p (fun i a => if i = j then g a else 1)
  simpa [Finset.prod_ite_eq, hp] using h

def bernoulliWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

@[simp] theorem bernoulli_sum (p : ℝ) : ∑ b, bernoulliWeight p b = 1 := by
  simp [bernoulliWeight]

theorem bernoulli_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (b : Bool) :
    0 ≤ bernoulliWeight p b := by cases b <;> simp [bernoulliWeight] <;> linarith

@[simp] theorem bernoulli_expect (p : ℝ) :
    ∑ b, bernoulliWeight p b * (if b then (1:ℝ) else 0) = p := by
  simp [bernoulliWeight]

/-- A distribution over entire leaf-test tables, not random bits added to the cube. -/
def leafWeight {α : Type*} [Fintype α] (p : α → ℝ) (t : α → Bool) : ℝ :=
  productWeight (fun a => bernoulliWeight (p a)) t

@[simp] theorem leafWeight_sum {α : Type*} [Fintype α] (p : α → ℝ) :
    ∑ t, leafWeight p t = 1 := sum_productWeight _ (fun _ => bernoulli_sum _)

theorem leafWeight_nonneg {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hp' : ∀ a, p a ≤ 1) (t : α → Bool) :
    0 ≤ leafWeight p t := productWeight_nonneg _ (fun a => bernoulli_nonneg (hp a) (hp' a)) t

@[simp] theorem leafWeight_eval {α : Type*} [Fintype α] (p : α → ℝ) (a : α) :
    ∑ t, leafWeight p t * (if t a then (1:ℝ) else 0) = p a := by
  simp only [leafWeight]
  simpa [bernoulliWeight] using weighted_evaluation (fun x => bernoulliWeight (p x))
    (fun _ => bernoulli_sum _) a (fun b => if b then (1 : ℝ) else 0)

theorem exists_ge_weighted_sum {α : Type*} [Fintype α] (p f : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (c : ℝ)
    (hc : c < ∑ a, p a * f a) : ∃ a, c < f a := by
  by_contra h
  push Not at h
  have he : ∑ a, p a * f a ≤ c := by
    calc ∑ a, p a * f a ≤ ∑ a, p a * c := by
           apply Finset.sum_le_sum; intro a _; exact mul_le_mul_of_nonneg_left (h a) (hp a)
      _ = c := by rw [← Finset.sum_mul, hs, one_mul]
  exact (not_lt_of_ge he) hc

end FiniteRounding
end SquareRootDegree

namespace SquareRootDegree
namespace TableRounding
open FiniteRounding SoftEvent
attribute [local instance] Classical.propDecidable
variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]

def tableWeight (s w : ι → β → ℝ) (t : (β → ι) × (ι → β → Bool)) : ℝ :=
  productWeight (fun b i => s i b) t.1 * productWeight (fun i => leafWeight (w i)) t.2

def bit (b : Bool) : ℝ := if b then 1 else 0

def tableEvent (S : β → ι) (L : ι → β → Bool) (x : β × (ι → β)) : Prop :=
  L (S x.1) (x.2 (S x.1)) = false ∧ ∀ i, i ≠ S x.1 → L i (x.2 i) = true

omit [Fintype β] in
theorem event_indicator (S : β → ι) (L : ι → β → Bool) (x : β × (ι → β)) :
    (if tableEvent S L x then (1:ℝ) else 0) =
      softWeight (fun i b => if S b = i then 1 else 0) (fun i b => bit (L i b)) x := by
  have hs : (∑ i, (if S x.1 = i then (1:ℝ) else 0) *
      ∏ j ∈ Finset.univ.erase i, bit (L j (x.2 j))) =
      ∏ j ∈ Finset.univ.erase (S x.1), bit (L j (x.2 j)) := by simp
  unfold softWeight
  rw [hs]
  have hp : (∏ j, bit (L j (x.2 j))) = bit (L (S x.1) (x.2 (S x.1))) *
      ∏ j ∈ Finset.univ.erase (S x.1), bit (L j (x.2 j)) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
  rw [hp]
  by_cases h : ∀ i, i ≠ S x.1 → L i (x.2 i) = true
  · have he : (∏ j ∈ Finset.univ.erase (S x.1), bit (L j (x.2 j))) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      simp [bit,h j (Finset.mem_erase.mp hj).1]
    rw [he]
    cases hb : L (S x.1) (x.2 (S x.1))
    · simp only [tableEvent,hb,true_and,bit,Bool.false_eq_true,ite_false,zero_mul,sub_zero]
      rw [ite_eq_left h]
    · simp [tableEvent,hb,bit]
  · obtain ⟨j,hj,hb⟩ := by simpa only [not_forall,Classical.not_imp] using h
    have he : (∏ j ∈ Finset.univ.erase (S x.1), bit (L j (x.2 j))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj,Finset.mem_univ _⟩)
      cases ht : L j (x.2 j) <;> simp_all [bit]
    rw [he]
    simp [tableEvent,h]

theorem tableWeight_nonneg (s w : ι → β → ℝ) (hs : ∀ i b, 0 ≤ s i b)
    (hw : ∀ i b, 0 ≤ w i b) (hw' : ∀ i b, w i b ≤ 1) (t) : 0 ≤ tableWeight s w t := by
  exact mul_nonneg (productWeight_nonneg _ (fun b i => hs i b) _)
    (productWeight_nonneg _ (fun i => leafWeight_nonneg _ (hw i) (hw' i)) _)

theorem tableWeight_sum (s w : ι → β → ℝ) (hs : ∀ b, ∑ i, s i b = 1) :
    ∑ t, tableWeight s w t = 1 := by
  simp only [tableWeight,Fintype.sum_prod_type,← Finset.mul_sum,
    sum_productWeight _ (fun i => leafWeight_sum (w i)),mul_one]
  exact sum_productWeight _ hs

theorem weighted_leaf_prod (w : ι → β → ℝ) (x : ι → β) (I : Finset ι) :
    ∑ L : ι → β → Bool, productWeight (fun i => leafWeight (w i)) L *
      ∏ i ∈ I, bit (L i (x i)) = ∏ i ∈ I, w i (x i) := by
  have h := weighted_product (fun i => leafWeight (w i))
    (fun i (t : β → Bool) => if i ∈ I then bit (t (x i)) else 1)
  have hi (i : ι) : (∑ t : β → Bool, leafWeight (w i) t *
      (if i ∈ I then bit (t (x i)) else 1)) = if i ∈ I then w i (x i) else 1 := by
    by_cases hi : i ∈ I
    · simp only [hi,ite_true,bit]
      exact leafWeight_eval (w i) (x i)
    · simp [hi]
  simpa only [Finset.prod_ite_mem,Finset.inter_univ,Finset.univ_inter,hi] using h

theorem weighted_indicator (s w : ι → β → ℝ) (hs : ∀ b, ∑ i, s i b = 1)
    (x : β × (ι → β)) :
    ∑ t, tableWeight s w t * (if tableEvent t.1 t.2 x then (1:ℝ) else 0) =
      softWeight s w x := by
  -- First average the independent leaf-test tables.
  have hL (S : β → ι) :
      (∑ L : ι → β → Bool, productWeight (fun i => leafWeight (w i)) L *
        ((∑ i, (if S x.1 = i then (1:ℝ) else 0) *
          ∏ j ∈ Finset.univ.erase i, bit (L j (x.2 j))) - ∏ j, bit (L j (x.2 j)))) =
      (∑ i, (if S x.1 = i then (1:ℝ) else 0) * ∏ j ∈ Finset.univ.erase i, w j (x.2 j)) -
        ∏ j, w j (x.2 j) := by
    simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [mul_left_comm _ (if _ then _ else _),← Finset.mul_sum,weighted_leaf_prod]
  have hS (i : ι) : (∑ S : β → ι, productWeight (fun b i => s i b) S *
      (if S x.1 = i then (1:ℝ) else 0)) = s i x.1 := by
    simpa using weighted_evaluation (fun b i => s i b) hs x.1 (fun j => if j = i then 1 else 0)
  simp only [tableWeight,Fintype.sum_prod_type]
  simp_rw [event_indicator,mul_assoc,← Finset.mul_sum]
  change (∑ S : β → ι, productWeight (fun b i => s i b) S *
    (∑ L : ι → β → Bool, productWeight (fun i => leafWeight (w i)) L *
      ((∑ i, (if S x.1 = i then (1:ℝ) else 0) *
        ∏ j ∈ Finset.univ.erase i, bit (L j (x.2 j))) - ∏ j, bit (L j (x.2 j))))) = _
  simp_rw [hL,mul_sub,Finset.mul_sum,Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc,← Finset.sum_mul,hS]
  rw [sum_productWeight _ hs,one_mul]
  rfl

theorem weighted_deficit (s w : ι → β → ℝ) (hs : ∀ b, ∑ i, s i b = 1)
    (F : α → β) (T : α → ℝ) (b : ℝ) :
    (∑ t, tableWeight s w t * deficit T b
      (fun x => if tableEvent t.1 t.2 (F x.1,fun i => F (x.2 i)) then 1 else 0)) =
      deficit T b (softWeight (fun i a => s i (F a)) (fun i a => w i (F a))) := by
  simp only [deficit,← average_const_mul,← average_sum]
  congr 1
  funext x
  simp_rw [← mul_assoc,← Finset.sum_mul,weighted_indicator s w hs]
  rfl

theorem exists_event_deficit (s w : ι → β → ℝ)
    (hs : ∀ b, ∑ i, s i b = 1) (hs0 : ∀ i b, 0 ≤ s i b)
    (hw0 : ∀ i b, 0 ≤ w i b) (hw1 : ∀ i b, w i b ≤ 1)
    (F : α → β) (T : α → ℝ) (b c : ℝ)
    (hc : c < deficit T b (softWeight (fun i a => s i (F a)) (fun i a => w i (F a)))) :
    ∃ S : β → ι, ∃ L : ι → β → Bool,
      c < deficit T b (fun x => if tableEvent S L (F x.1,fun i => F (x.2 i)) then 1 else 0) := by
  rw [← weighted_deficit s w hs F T b] at hc
  obtain ⟨t,ht⟩ := exists_ge_weighted_sum (tableWeight s w) _
    (tableWeight_nonneg s w hs0 hw0 hw1) (tableWeight_sum s w hs) c hc
  exact ⟨t.1,t.2,ht⟩

end TableRounding
end SquareRootDegree

end

end OAI
