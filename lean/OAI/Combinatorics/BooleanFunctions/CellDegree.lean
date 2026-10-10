import OAI.Combinatorics.BooleanFunctions.Observations
import OAI.Combinatorics.BooleanFunctions.Switching
import OAI.Combinatorics.BooleanFunctions.Rounding

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace CellDegree
attribute [local instance] Classical.propDecidable
variable {γ β ι : Type*} [Fintype γ] [Fintype β] [Fintype ι]

omit [Fintype β] [Fintype ι] in
theorem sub_le (f g : Cube γ → ℝ) (d : ℕ)
    (hf : fourierDegree f ≤ d) (hg : fourierDegree g ≤ d) :
    fourierDegree (fun x => f x-g x) ≤ d := by
  rw [fourierDegree_le_iff]
  intro s hs
  simp only [fourierCoeff,sub_mul,average_sub]
  change fourierCoeff f s-fourierCoeff g s = 0
  rw [fourierCoeff_eq_zero_of_degree_lt f (lt_of_le_of_lt hf hs),
    fourierCoeff_eq_zero_of_degree_lt g (lt_of_le_of_lt hg hs),sub_self]

theorem event_degree (F₀ : Cube γ → β) (F : ι → Cube γ → β)
    (S : β → ι) (L : ι → β → Bool) (D : ℕ)
    (hF₀ : ∀ b, fourierDegree (cell F₀ b) ≤ D)
    (hF : ∀ i b, fourierDegree (cell (F i) b) ≤ D) :
    fourierDegree (fun x => if TableRounding.tableEvent S L (F₀ x,fun i => F i x) then 1 else 0) ≤
      Fintype.card ι*D := by
  have he : (fun x : Cube γ => if TableRounding.tableEvent S L (F₀ x,fun i => F i x) then (1:ℝ) else 0) =
      fun x => (∑ i, (if S (F₀ x) = i then (1:ℝ) else 0)*
        ∏ j ∈ Finset.univ.erase i, TableRounding.bit (L j (F j x))) -
      ∏ j, TableRounding.bit (L j (F j x)) := by
    funext x
    exact TableRounding.event_indicator S L (F₀ x,fun i => F i x)
  have hl (j : ι) : fourierDegree (fun x => TableRounding.bit (L j (F j x))) ≤ D :=
    fourierDegree_comp_observation_le (F j) D (hF j) (fun b => TableRounding.bit (L j b))
  have hp (I : Finset ι) : fourierDegree (fun x => ∏ j ∈ I, TableRounding.bit (L j (F j x))) ≤ I.card*D := by
    apply (fourierDegree_prod_le I _).trans
    calc ∑ j ∈ I, fourierDegree (fun x => TableRounding.bit (L j (F j x))) ≤ ∑ _j ∈ I, D :=
          Finset.sum_le_sum (fun j _ => hl j)
      _ = I.card*D := by simp
  rw [he]
  apply sub_le
  · apply fourierDegree_sum_le
    intro i _
    have hs : fourierDegree (fun x => if S (F₀ x) = i then (1:ℝ) else 0) ≤ D :=
      fourierDegree_comp_observation_le F₀ D hF₀ (fun b => if S b = i then 1 else 0)
    apply (fourierDegree_mul_le _ _).trans
    apply (Nat.add_le_add hs (hp _)).trans
    have hi : (Finset.univ.erase i : Finset ι).card+1 = Fintype.card ι :=
      Finset.card_erase_add_one (Finset.mem_univ i)
    calc D+(Finset.univ.erase i : Finset ι).card*D =
          ((Finset.univ.erase i : Finset ι).card+1)*D := by ring
      _ = Fintype.card ι*D := by rw [hi]
      _ ≤ Fintype.card ι*D := le_rfl
  · simpa only [Finset.card_univ] using hp Finset.univ

def labelTuple (F₀ : Cube γ → β) (F : ι → Cube γ → β) (x : Cube γ) : β × (ι → β) :=
  (F₀ x,fun i => F i x)

omit [Fintype γ] [Fintype β] in
theorem tuple_cell (F₀ : Cube γ → β) (F : ι → Cube γ → β) (a : β × (ι → β)) :
    cell (labelTuple F₀ F) a = fun x => cell F₀ a.1 x*∏ i, cell (F i) (a.2 i) x := by
  funext x
  rw [← cell_tuple F a.2 x]
  rcases a with ⟨a₀,a⟩
  simp only [cell,labelTuple,Prod.mk.injEq]
  split_ifs <;> simp_all

omit [Fintype β] in
theorem tuple_degree (F₀ : Cube γ → β) (F : ι → Cube γ → β) (D : ℕ)
    (hF₀ : ∀ b, fourierDegree (cell F₀ b) ≤ D)
    (hF : ∀ i b, fourierDegree (cell (F i) b) ≤ D) (a) :
    fourierDegree (cell (labelTuple F₀ F) a) ≤ (Fintype.card ι+1)*D := by
  rw [tuple_cell]
  apply (fourierDegree_mul_le _ _).trans
  have hp : fourierDegree (fun x => ∏ i, cell (F i) (a.2 i) x) ≤ Fintype.card ι*D := by
    apply (fourierDegree_prod_le _ _).trans
    calc ∑ i, fourierDegree (cell (F i) (a.2 i)) ≤ ∑ _i : ι, D :=
          Finset.sum_le_sum (fun i _ => hF i (a.2 i))
      _ = Fintype.card ι*D := by simp
  exact (Nat.add_le_add (hF₀ _) hp).trans (by simp only [Nat.add_mul,one_mul]; omega)

def observationOn (F₀ Fw : Cube γ → β) (F : ι → Cube γ → β)
    (S : β → ι) (L : ι → β → Bool) (x : Cube γ) : (β × (ι → β)) ⊕ β :=
  if TableRounding.tableEvent S L (labelTuple F₀ F x) then Sum.inr (Fw x) else Sum.inl (labelTuple F₀ F x)

theorem observation_degree (F₀ Fw : Cube γ → β) (F : ι → Cube γ → β)
    (S : β → ι) (L : ι → β → Bool) (D : ℕ)
    (hF₀ : ∀ b, fourierDegree (cell F₀ b) ≤ D)
    (hFw : ∀ b, fourierDegree (cell Fw b) ≤ D)
    (hF : ∀ i b, fourierDegree (cell (F i) b) ≤ D) (a) :
    fourierDegree (cell (observationOn F₀ Fw F S L) a) ≤ (Fintype.card ι+1)*D := by
  cases a with
  | inl a =>
    have he : cell (observationOn F₀ Fw F S L) (Sum.inl a) =
        if TableRounding.tableEvent S L a then (fun _ => 0) else cell (labelTuple F₀ F) a := by
      funext x
      unfold cell observationOn
      by_cases h : labelTuple F₀ F x = a
      · by_cases ha : TableRounding.tableEvent S L a <;> simp [h,ha]
      · split_ifs <;> simp_all
    rw [he]
    split_ifs
    · simp [fourierDegree_const]
    · exact tuple_degree F₀ F D hF₀ hF a
  | inr a =>
    have he : cell (observationOn F₀ Fw F S L) (Sum.inr a) = fun x =>
        (if TableRounding.tableEvent S L (labelTuple F₀ F x) then (1:ℝ) else 0)*cell Fw a x := by
      funext x
      unfold cell observationOn
      split_ifs <;> simp_all
    rw [he]
    apply (fourierDegree_mul_le _ _).trans
    exact (Nat.add_le_add (event_degree F₀ F S L D hF₀ hF) (hFw a)).trans (by simp only [Nat.add_mul,one_mul]; omega)

end CellDegree
end SquareRootDegree

namespace SquareRootDegree
namespace Observations
open Switching
attribute [local instance] Classical.propDecidable
variable {γ β ι : Type*} [Fintype γ] [Fintype β] [Fintype ι]
  [DecidableEq γ] [DecidableEq ι]

def fullCubeEquiv (γ ι : Type*) : Cube (Slots ι × γ) ≃ FullSpace (Cube γ) ι :=
  (blockCurry (Slots ι) γ Bool).trans (fullEquiv (Cube γ) ι)

def switched (F : Cube γ → β) (S : β → ι) (L : ι → β → Bool)
    (x : Cube (Slots ι × γ)) : EventSpace β ι ⊕ β :=
  observation F (TableRounding.tableEvent S L) (fullCubeEquiv γ ι x)

omit [DecidableEq γ] [DecidableEq ι] in
theorem switched_degree (F : Cube γ → β) (S : β → ι) (L : ι → β → Bool) (D : ℕ)
    (hF : ∀ b, fourierDegree (cell F b) ≤ D) (a) :
    fourierDegree (cell (switched F S L) a) ≤ (Fintype.card ι+1)*D := by
  have he : switched F S L = CellDegree.observationOn
      (fun x => F (fun i => x (some none,i))) (fun x => F (fun i => x (none,i)))
      (fun j x => F (fun i => x (some (some j),i))) S L := rfl
  rw [he]
  apply CellDegree.observation_degree
  · exact fun a => fourierDegree_block_cell_le F D hF (some none) a
  · exact fun a => fourierDegree_block_cell_le F D hF none a
  · exact fun j a => fourierDegree_block_cell_le F D hF (some (some j)) a

omit [Fintype β] [DecidableEq γ] [DecidableEq ι] in
theorem cubeSum_full (x : Cube (Slots ι × γ)) :
    cubeSum x = totalSum cubeSum (fullCubeEquiv γ ι x) := by
  rw [cubeSum_block]
  exact sum_full cubeSum (blockCurry (Slots ι) γ Bool x)

theorem switched_score (F : Cube γ → β) (S : β → ι) (L : ι → β → Bool) :
    score (switched F S L) =
      conditionalAverage (observation F (TableRounding.tableEvent S L)) (totalSum (score F)) ∘
        fullCubeEquiv γ ι := by
  have he : cubeSum (γ := Slots ι × γ) = totalSum cubeSum ∘ fullCubeEquiv γ ι := by
    funext x; exact cubeSum_full x
  unfold score switched
  change conditionalAverage
    (observation F (TableRounding.tableEvent S L) ∘ fullCubeEquiv γ ι) cubeSum = _
  rw [he,Projection.conditional_equiv]
  apply congrArg (fun p => p ∘ fullCubeEquiv γ ι)
  exact full_conditional_sum F (TableRounding.tableEvent S L) cubeSum

theorem switched_variance (F : Cube γ → β) (S : β → ι) (L : ι → β → Bool) :
    variance (switched F S L) =
      average (fun x => (conditionalAverage (observation F (TableRounding.tableEvent S L))
        (totalSum (score F)) x)^2) := by
  unfold variance
  rw [switched_score]
  convert average_equiv (fullCubeEquiv γ ι)
    (fun x => (conditionalAverage (observation F (TableRounding.tableEvent S L))
        (totalSum (score F)) x)^2) using 1
  congr 1

theorem switched_variance_scaled (F : Cube γ → β) (S : β → ι) (L : ι → β → Bool)
    (T : Cube γ → ℝ) (k : ℝ) (hT : score F = fun x => k*T x) :
    variance (switched F S L) = k^2*
      average (fun x => (conditionalAverage (observation F (TableRounding.tableEvent S L))
        (totalSum T) x)^2) := by
  rw [switched_variance,hT]
  have he : totalSum (ι := ι) (fun x : Cube γ => k*T x) = fun x => k*totalSum T x := by
    funext x
    simp only [totalSum,oldSum,← Finset.mul_sum]
    ring
  rw [he,Projection.conditional_const_mul]
  simp only [mul_pow,average_const_mul]

end Observations
end SquareRootDegree

end

end OAI
