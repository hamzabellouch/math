import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CardTreeVerticesLe
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.EdgeGraph

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

def fixedIsTagged (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (p : S.Index) (a : ZMod (p : ℕ)) : Prop :=
  (p : ℕ) ∈ listSupport w 𝔏 ∨ ¬ ActiveConnected w hh p a ∨
    ∃ i, (p : ℕ) ∣ w.label i ∧ a + (w.offset i.castSucc : ZMod (p : ℕ)) ≠ 0

@[reducible] def AssignedRecord (S : PrimeSystem) (ℓ : ℕ) :=
  (S.Index → Finset (Fin ℓ)) × (S.Index → Bool)

instance : Fintype (AssignedRecord S ℓ) := inferInstanceAs
  (Fintype ((S.Index → Finset (Fin ℓ)) × (S.Index → Bool)))

def recordAt (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) : AssignedRecord S ℓ :=
  (fun p => if hp : S.IsFixed w p then litEdges w p (a ⟨p,hp⟩) else ∅,
   fun p => if hp : S.IsFixed w p then
     if (treeOccurrences w p).Nonempty then decide (fixedIsTagged w hh 𝔏 p (a ⟨p,hp⟩)) else false
     else false)

def recordGroup (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (R : AssignedRecord S ℓ) (a : S.FixedResidues w) : Prop :=
  recordAt w hh 𝔏 a = R

lemma recordAt_edges (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.FixedIndex w) :
    (recordAt w hh 𝔏 a).1 p.val = litEdges w p.val (a p) := by
  simp only [recordAt, p.property, dite_true]

lemma recordAt_tag (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.FixedIndex w)
    (hp : (treeOccurrences w p.val).Nonempty) :
    (recordAt w hh 𝔏 a).2 p.val = true ↔ fixedIsTagged w hh 𝔏 p.val (a p) := by
  simp only [recordAt,p.property,dite_true,hp,ite_true,decide_eq_true_eq]

lemma recordAt_compatible (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index) :
    (recordAt w hh 𝔏 a).1 p ⊆ treeOccurrences w p := by
  dsimp only [recordAt]
  split_ifs
  · exact litEdges_subset_occurrences w p _
  · exact empty_subset _

lemma recordGroup_edges (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (R : AssignedRecord S ℓ)
    (a : S.FixedResidues w) (ha : recordGroup w hh 𝔏 R a) (p : S.FixedIndex w) :
    litEdges w p.val (a p) = R.1 p.val := by
  rw [← recordAt_edges w hh 𝔏 a p,show recordAt w hh 𝔏 a = R from ha]

theorem assigned_records_partition (w : ClosedLine h ℓ) (hh : 0 < h)
    {T : ℝ} (cut : S.Cutoffs T) (𝔏 : List (AttachedSpec w D L)) :
    (∑ R : AssignedRecord S ℓ, assignedKernelIntegral w cut 𝔏 (recordGroup w hh 𝔏 R)) =
      assignedKernelIntegral w cut 𝔏 (fun _ => True) := by
  unfold assignedKernelIntegral avg
  rw [← mul_sum, sum_comm]
  apply congrArg (fun z : ℝ => (Fintype.card (S.FixedResidues w) : ℝ)⁻¹ * z)
  apply sum_congr rfl
  intro a _
  simp [recordGroup]

def taggedFixedWeight (w : ClosedLine h ℓ) (hh : 0 < h) (p : S.Index)
    (E : Finset (Fin ℓ)) : ℝ :=
  (∏ c ∈ edgeComponents w hh E, subtreeUnionWeight w p (componentEdges w hh E c)) *
    ∏ _e ∈ (treeOccurrences w p) \ E, (2 : ℝ)

lemma taggedFixedWeight_eq (w : ClosedLine h ℓ) (hh : 0 < h) (p : S.Index)
    (E : Finset (Fin ℓ)) : taggedFixedWeight w hh p E = fixedTreeWeight w p E := by
  rw [taggedFixedWeight, ← subtreeUnionWeight_components w hh p E, prod_const]
  rfl

def modifiedWeight (w : ClosedLine h ℓ) (p : S.Index) (E : Finset (Fin ℓ)) : ℝ :=
  if S.IsCore p then subtreeUnionWeight w p E else
    if ∃ e, E = {e} ∧ w.Good e then theta/2 else
      if ∃ e, E = {e} ∧ ¬ w.Good e then subtreeUnionWeight w p E + theta else
        subtreeUnionWeight w p E

lemma modifiedWeight_nonneg (w : ClosedLine h ℓ) (p : S.Index) (E : Finset (Fin ℓ)) :
    0 ≤ modifiedWeight w p E := by
  unfold modifiedWeight
  have hw := subtreeUnionWeight_nonneg w p E
  have ht : 0 ≤ theta := by norm_num
  split_ifs <;> positivity

lemma untagged_fixed_edges (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (p : S.Index) (a : ZMod (p : ℕ))
    (ht : ¬fixedIsTagged w hh 𝔏 p a) : litEdges w p a = treeOccurrences w p := by
  apply filter_eq_self.mpr
  intro i hi
  by_contra hn
  exact ht (Or.inr (Or.inr ⟨i,(mem_filter.mp hi).2,hn⟩))

lemma untagged_fixed_weight_le (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (p : S.FixedIndex w) (a : ZMod (p.val : ℕ))
    (ht : ¬fixedIsTagged w hh 𝔏 p.val a) :
    fixedTreeWeight w p.val (litEdges w p.val a) ≤ modifiedWeight w p.val (litEdges w p.val a) := by
  have hall : ∀ i, (p.val : ℕ) ∣ w.label i → a + (w.offset i.castSucc : ZMod (p.val : ℕ)) = 0 := by
    intro i hi
    by_contra hn
    exact ht (Or.inr (Or.inr ⟨i,hi,hn⟩))
  have hconn : ActiveConnected w hh p.val a := by
    by_contra hn
    exact ht (Or.inr (Or.inl hn))
  have hweight : fixedTreeWeight w p.val (litEdges w p.val a) = subtreeUnionWeight w p.val (litEdges w p.val a) := by
    unfold fixedTreeWeight
    rw [untagged_fixed_edges w hh 𝔏 p.val a ht]
    simp
  rw [hweight,modifiedWeight]
  split_ifs with hc hg hng
  · exact le_rfl
  · obtain ⟨e,hE,he⟩ := hg
    exact False.elim (no_untagged_fixed_center_good_singleton w hh p.val p.property hc a hall hconn e he hE)
  · exact le_add_of_nonneg_right (by norm_num : 0 ≤ theta)
  · exact le_rfl

def recordTreeWeight (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (R : AssignedRecord S ℓ) (p : S.Index) : ℝ :=
  if (treeOccurrences w p).Nonempty then
    if S.IsFixed w p then
      if R.2 p then taggedFixedWeight w hh p (R.1 p) else modifiedWeight w p (R.1 p)
    else freeTreeWeight w 𝔏 p
  else 1

lemma recordTreeWeight_nonneg (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (R : AssignedRecord S ℓ) (p : S.Index) :
    0 ≤ recordTreeWeight w hh 𝔏 R p := by
  unfold recordTreeWeight
  split_ifs
  · rw [taggedFixedWeight_eq]
    exact fixedTreeWeight_nonneg w p _
  · exact modifiedWeight_nonneg w p _
  · exact freeTreeWeight_nonneg w 𝔏 p
  · norm_num

lemma record_tokenPrimeFactor_le (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index) :
    tokenPrimeFactor w 𝔏 (recordAt w hh 𝔏 a).1 p ≤
      (if UsedPrime w 𝔏 p then (p : ℝ)⁻¹ else 1) * recordTreeWeight w hh 𝔏 (recordAt w hh 𝔏 a) p := by
  by_cases ho : (treeOccurrences w p).Nonempty
  · have hused : UsedPrime w 𝔏 p := Or.inl ho
    rw [tokenPrimeFactor,ite_eq_left ho,ite_eq_left hused,recordTreeWeight,ite_eq_left ho]
    by_cases hf : S.IsFixed w p
    · rw [ite_eq_left hf,ite_eq_left hf]
      let pf : S.FixedIndex w := ⟨p,hf⟩
      have he := recordAt_edges w hh 𝔏 a pf
      change (recordAt w hh 𝔏 a).1 p = _ at he
      by_cases ht : (recordAt w hh 𝔏 a).2 p = true
      · rw [ite_eq_left ht,taggedFixedWeight_eq,div_eq_mul_inv,mul_comm]
      · rw [ite_eq_right ht,he,div_eq_mul_inv,mul_comm]
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
        exact untagged_fixed_weight_le w hh 𝔏 pf (a pf)
          (fun htag => ht ((recordAt_tag w hh 𝔏 a pf ho).mpr htag))
    · rw [ite_eq_right hf,ite_eq_right hf,div_eq_mul_inv,mul_comm]
  · rw [tokenPrimeFactor,ite_eq_right ho,recordTreeWeight,ite_eq_right ho,mul_one]
    simp only [UsedPrime,ho,false_or]
    split_ifs <;> exact le_rfl

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
