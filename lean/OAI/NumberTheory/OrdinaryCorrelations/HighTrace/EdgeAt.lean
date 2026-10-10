import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SegmentEdges
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LabelPrimeSetEraseProduct

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ : ℕ}

namespace LineExpression
variable (w : ClosedLine h ℓ) (hl : ∀ i, w.label i ∈ D.members)

def edgeAt (i : ℕ) : ℤ := if hi : i < ℓ then w.sign ⟨i,hi⟩*(h:ℤ)*w.label ⟨i,hi⟩ else 0

def vertexAt (i : ℕ) : ℤ := if hi : i ≤ ℓ then w.offset ⟨i,by omega⟩ else 0

lemma edgeAt_step (i : ℕ) (hi : i < ℓ) :
    edgeAt w i = vertexAt w (i+1)-vertexAt w i := by
  simp only [edgeAt,dite_eq_left hi,vertexAt,dite_eq_left (show i+1 ≤ ℓ by omega),
    dite_eq_left (show i ≤ ℓ by omega)]
  exact (w.step ⟨i,hi⟩).symm

lemma displacement_sum (a b : Fin (ℓ+1)) (hab : a ≤ b) :
    w.offset b-w.offset a = ∑ i ∈ Ico a.val b.val, edgeAt w i := by
  have ha : a.val ≤ ℓ := by omega
  have hb : b.val ≤ ℓ := by omega
  calc
    _ = vertexAt w b.val-vertexAt w a.val := by simp only [vertexAt,dite_eq_left ha,dite_eq_left hb]
    _ = ∑ i ∈ Ico a.val b.val, (vertexAt w (i+1)-vertexAt w i) := (sum_Ico_sub _ hab).symm
    _ = _ := sum_congr rfl (fun i hi => (edgeAt_step w i (by have := mem_Ico.mp hi; omega)).symm)

noncomputable def segment (a b : Fin (ℓ+1)) : SquarefreeExpression S.Index ℓ where
  factors i := labelPrimeSet (w.label i) (hl i)
  coefficient i := if min a.val b.val ≤ i.val ∧ i.val < max a.val b.val then
    (if a ≤ b then 1 else -1)*w.sign i*(h:ℤ) else 0

lemma segment_factor_card (a b : Fin (ℓ+1)) (i : Fin ℓ) :
    ((segment w hl a b).factors i).card ≤ ⌈C₀*Real.log B⌉₊ := by
  rw [segment,labelPrimeSet_card]
  exact D.omega _ (hl i)

lemma segment_support (a b : Fin (ℓ+1)) {p : S.Index}
    (hp : p ∈ (segment w hl a b).support) : (p:ℕ) ∈ w.segmentSupport a b := by
  obtain ⟨i,hi,hp⟩ := mem_biUnion.mp hp
  split_ifs at hp with hc
  · simp at hp
  · have he : min a.val b.val ≤ i.val ∧ i.val < max a.val b.val := by
      by_contra he
      exact hc (by simp only [segment,ite_eq_right he])
    exact mem_biUnion.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,he⟩,(mem_labelPrimeSet (w.label i) (hl i) p).mp hp⟩

lemma segment_eval_factor (a b : Fin (ℓ+1)) :
    (segment w hl a b).eval (fun p => ((p:ℕ):ℤ)) =
      (if a ≤ b then 1 else -1)*∑ i ∈ w.segmentEdges a b, w.sign i*(h:ℤ)*w.label i := by
  unfold SquarefreeExpression.eval
  rw [ClosedLine.segmentEdges,sum_filter,mul_sum]
  apply sum_congr rfl
  intro i hi
  have hp : (∏ p ∈ labelPrimeSet (w.label i) (hl i), ((p:ℕ):ℤ)) = (w.label i:ℤ) := by
    exact_mod_cast labelPrimeSet_product (w.label i) (hl i)
  simp only [segment,hp]
  split_ifs <;> ring

lemma segment_sum (a b : Fin (ℓ+1)) (hab : a ≤ b) :
    ∑ i ∈ w.segmentEdges a b, w.sign i*(h:ℤ)*w.label i = w.offset b-w.offset a := by
  have hab' : a.val ≤ b.val := hab
  unfold ClosedLine.segmentEdges
  simp only [min_eq_left hab',max_eq_right hab',sum_filter]
  have he (i : Fin ℓ) : w.sign i*(h:ℤ)*w.label i = edgeAt w i.val := by
    simp only [edgeAt,dite_eq_left i.isLt]
  simp_rw [he]
  rw [Fin.sum_univ_eq_sum_range (fun n => if a.val ≤ n ∧ n < b.val then edgeAt w n else 0) ℓ,
    ←sum_filter,Specification.range_filter_interval a.val b.val (by omega)]
  exact (displacement_sum w a b hab).symm

lemma segment_eval (a b : Fin (ℓ+1)) :
    (segment w hl a b).eval (fun p => ((p:ℕ):ℤ)) = w.offset b-w.offset a := by
  rw [segment_eval_factor]
  by_cases hab : a ≤ b
  · rw [ite_eq_left hab,one_mul,segment_sum w a b hab]
  · rw [ite_eq_right hab]
    have he : w.segmentEdges a b=w.segmentEdges b a := by
      unfold ClosedLine.segmentEdges
      simp only [min_comm a.val b.val,max_comm a.val b.val]
    rw [he,segment_sum w b a (le_of_not_ge hab)]
    ring

lemma segment_coefficient (a b : Fin (ℓ+1)) (q : S.Index) :
    (segment w hl a b).linearCoeff q (fun p => ((p:ℕ):ℤ)) = w.segmentCoefficient q a b := by
  unfold SquarefreeExpression.linearCoeff ClosedLine.segmentCoefficient
  rw [ClosedLine.segmentEdges,sum_filter,mul_sum]
  apply sum_congr rfl
  intro i hi
  have hq : q ∈ labelPrimeSet (w.label i) (hl i) ↔ (q:ℕ) ∣ w.label i := by
    rw [mem_labelPrimeSet]
    exact ⟨fun hp => (Nat.mem_primeFactors.mp hp).2.1,fun hp =>
      Nat.mem_primeFactors.mpr ⟨S.prime_mem q q.property,hp,(w.label_pos i).ne'⟩⟩
  by_cases hp : q ∈ labelPrimeSet (w.label i) (hl i)
  · have hprod : (∏ p ∈ (labelPrimeSet (w.label i) (hl i)).erase q, ((p:ℕ):ℤ)) =
        ((w.label i/(q:ℕ):ℕ):ℤ) := by
      exact_mod_cast labelPrimeSet_erase_product _ (hl i) q hp
    simp only [segment,hp,ite_true,hprod,ite_eq_left (hq.mp hp)]
    split_ifs <;> ring
  · simp only [segment,hp,ite_false,ite_eq_right (mt hq.mpr hp)]
    split_ifs <;> ring

lemma segment_coeff_bound (a b : Fin (ℓ+1)) (i : Fin ℓ) :
    |((segment w hl a b).coefficient i:ℝ)| ≤ (h:ℝ) := by
  unfold segment
  dsimp only
  split_ifs <;> obtain hs|hs := w.sign_mem i <;> simp [hs]

end LineExpression
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
