import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSquareProbabilityBasic
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeSquareResidueLaw

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryPairSquareProbability

def rmean {α : Type*} [Fintype α] (F : α→ℝ) : ℝ :=
  (Fintype.card α:ℝ)⁻¹*∑x,F x

lemma probability_eq_rmean {α : Type*} [Fintype α] (P : α→Prop) :
    probability P=rmean (fun x => if P x then (1:ℝ) else 0) := by
  simp [probability,rmean,div_eq_mul_inv,mul_comm]

lemma rmean_nonneg {α : Type*} [Fintype α] (F : α→ℝ) (hF : ∀x,0≤F x) :
    0≤rmean F := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun x _ => hF x))

lemma rmean_mono {α : Type*} [Fintype α] (F H : α→ℝ) (h : ∀x,F x≤H x) :
    rmean F≤rmean H := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => h x))
      (inv_nonneg.mpr (Nat.cast_nonneg _))

lemma rmean_sub {α : Type*} [Fintype α] (F H : α→ℝ) :
    rmean (fun x => F x-H x)=rmean F-rmean H := by
  simp only [rmean,Finset.sum_sub_distrib,mul_sub]

lemma rmean_mul_left {α : Type*} [Fintype α] (c : ℝ) (F : α→ℝ) :
    rmean (fun x => c*F x)=c*rmean F := by
  simp only [rmean,←Finset.mul_sum]
  ring

lemma rmean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α≃β) (F : β→ℝ) : rmean (fun x => F (e x))=rmean F := by
  unfold rmean
  rw [Fintype.card_congr e,e.sum_comp]

lemma rmean_prod {α β : Type*} [Fintype α] [Fintype β] (F : α×β→ℝ) :
    rmean F=rmean (fun a => rmean (fun b => F (a,b))) := by
  simp only [rmean,Fintype.card_prod,Nat.cast_mul,mul_inv_rev,
    Fintype.sum_prod_type,←Finset.mul_sum]
  ring

theorem base_average_lift_loss {ι α : Type*} [Fintype α]
    (p : ℕ) [Fact p.Prime] (s : Finset ι) (A B : ι→ℤ) (X Y : α→ℤ)
    (hrow : ∀i∈s,(A i:ZMod p)≠0 ∨ (B i:ZMod p)≠0) :
    0≤probability (fun a => Base p s A B (X a) (Y a))-
      rmean (fun a => probability (fun z : ZMod p×ZMod p =>
        Good p s A B (X a+(p:ℤ)*(z.1.val:ℤ)) (Y a+(p:ℤ)*(z.2.val:ℤ)))) ∧
    probability (fun a => Base p s A B (X a) (Y a))-
      rmean (fun a => probability (fun z : ZMod p×ZMod p =>
        Good p s A B (X a+(p:ℤ)*(z.1.val:ℤ)) (Y a+(p:ℤ)*(z.2.val:ℤ))))≤
      ((s.card:ℝ)/p)*probability (fun a => Base p s A B (X a) (Y a)) := by
  rw [probability_eq_rmean,←rmean_sub]
  constructor
  · apply rmean_nonneg
    intro a
    exact (conditional_lift_loss p s A B (X a) (Y a) hrow).1
  · rw [←rmean_mul_left]
    apply rmean_mono
    intro a
    exact (conditional_lift_loss p s A B (X a) (Y a) hrow).2

end Ostmann.Arithmetic.HistoryPairSquareProbability

end

end OAI
