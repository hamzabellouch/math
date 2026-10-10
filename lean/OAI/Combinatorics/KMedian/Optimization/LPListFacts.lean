import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryPredicates
import OAI.Combinatorics.KMedian.Binary.BinaryListSelection

namespace OAI


                                   
section
namespace MetricKMedian.LPBinary
open Finset
abbrev Row := List ℚ
abbrev Rows := List Row
abbrev er := Binary.encodeList Binary.Ratio.encode
abbrev ers := Binary.encodeList er

 theorem foldl_max_le {α : Type} [LinearOrder α] (xs : List α) (a b : α)
    (ha : a ≤ b) (hx : ∀ x∈xs, x≤b) : xs.foldl max a ≤ b := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
      exact ih (max a x) (max_le ha (hx x List.mem_cons_self)) (fun y hy => hx y (List.mem_cons_of_mem _ hy))

 theorem le_foldl_max {α : Type} [LinearOrder α] (xs : List α) (a : α) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_left a x).trans (ih (max a x))

 theorem member_le_foldl_max {α : Type} [LinearOrder α] (xs : List α) (a b : α) (hb : b∈xs) : b ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => cases hb
  | cons x xs ih =>
      rcases List.mem_cons.mp hb with rfl|hb
      · exact (le_max_right a b).trans (le_foldl_max xs (max a b))
      · exact ih (max a x) hb

 theorem foldl_max_eq {α : Type} [LinearOrder α] (xs : List α) (a b : α)
    (ha : a ≤ b) (hb : b∈xs) (hx : ∀ x∈xs, x≤b) : xs.foldl max a=b :=
  le_antisymm (foldl_max_le xs a b ha hx) (member_le_foldl_max xs a b hb)

 theorem sum_filter_ofFn (n : ℕ) (f : Fin n → ℚ) (p : ℚ → Bool) :
    ((List.ofFn f).filter p).sum=∑ i∈univ.filter (fun i => p (f i)), f i := by
  rw [Finset.sum_filter]
  have he : ((List.ofFn f).filter p).sum=((List.ofFn f).map (fun a => if p a then a else 0)).sum := by
    generalize List.ofFn f=xs
    induction xs with
    | nil => rfl
    | cons a xs ih => cases h : p a <;> simp [h,ih]
  rw [he,List.map_ofFn,List.sum_ofFn]
  rfl

 theorem length_filter_ofFn (n : ℕ) (f : Fin n → ℚ) (p : ℚ → Bool) :
    ((List.ofFn f).filter p).length=(univ.filter (fun i => p (f i))).card := by
  have he : ((List.ofFn f).filter p).length=((List.ofFn f).map (fun a => if p a then (1:ℕ) else 0)).sum := by
    generalize List.ofFn f=xs
    induction xs with
    | nil => rfl
    | cons a xs ih => cases h : p a <;> simp [h,ih,Nat.add_comm]
  rw [he,List.map_ofFn,List.sum_ofFn]
  simp

namespace Program
open Binary Binary.PolyProgram
noncomputable def ratMax : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => max x.1 x.2) :=
  (ite ratLE (fst Ratio.encode Ratio.encode) (snd Ratio.encode Ratio.encode)).congr _ (fun x => by
    by_cases h : x.1≤x.2
    · simp [h]
    · simp [h,max_eq_left (le_of_not_ge h)])
noncomputable def ratMin : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => min x.1 x.2) :=
  (ite ratLE (snd Ratio.encode Ratio.encode) (fst Ratio.encode Ratio.encode)).congr _ (fun x => by
    by_cases h : x.1≤x.2
    · simp [h]
    · simp [h,min_eq_right (le_of_not_ge h)])
noncomputable def maxFold : PolyProgram (encodePair er Ratio.encode) Ratio.encode (fun x : Row × ℚ => x.1.foldl max x.2) :=
  (listChoose ratLT 0).congr _ (fun x => by
    congr 1
    funext a b
    by_cases h : a<b
    · simp [h,max_eq_right h.le]
    · simp [h,max_eq_left (le_of_not_gt h)])
end Program
end MetricKMedian.LPBinary
end

end OAI
