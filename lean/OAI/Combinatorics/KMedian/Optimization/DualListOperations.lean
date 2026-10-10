import Mathlib
import OAI.Combinatorics.KMedian.Optimization.FractionalDual
import OAI.Combinatorics.KMedian.Optimization.LPListFacts
import OAI.Combinatorics.KMedian.Compression.GaussianListOperations

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Finset

def maximum (xs : Row) : ℚ := xs.foldl max (xs.head?.getD 0)

 theorem maximum_eq_finset (xs : Row) (U : Finset ℚ) (hU : U.Nonempty)
    (hm : ∀ q, q∈xs ↔ q∈U) : maximum xs=U.max' hU := by
  have hne : xs≠[] := by
    intro he
    obtain ⟨q,hq⟩ := hU
    have hx := (hm q).mpr hq
    rw [he] at hx
    cases hx
  have hd : xs.head?.getD 0∈xs := by
    cases xs with
    | nil => contradiction
    | cons a xs => exact List.mem_cons_self
  apply foldl_max_eq
  · exact le_max' U _ ((hm _).mp hd)
  · exact (hm _).mpr (max'_mem U hU)
  · intro q hq
    exact le_max' U q ((hm q).mp hq)

namespace Dual

def candidates (ds : Row) (H : ℚ) : Row := 0::H::ds
def affine (ds ys : Row) (t : ℚ) : ℚ := t-((ds.zip ys).map (fun q => q.2*max 0 (t-q.1))).sum
def value (ds ys : Row) (H : ℚ) : ℚ := maximum ((candidates ds H).map (affine ds ys))
def best (ds ys : Row) (H : ℚ) : ℚ :=
  maximum ((candidates ds H).filter (fun t => decide (affine ds ys t=value ds ys H)))
def gradient (ds ys : Row) (H : ℚ) : Row := ds.map (fun d => -max 0 (best ds ys H-d))

 theorem affine_ofFn {n : ℕ} (d y : Fin n → ℚ) (t : ℚ) :
    affine (List.ofFn d) (List.ofFn y) t=FractionalDual.affine d y t := by
  simp only [affine,Gaussian.ListOperation.zip_ofFn,List.map_ofFn,List.sum_ofFn,FractionalDual.affine]
  rfl

 theorem mem_candidates {n : ℕ} (d : Fin n → ℚ) (H q : ℚ) :
    q∈candidates (List.ofFn d) H ↔ q∈FractionalDual.thresholds d H := by
  simp only [candidates,List.mem_cons,List.mem_ofFn,FractionalDual.thresholds,mem_insert,mem_image,mem_univ,true_and]

 theorem value_ofFn {n : ℕ} (d y : Fin n → ℚ) (H : ℚ) :
    value (List.ofFn d) (List.ofFn y) H=FractionalDual.value d y H := by
  unfold value FractionalDual.value
  apply maximum_eq_finset
  intro q
  simp only [List.mem_map,mem_image,mem_candidates,affine_ofFn]

 theorem best_ofFn {n : ℕ} (d y : Fin n → ℚ) (H : ℚ) :
    best (List.ofFn d) (List.ofFn y) H=FractionalDual.bestThreshold d y H := by
  have hU : ((FractionalDual.thresholds d H).filter (fun t => FractionalDual.affine d y t=FractionalDual.value d y H)).Nonempty := by
    obtain ⟨ht,he⟩ := FractionalDual.bestThreshold_spec d y H
    exact ⟨_,mem_filter.mpr ⟨ht,he⟩⟩
  unfold best FractionalDual.bestThreshold
  rw [dite_eq_left hU]
  apply maximum_eq_finset
  intro q
  simp only [List.mem_filter,mem_filter,decide_eq_true_eq,mem_candidates,affine_ofFn,value_ofFn]

 theorem gradient_ofFn {n : ℕ} (d y : Fin n → ℚ) (H : ℚ) :
    gradient (List.ofFn d) (List.ofFn y) H=List.ofFn (FractionalDual.gradient d y H) := by
  simp only [gradient,best_ofFn,List.map_ofFn]
  rfl
end Dual
end MetricKMedian.LPBinary
end

end OAI
