import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarResponseBounds
import OAI.Probability.SKBarriers.Hierarchy.ConstantWeightStats
import OAI.Probability.SKBarriers.Hierarchy.ListPrefixVariance

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic

def blockWeights (κ : ℝ) (c a t : List (ℝ × ℝ)) :
    Fin (zeroWeightChain c++constantWeightChain κ a++zeroWeightChain t).length → ℝ :=
  fun i => if i.val<c.length then 0 else if i.val<c.length+a.length then κ else 0

theorem blockWeights_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (c a t : List (ℝ × ℝ)) :
    ∀ i, 0 ≤ blockWeights κ c a t i := by
  intro i
  unfold blockWeights
  split_ifs <;> positivity

theorem blockWeights_factor (κ : ℝ) (c a t : List (ℝ × ℝ)) :
    ∀ i, ((zeroWeightChain c++constantWeightChain κ a++zeroWeightChain t).get i).2.2=
      blockWeights κ c a t i*((zeroWeightChain c++constantWeightChain κ a++zeroWeightChain t).get i).2.1 := by
  intro i
  simp only [List.get_eq_getElem]
  have hi := i.isLt
  simp only [List.length_append,zeroWeightChain,constantWeightChain,List.length_map] at hi
  by_cases h0 : i.val<c.length
  · have h01 : i.val<c.length+a.length := by omega
    simp only [blockWeights,zero_mul,zeroWeightChain,constantWeightChain,
      List.getElem_append,List.length_append,List.length_map,h01,h0,dite_true,List.getElem_map,ite_true,zero_mul]
  · by_cases h1 : i.val<c.length+a.length
    · simp only [blockWeights,zeroWeightChain,constantWeightChain,
        List.getElem_append,List.length_append,List.length_map,h1,h0,dite_true,dite_false,List.getElem_map,ite_true,ite_false]
    · simp only [blockWeights,zero_mul,zeroWeightChain,constantWeightChain,
        List.getElem_append,List.length_append,List.length_map,h1,h0,dite_false,List.getElem_map,ite_false,zero_mul]

theorem blockWeights_active (κ : ℝ) (c a t : List (ℝ × ℝ)) :
    ∀ i,blockWeights κ c a t i≠0 →
      scalarPrefixVariance (zeroWeightChain c++constantWeightChain κ a++zeroWeightChain t).length
        (fun j => ((zeroWeightChain c++constantWeightChain κ a++zeroWeightChain t).get j).2.1) i.castSucc ≤
      rawVariance (c++a) := by
  intro i hi
  have hcut : i.val<c.length+a.length := by
    by_contra h
    have h' : ¬i.val<c.length := by omega
    simp only [blockWeights,ite_eq_right h',ite_eq_right h] at hi
    exact hi rfl
  let l := zeroWeightChain c++constantWeightChain κ a
  let r := zeroWeightChain t
  have hlen : l.length=c.length+a.length := by simp [l,zeroWeightChain,constantWeightChain]
  have Hcut := scalarPrefixVariance_append_cut l r (fun p => p.2.1)
  have H := scalarPrefixVariance_monotone (l++r).length (fun j => ((l++r).get j).2.1)
    (show i.castSucc≤(⟨l.length,by simp only [List.length_append]; omega⟩ : Fin ((l++r).length+1)) by
      change i.val≤l.length; rw [hlen]; omega)
  rw [Hcut] at H
  have he : (l.map (fun p => p.2.1^2)).sum=rawVariance (c++a) := by
    have heu : weightedUnderlying l=c++a := by
      change weightedUnderlying (zeroWeightChain c++constantWeightChain κ a)=_
      rw [weightedUnderlying_append,weightedUnderlying_zeroWeight,constantWeightChain_underlying]
    rw [← heu]
    simp only [rawVariance,weightedUnderlying,List.map_map,Function.comp_def]
  exact H.trans_eq he

end SK.Analytic

end
end

end OAI
