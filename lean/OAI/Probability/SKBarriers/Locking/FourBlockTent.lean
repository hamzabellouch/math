import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.ConstantWeightStats
import OAI.Probability.SKBarriers.Scalar.ScalarTentGeometry
import OAI.Probability.SKBarriers.Hierarchy.ListPrefixTake

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic

abbrev fourBlockTent (κ : ℝ) (b l j k : List (ℝ × ℝ)) : List (ℝ × (ℝ × ℝ)) :=
  (zeroWeightChain b++constantWeightChain κ l)++(constantWeightChain (-κ) j++zeroWeightChain k)

@[simp] theorem fourBlockTent_length (κ : ℝ) (b l j k : List (ℝ × ℝ)) :
    (fourBlockTent κ b l j k).length=b.length+l.length+j.length+k.length := by
  simp only [fourBlockTent,zeroWeightChain,constantWeightChain,List.length_append,List.length_map]
  omega

abbrev fourBlockLeft (κ : ℝ) (b l j k : List (ℝ × ℝ)) : Fin ((fourBlockTent κ b l j k).length+1) :=
  ⟨b.length,by rw [fourBlockTent_length]; omega⟩
abbrev fourBlockMiddle (κ : ℝ) (b l j k : List (ℝ × ℝ)) : Fin ((fourBlockTent κ b l j k).length+1) :=
  ⟨b.length+l.length,by rw [fourBlockTent_length]; omega⟩
abbrev fourBlockRight (κ : ℝ) (b l j k : List (ℝ × ℝ)) : Fin ((fourBlockTent κ b l j k).length+1) :=
  ⟨b.length+l.length+j.length,by rw [fourBlockTent_length]; omega⟩

theorem fourBlockTent_vector {κ d : ℝ} (hd : d≠0) (hκ : κ*d=1) (b l j k : List (ℝ × ℝ)) :
    (fun i => ((fourBlockTent κ b l j k).get i).2.2)=
      scalarTentVector (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).2.1)
        (fourBlockLeft κ b l j k) (fourBlockMiddle κ b l j k) (fourBlockRight κ b l j k) d := by
  funext i
  simp only [List.get_eq_getElem]
  have hfactor : κ=1/d := (eq_div_iff hd).mpr hκ
  unfold scalarTentVector scalarPrefixVector
  simp only []
  by_cases hb : i.val<b.length
  · have hbl : i.val<b.length+l.length := by omega
    have hblj : i.val<b.length+l.length+j.length := by omega
    simp only [hb,hbl,hblj,ite_true]
    simp only [fourBlockTent,zeroWeightChain,constantWeightChain,List.getElem_append,
      List.length_append,List.length_map,hbl,hb,dite_true,List.getElem_map]
    ring
  · by_cases hl : i.val<b.length+l.length
    · have hblj : i.val<b.length+l.length+j.length := by omega
      have hil : i.val-b.length<l.length := by omega
      simp only [hb,hl,hblj,ite_true,ite_false]
      simp only [fourBlockTent,zeroWeightChain,constantWeightChain,List.getElem_append,
        List.length_append,List.length_map,hl,hb,dite_true,dite_false,List.getElem_map]
      apply (eq_div_iff hd).mpr
      linear_combination l[i.val-b.length].2*hκ
    · by_cases hj : i.val<b.length+l.length+j.length
      · have hij : i.val-(b.length+l.length)<j.length := by omega
        simp only [hb,hl,hj,ite_true,ite_false]
        simp only [fourBlockTent,zeroWeightChain,constantWeightChain,List.getElem_append,
          List.length_append,List.length_map,hl,hb,hij,dite_true,dite_false,List.getElem_map]
        apply (eq_div_iff hd).mpr
        linear_combination -j[i.val-(b.length+l.length)].2*hκ
      · have hij : ¬i.val-(b.length+l.length)<j.length := by omega
        simp only [hb,hl,hj,ite_false]
        simp only [fourBlockTent,zeroWeightChain,constantWeightChain,List.getElem_append,
          List.length_append,List.length_map,hl,hb,hij,dite_false,List.getElem_map]
        ring

theorem fourBlockTent_left_variance (κ : ℝ) (b l j k : List (ℝ × ℝ)) :
    scalarPrefixVariance (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).2.1)
      (fourBlockLeft κ b l j k)=rawVariance b := by
  rw [scalarPrefixVariance_list (fourBlockTent κ b l j k) (fun p => p.2.1)]
  simp only [fourBlockTent,zeroWeightChain,constantWeightChain,rawVariance,
    List.take_append,← List.map_take,List.length_map,List.map_append,List.sum_append,List.map_map,Function.comp_def]
  simp (disch := (simp only [List.length_map]; omega)) [Nat.sub_eq_zero_of_le (show b.length≤b.length+l.length by omega)]

theorem fourBlockTent_middle_variance (κ : ℝ) (b l j k : List (ℝ × ℝ)) :
    scalarPrefixVariance (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).2.1)
      (fourBlockMiddle κ b l j k)=rawVariance b+rawVariance l := by
  rw [scalarPrefixVariance_list (fourBlockTent κ b l j k) (fun p => p.2.1)]
  simp only [fourBlockTent,zeroWeightChain,constantWeightChain,rawVariance,
    List.take_append,← List.map_take,List.length_map,List.map_append,List.sum_append,List.map_map,Function.comp_def]
  simp (disch := (simp only [List.length_map]; omega)) [List.take_of_length_le]

theorem fourBlockTent_right_variance (κ : ℝ) (b l j k : List (ℝ × ℝ)) :
    scalarPrefixVariance (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).2.1)
      (fourBlockRight κ b l j k)=rawVariance b+rawVariance l+rawVariance j := by
  rw [scalarPrefixVariance_list (fourBlockTent κ b l j k) (fun p => p.2.1)]
  simp only [fourBlockTent,zeroWeightChain,constantWeightChain,rawVariance,
    List.take_append,← List.map_take,List.length_map,List.map_append,List.sum_append,List.map_map,Function.comp_def]
  simp (disch := (simp only [List.length_map]; omega)) [List.take_of_length_le]

end SK.Analytic

end
end

end OAI
