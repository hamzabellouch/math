import Mathlib
import OAI.Probability.SKGap.Matrix.WordExpectedRecursion

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators SchwartzMap

lemma finite_cost_bound (g : ℕ→ℕ→ℕ→ℝ) (L : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ u≤L,∀ v≤L,∀ q≤L,g u v q≤C := by
  let C := ∑ u∈Finset.range (L+1),∑ v∈Finset.range (L+1),∑ q∈Finset.range (L+1),|g u v q|
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro u hu v hv q hq
  calc
    g u v q ≤ |g u v q| := le_abs_self _
    _ ≤ ∑ r∈Finset.range (L+1),|g u v r| := Finset.single_le_sum (f := fun r => |g u v r|) (fun _ _=>abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))
    _ ≤ ∑ w∈Finset.range (L+1),∑ r∈Finset.range (L+1),|g u w r| := Finset.single_le_sum (f := fun w => ∑ r∈Finset.range (L+1),|g u w r|) (fun w _=>Finset.sum_nonneg (fun r _=>abs_nonneg (g u w r))) (Finset.mem_range.mpr (Nat.lt_succ_of_le hv))
    _ ≤ C := by
      dsimp only [C]
      exact Finset.single_le_sum (f := fun w => ∑ v∈Finset.range (L+1),∑ r∈Finset.range (L+1),|g w v r|) (fun w _=>Finset.sum_nonneg (fun v _=>Finset.sum_nonneg (fun r _=>abs_nonneg (g w v r)))) (Finset.mem_range.mpr (Nat.lt_succ_of_le hu))

lemma continuous_wordMarkedCost (B : NNReal) (j R A c : ℝ) (p q : ℕ) :
    Continuous (fun z=>wordMarkedCost B j R A c z p q) := by
  unfold wordMarkedCost markedRateConstant wordDifferentialBound
  fun_prop

lemma wordMarkedCost_uniform (B : NNReal) (j R A c : ℝ) (L : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ z∈Icc (0:ℝ) 1,∀ p≤L,∀ q≤L,
      wordMarkedCost B j R A c z p q≤C := by
  let H : ℝ→ℝ := fun z=>∑ p∈Finset.range (L+1),∑ q∈Finset.range (L+1),|wordMarkedCost B j R A c z p q|
  have hH : Continuous H := by
    unfold H
    exact continuous_finsetSum _ (fun p _=>continuous_finsetSum _ (fun q _=>(continuous_wordMarkedCost B j R A c p q).abs))
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hH.continuousOn
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro z hz p hp q hq
  have hb : wordMarkedCost B j R A c z p q≤H z := by
    calc
      _ ≤ |wordMarkedCost B j R A c z p q| := le_abs_self _
      _ ≤ ∑ r∈Finset.range (L+1),|wordMarkedCost B j R A c z p r| :=
        Finset.single_le_sum (f := fun r=>|wordMarkedCost B j R A c z p r|) (fun _ _=>abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))
      _ ≤ H z := by
        dsimp only [H]
        exact Finset.single_le_sum (f := fun w=>∑ r∈Finset.range (L+1),|wordMarkedCost B j R A c z w r|) (fun w _=>Finset.sum_nonneg (fun r _=>abs_nonneg (wordMarkedCost B j R A c z w r)))
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hp))
  have hbH : |H z|≤C := hC z hz
  exact hb.trans ((le_abs_self _).trans (hbH.trans (le_max_right _ _)))

variable {ι : Type*}
lemma wordPartners_length_sides (a : ι→ℝ) (F : List (WordLetter ι)) (c : WordCut ι)
    (hc : c∈wordPartners a F) : c.left.length≤F.length+1 ∧ c.right.length≤F.length+1 := by
  have hh := wordPartners_lengths a F c hc
  cases hi : c.inversePartner
  · simp only [hi,Bool.false_eq_true,ite_false] at hh
    omega
  · have hs := wordPartners_inverse_sides a F c hc hi
    have hL : inverseCount c.left≤c.left.length := List.countP_le_length
    have hR : inverseCount c.right≤c.right.length := List.countP_le_length
    simp only [hi,ite_true] at hh
    omega

lemma wordRecursionAtCost_uniform {j B z C : ℝ} (hz : z∈Icc (0:ℝ) 1)
    (hC : 0≤C) (L : ℕ) (hc : ∀ u≤L,∀ v≤L,∀ q≤L,wordLeadingCost j B u v q≤C)
    (a : ι→ℝ) (P Q : List (WordLetter ι)) (hP : P.length+1+Q.length≤L) :
    wordRecursionAtCost j B z a P Q≤(L:ℝ)*C := by
  have hp : P.length≤L := by omega
  have hq : Q.length≤L := by omega
  have hz' (b : Bool) : |if b then z else 1|≤1 := by
    split
    · rw [abs_of_nonneg hz.1];exact hz.2
    · simp
  have hl (c : WordCut ι) (h : c∈wordPartners a P) :
      |if c.inversePartner then z else 1| *wordLeadingCost j B c.left.length c.right.length Q.length≤C := by
    have hb := wordPartners_length_sides a P c h
    have hcost := hc c.left.length (by omega) c.right.length (by omega) Q.length hq
    have hh := mul_le_mul_of_nonneg_left hcost (abs_nonneg (if c.inversePartner then z else 1))
    exact hh.trans ((mul_le_mul_of_nonneg_right (hz' _) hC).trans_eq (one_mul C))
  have hr (c : WordCut ι) (h : c∈wordPartners a Q) :
      |if c.inversePartner then z else 1| *wordLeadingCost j B P.length c.left.length c.right.length≤C := by
    have hb := wordPartners_length_sides a Q c h
    have hcost := hc P.length hp c.left.length (by omega) c.right.length (by omega)
    exact (mul_le_mul_of_nonneg_left hcost (abs_nonneg (if c.inversePartner then z else 1))).trans
      ((mul_le_mul_of_nonneg_right (hz' _) hC).trans_eq (one_mul C))
  have hb (X : List (WordCut ι)) (f : WordCut ι→ℝ) (hf : ∀ x∈X,f x≤C) :
      (X.map f).sum≤(X.length:ℝ)*C := by
    induction X with
    | nil => simp
    | cons x X ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      exact (add_le_add (hf x List.mem_cons_self) (ih (fun x hx=>hf x (List.mem_cons_of_mem _ hx)))).trans_eq (by ring)
  have hsum := add_le_add (hb _ _ hl) (hb _ _ hr)
  have hlen : ((wordPartners a P).length:ℝ)+(wordPartners a Q).length≤L := by
    exact_mod_cast (show (wordPartners a P).length+(wordPartners a Q).length≤L by
      have hh1 := wordPartners_card_bound a P
      have hh2 := wordPartners_card_bound a Q
      omega)
  apply hsum.trans
  nlinarith [mul_nonneg hC (sub_nonneg.mpr hlen)]
end SKGap
end
end

end OAI
