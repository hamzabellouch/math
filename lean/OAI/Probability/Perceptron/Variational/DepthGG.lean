import Mathlib
import OAI.Probability.Perceptron.Variational.DepthBlock

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology
namespace SphericalPerceptronFreeEnergy

lemma depth_block_row_threshold (k r d : ℕ)
    (μ : Measure (FiniteOverlap (Fin (k+1)))) (A : FiniteBlock (Fin (k+1)) r)
    (i j : Fin r) :
    μ.real {R | finiteBlock r R = A ∧ d ≤ (R i j).val} =
      μ.real {R | finiteBlock r R = A} * (if d ≤ (A i j).val then 1 else 0) := by
  have he (R : FiniteOverlap (Fin (k+1))) (hR : finiteBlock r R = A) : R i j = A i j :=
    congrFun (congrFun hR i) j
  by_cases hd : d ≤ (A i j).val
  · rw [ite_eq_left hd,mul_one]
    congr 1
    ext R
    constructor
    · exact And.left
    · intro hR
      exact ⟨hR,by rw [he R hR]; exact hd⟩
  · rw [ite_eq_right hd,mul_zero]
    have hEmpty : {R : FiniteOverlap (Fin (k+1)) | finiteBlock r R = A ∧ d ≤ (R i j).val} = ∅ := by
      ext R
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false,not_and]
      intro hR hD
      exact hd (by simpa only [he R hR] using hD)
    rw [hEmpty,measureReal_empty]

lemma indexedDepthLaw_block_zero_of_diagonal (k r : ℕ) (z : Fin k → ℝ)
    (A : FiniteBlock (Fin (k+1)) r) (i : Fin r) (hA : A i i ≠ Fin.last k) :
    (indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1)))).real
      {R | finiteBlock r R = A} = 0 := by
  convert measureReal_empty (μ := (indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1))))) using 1
  apply measureReal_congr
  filter_upwards [indexedDepthLaw_geometry k z] with R hR
  change (finiteBlock r R = A) = False
  apply propext
  simp only [iff_false]
  intro hB
  have he : R i i = A i i := congrFun (congrFun hB i) i
  exact hA (he.symm.trans (hR.2.1 i))

lemma indexedDepthLaw_focused_formula_real (k : ℕ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (r d : ℕ) (hd : d ≤ k) (A : FiniteBlock (Fin (k+1)) r) (i : Fin r)
    (hA : A i i = Fin.last k) :
    (indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1)))).real
      {R | finiteBlock r R = A ∧ d ≤ (R i r).val} =
      (indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1)))).real {R | finiteBlock r R = A} *
        (((∑ j, if d ≤ (A i j).val then (1:ℝ) else 0) -
          (if h : d = 0 then 0 else z ⟨d-1,by omega⟩)) / r) := by
  have hb : (if h : d = 0 then (0:ℝ) else z ⟨d-1,by omega⟩) ≤ 1 := by
    split_ifs
    · norm_num
    · exact (hz1 _).le
  have hc : (1:ℝ) ≤ ∑ j, if d ≤ (A i j).val then (1:ℝ) else 0 := by
    have he := Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin r => if d ≤ (A i j).val then (1:ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
    simpa only [hA,Fin.val_last,ite_eq_left hd] using he
  have hn : 0 ≤ ((∑ j, if d ≤ (A i j).val then (1:ℝ) else 0) -
      (if h : d = 0 then (0:ℝ) else z ⟨d-1,by omega⟩)) / r :=
    div_nonneg (sub_nonneg.mpr (hb.trans hc)) (Nat.cast_nonneg _)
  have he := congrArg ENNReal.toReal (indexedDepthLaw_focused_formula k z hz hz0 hz1 r d hd A i)
  simpa only [measureReal_def,ENNReal.toReal_mul,ENNReal.toReal_ofReal hn] using he

lemma indexedDepthLaw_pair_tail_real (k : ℕ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (d : ℕ) (hd : d ≤ k) :
    (indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1)))).real {R | d ≤ (R 0 1).val} =
      1 - (if h : d = 0 then 0 else z ⟨d-1,by omega⟩) := by
  have hb : (if h : d = 0 then (0:ℝ) else z ⟨d-1,by omega⟩) ≤ 1 := by
    split_ifs
    · norm_num
    · exact (hz1 _).le
  have he := congrArg ENNReal.toReal (indexedDepthLaw_pair_tail k z hz hz0 hz1 d hd)
  simpa only [measureReal_def,ENNReal.toReal_ofReal (sub_nonneg.mpr hb)] using he

theorem indexedDepthLaw_finiteGG (k : ℕ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) :
    FiniteGG (indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1)))) := by
  apply finiteGG_of_depth_thresholds
  intro r _hr i A d hd
  let μ := (indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1))))
  change μ.real {R | finiteBlock r R = A ∧ d ≤ (R i r).val} =
    μ.real {R | finiteBlock r R = A} * μ.real {R | d ≤ (R 0 1).val} / r +
      (∑ j ∈ Finset.univ.erase i, μ.real {R | finiteBlock r R = A ∧ d ≤ (R i j).val}) / r
  by_cases hdk : d ≤ k
  · by_cases hA : A i i = Fin.last k
    · have he := indexedDepthLaw_focused_formula_real k z hz hz0 hz1 r d hdk A i hA
      have hp := indexedDepthLaw_pair_tail_real k z hz hz0 hz1 d hdk
      change μ.real _ = μ.real _ * _ at he
      change μ.real _ = _ at hp
      rw [he,hp]
      simp_rw [depth_block_row_threshold k r d μ A i]
      rw [← Finset.mul_sum,Finset.sum_erase_eq_sub (Finset.mem_univ i)]
      simp only [hA,Fin.val_last,ite_eq_left hdk]
      ring
    · have hB := indexedDepthLaw_block_zero_of_diagonal k r z A i hA
      change μ.real _ = 0 at hB
      have hF : μ.real {R | finiteBlock r R = A ∧ d ≤ (R i r).val} = 0 :=
        measureReal_mono_null (fun _ h => h.1) hB
      rw [hF,hB]
      simp_rw [depth_block_row_threshold k r d μ A i,hB,zero_mul]
      simp
  · have he : d = k+1 := by omega
    subst d
    have hfalse (l : Fin (k+1)) : ¬ k+1 ≤ l.val := Nat.not_le.mpr l.isLt
    simp only [hfalse,and_false]
    simp

end SphericalPerceptronFreeEnergy

end

end OAI
