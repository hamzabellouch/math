import OAI.NumberTheory.DirichletL.PrimeRows.SmallPartition

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

theorem nonprincipal_rows_partition (L U : ℝ) (hL : 1≤L) (hLU : L≤U)
    (f : FreeRow→ℂ) (hf : Summable f) :
    (∑'u : FreeRow,if u.val=1 then 0 else f u)=
      (∑n∈smallDyadicIndices L,∑u∈smallDyadicRows L n,f u)+
        (∑u∈rowBand L U,f u)+(∑'n : ℕ,∑u∈dyadicRows U n,f u) := by
  let g1 := (↑(rowBand 1 L):Set FreeRow).indicator f
  let g2 := (↑(rowBand L U):Set FreeRow).indicator f
  let g3 := {u : FreeRow | u.val≠1 ∧ U≤rowNorm u}.indicator f
  have hg1 : Summable g1 := hf.indicator _
  have hg2 : Summable g2 := hf.indicator _
  have hg3 : Summable g3 := hf.indicator _
  have hpoint (u : FreeRow) : (if u.val=1 then 0 else f u)=g1 u+g2 u+g3 u := by
    have hnorm := rowNorm_ge_one u
    by_cases hu : u.val=1
    · simp [g1,g2,g3,mem_rowBand,hu]
    · by_cases hsmall : rowNorm u<L
      · have hU : ¬U≤rowNorm u := not_le.mpr (hsmall.trans_le hLU)
        have hL' : ¬L≤rowNorm u := not_le.mpr hsmall
        simp [g1,g2,g3,mem_rowBand,hu,hnorm,hsmall,hL',hU]
      · have hL' : L≤rowNorm u := le_of_not_gt hsmall
        by_cases hlarge : U≤rowNorm u
        · have hU : ¬rowNorm u<U := not_lt.mpr hlarge
          simp [g1,g2,g3,mem_rowBand,hu,hnorm,hsmall,hL',hlarge,hU]
        · have hU : rowNorm u<U := lt_of_not_ge hlarge
          simp [g1,g2,g3,mem_rowBand,hu,hnorm,hsmall,hL',hlarge,hU]
  have hsum1 : (∑'u,g1 u)=∑u∈rowBand 1 L,f u := by
    rw [tsum_eq_sum (s:=rowBand 1 L) (fun u hu=>Set.indicator_of_notMem hu f)]
    apply Finset.sum_congr rfl
    intro u hu
    exact Set.indicator_of_mem hu f
  have hsum2 : (∑'u,g2 u)=∑u∈rowBand L U,f u := by
    rw [tsum_eq_sum (s:=rowBand L U) (fun u hu=>Set.indicator_of_notMem hu f)]
    apply Finset.sum_congr rfl
    intro u hu
    exact Set.indicator_of_mem hu f
  have hsum3 : (∑'u,g3 u)=∑'n : ℕ,∑u∈dyadicRows U n,f u := by
    have hh := (tsum_dyadicRows U (by linarith) f hf).2
    convert hh using 1
    apply tsum_congr
    intro u
    by_cases h : u.val≠1 ∧ U≤rowNorm u <;> simp [g3,h]
  simp_rw [hpoint]
  rw [(hg1.add hg2).tsum_add hg3,hg1.tsum_add hg2,hsum1,hsum2,hsum3,sum_small_dyadicRows]

end SevenEighths.ProbeHighRowFamily

end

end OAI
