import OAI.Analysis.Triangular.Construction.FiniteAssembly
import OAI.Analysis.Triangular.Construction.FinitePairBridge
import OAI.Analysis.Triangular.Construction.FiniteRemainder

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma finiteJ_remainder (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) (n : Fin 7) {v : ℝ}
    (hv : |v|≤nearRadius n) :
    ‖complexError (fun k s => finiteJJet side (actualParameter z) k s) (nearNode n) v‖ <
      (if n.val=0 then (161/100000:ℝ) else 75/10000000) := by
  obtain ⟨c,_,hc⟩ := Finset.exists_max_image Finset.univ (rawRemainderColumn 0 n) Finset.univ_nonempty
  obtain ⟨d,_,hd⟩ := Finset.exists_max_image Finset.univ (rawRemainderColumn 1 n) Finset.univ_nonempty
  have h0 := finite_input_error ((gamma side *ᵥ actualParameter z) 2) (finiteApprox side (actualParameter z)) 0 n hv (fun i => hc i (Finset.mem_univ i))
  have h1 := finite_input_error ((gamma (otherSide side) *ᵥ actualParameter z) 2) (finiteApprox (otherSide side) (actualParameter z)) 1 n hv (fun i => hd i (Finset.mem_univ i))
  have hg (side : Fin 2) : |(gamma side *ᵥ actualParameter z) 2|=6/1000 := by
    rw [gamma_actual]
    change |(if side.val=0 then -(3/500:ℝ) else 3/500)|=6/1000
    fin_cases side <;> norm_num
  rw [hg] at h0 h1
  have ha := mul_le_mul_of_nonneg_right (finiteApprox_norm side (actualParameter z) (actualParameter_mem hz hzB)).le (rawRemainderColumn_nonneg 0 n c)
  have hb := mul_le_mul_of_nonneg_right (finiteApprox_norm (otherSide side) (actualParameter z) (actualParameter_mem hz hzB)).le (rawRemainderColumn_nonneg 1 n d)
  simp only [finiteJJet_pair,pairJJet]
  rw [complexError_add]
  have hh := norm_add_le
    (complexError (fun k s => inputJJet (coefficientInput ((gamma side *ᵥ actualParameter z) 2) (finiteApprox side (actualParameter z)) 0) 0 k s) (nearNode n) v)
    (complexError (fun k s => inputJJet (coefficientInput ((gamma (otherSide side) *ᵥ actualParameter z) 2) (finiteApprox (otherSide side) (actualParameter z)) 0) 1 k s) (nearNode n) v)
  have htab := remainder_table n c d
  linarith
lemma complexDeleted_finiteJ (side : Fin 2) (e : Fin 8 → ℝ) (m v : ℝ) :
    (complexDeleted (fun k s => finiteJJet side e k s) m v).re=deletedSecond (finiteJ side e) m (m+v) := by
  apply complexDeleted_re
  · intro s; rfl
  · simpa only [iteratedDeriv_one] using congrFun (finiteJJet_re_iterated side e 1) m
  · exact congrFun (finiteJJet_re_iterated side e 2) m
lemma complexTaylor_finiteJ (side : Fin 2) (e : Fin 8 → ℝ) (m : ℤ) (y τ : ℝ) :
    (complexTaylor (fun k s => finiteJJet side e k s) m (y*τ)).re=finiteTaylor side m y e τ := by
  rw [finiteTaylor_exact]
  simp only [complexTaylor,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [←Complex.ofReal_natCast,Complex.div_ofReal_re,←Complex.ofReal_pow,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rw [congrFun (finiteJJet_re_iterated side e (j+2)) m,mul_pow]
  ring
lemma finiteTaylor_error (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) (n : Fin 7) {y τ : ℝ}
    (hv : |y*τ|≤nearRadius n) :
    |deletedSecond (finiteJ side (actualParameter z)) (nearNode n) (nearNode n+y*τ)-finiteTaylor side (nearNode n) y (actualParameter z) τ| <
      (if n.val=0 then (161/100000:ℝ) else 75/10000000) := by
  rw [←complexDeleted_finiteJ,←complexTaylor_finiteJ,←Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans_lt (finiteJ_remainder side hz hzB n hv)
end AtomicTriangular.Construction
end

end OAI
