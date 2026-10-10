import Mathlib

namespace OAI

section
section
noncomputable section
open Set

namespace WeakMTWTransport

lemma convex_barycentric_segment {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype ι] {G : Set E} (hG : Convex ℝ G) (w : ι → ℝ) (v : ι → E)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i,w i=1) (hv : ∀ i,v i∈G)
    (i : ι) {μ : ℝ} (hμ : 0 ≤ μ) (hi : μ ≤ w i) (t : ℝ) (ht : t∈Icc (-μ) 1) :
    (∑ j,w j • v j)+t • (v i-∑ j,w j • v j)∈G := by
  classical
  let a : ι → ℝ := fun j => (1-t)*w j+if j=i then t else 0
  have ha (j : ι) (_hj : j∈Finset.univ) : 0 ≤ a j := by
    dsimp only [a]
    by_cases hj : j=i
    · rw [ite_eq_left hj,hj]
      by_cases h0 : 0 ≤ t
      · exact add_nonneg (mul_nonneg (by linarith [ht.2]) (hw i)) h0
      · have ht0 : t<0 := lt_of_not_ge h0
        nlinarith [mul_nonneg (neg_nonneg.mpr ht0.le) (hμ.trans hi),ht.1]
    · rw [ite_eq_right hj,add_zero]
      exact mul_nonneg (by linarith [ht.2]) (hw j)
  have has : ∑ j,a j=1 := by
    simp only [a,Finset.sum_add_distrib,←Finset.mul_sum,hs,mul_one]
    simp
  have HH := hG.sum_mem (t := Finset.univ) ha has (fun j _ => hv j)
  have he : (∑ j,a j • v j)=(∑ j,w j • v j)+t • (v i-∑ j,w j • v j) := by
    simp only [a,add_smul,mul_smul,Finset.sum_add_distrib,←Finset.smul_sum,
      ite_smul,zero_smul]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    module
  rwa [he] at HH
end WeakMTWTransport

end

end

end

end OAI
