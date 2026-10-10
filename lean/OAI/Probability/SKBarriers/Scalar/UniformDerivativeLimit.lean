import Mathlib
import OAI.Probability.SKBarriers.Scalar.DerivativeStability

namespace OAI

section

noncomputable section
open scoped Topology NNReal
open Filter Set
namespace SK.Analytic

theorem geometric_uniform_limit {X : Type*} (F : ℕ → X → ℝ) {C r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1)
    (hF : ∀ n x, |F (n+1) x-F n x| ≤ C*r^n) :
    TendstoUniformly F (fun x => limUnder atTop (fun n => F n x)) atTop ∧
      ∀ n x, |F n x-limUnder atTop (fun k => F k x)| ≤ C*r^n/(1-r) := by
  have hs : Summable (fun n : ℕ => C*r^n) := (summable_geometric_of_lt_one hr hr1).mul_left C
  have hd (n : ℕ) (x : X) : dist (F n x) (F (n+1) x) ≤ C*r^n := by
    simpa only [Real.dist_eq,abs_sub_comm] using hF n x
  have ht (x : X) : Tendsto (fun n => F n x) atTop (𝓝 (limUnder atTop (fun n => F n x))) :=
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete
      (cauchySeq_of_dist_le_of_summable _ (fun n => hd n x) hs))
  have hb (n : ℕ) (x : X) : |F n x-limUnder atTop (fun k => F k x)| ≤ C*r^n/(1-r) := by
    have H := dist_le_tsum_of_dist_le_of_tendsto _ (fun k => hd k x) hs (ht x) n
    have he : (∑' k : ℕ, C*r^(n+k))=C*r^n/(1-r) := by
      simp only [pow_add,← mul_assoc,tsum_mul_left,tsum_geometric_of_lt_one hr hr1,div_eq_mul_inv]
    simpa only [Real.dist_eq,he] using H
  refine ⟨?_,hb⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => C*r^n/(1-r)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).const_mul C).div_const (1-r)
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with n hn x
  rw [Real.dist_eq,abs_sub_comm]
  exact (hb n x).trans_lt hn

theorem uniformCauchySeq_derivative {F D : ℕ → ℝ → ℝ} (K : ℝ≥0)
    (hD : ∀ n x, HasDerivAt (F n) (D n x) x)
    (hLip : ∀ n, LipschitzWith K (D n))
    (hF : UniformCauchySeqOn F atTop univ) : UniformCauchySeqOn D atTop univ := by
  rw [Metric.uniformCauchySeqOn_iff] at hF ⊢
  intro ε hε
  let h : ℝ := ε/(8*((K:ℝ)+1))
  have hh : 0<h := div_pos hε (by positivity)
  have hke : 8*((K:ℝ)+1)*h=ε := by dsimp [h]; field_simp
  let δ : ℝ := ε*h/8
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨N,hN⟩ := hF δ hδ
  refine ⟨N,?_⟩
  intro m hm n hn x _
  have hb (z : ℝ) : |F m z-F n z| ≤ δ := by
    exact (hN m hm n hn z (mem_univ _)).le
  have H := derivative_bound_of_uniform_value_and_lipschitz _ _ (K+K) δ
    (fun z => (hD m z).sub (hD n z)) ((hLip m).sub (hLip n)) hb x h hh
  have he : 2*δ/h=ε/4 := by dsimp [δ]; field_simp; ring
  rw [he,NNReal.coe_add] at H
  rw [Real.dist_eq]
  have hk := K.coe_nonneg
  nlinarith

theorem uniformCauchySeq_limUnder {X : Type*} {F : ℕ → X → ℝ}
    (hF : UniformCauchySeqOn F atTop univ) :
    TendstoUniformly F (fun x => limUnder atTop (fun n => F n x)) atTop := by
  apply tendstoUniformlyOn_univ.mp
  apply hF.tendstoUniformlyOn_of_tendsto
  intro x _
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hF.cauchySeq (mem_univ x)))

theorem uniform_limit_hasDerivAt {F D : ℕ → ℝ → ℝ} (K : ℝ≥0)
    (hD : ∀ n x, HasDerivAt (F n) (D n x) x)
    (hLip : ∀ n, LipschitzWith K (D n))
    (hF : UniformCauchySeqOn F atTop univ) (x : ℝ) :
    HasDerivAt (fun z => limUnder atTop (fun n => F n z))
      (limUnder atTop (fun n => D n x)) x := by
  have hU := uniformCauchySeq_limUnder (uniformCauchySeq_derivative K hD hLip hF)
  exact hasDerivAt_of_tendstoUniformly hU (Eventually.of_forall hD)
    (fun z => (uniformCauchySeq_limUnder hF).tendsto_at z) x

end SK.Analytic

end
end

end OAI
