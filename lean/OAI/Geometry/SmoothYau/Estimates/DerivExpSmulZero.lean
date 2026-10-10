import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
lemma hasDerivAt_exp_smul_zero (K : E →L[ℝ] E) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • K)) K 0 := by
  simpa only [zero_smul,NormedSpace.exp_zero,one_mul] using
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) K 0)

lemma exp_smul_apply_deriv_zero (K : E →L[ℝ] E) (v : E) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • K)) v) (K v) 0 := by
  exact (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_exp_smul_zero K)

lemma exp_pairing_first_variation (G : E →L[ℝ] E →L[ℝ] ℝ)
    (K : E →L[ℝ] E) (v w : E) :
    HasDerivAt (fun t : ℝ => G ((NormedSpace.exp (t • K)) v)
      ((NormedSpace.exp (t • K)) w)) (G (K v) w + G v (K w)) 0 := by
  have hh := G.hasFDerivAt.comp_hasDerivAt 0 (exp_smul_apply_deriv_zero K v)
  have he := hh.clm_apply (exp_smul_apply_deriv_zero K w)
  simpa only [Function.comp_def,zero_smul,NormedSpace.exp_zero,one_apply_eq_self] using he

lemma clm_exp_fix_kernel {K : E →L[ℝ] E} {v : E} (h : K v = 0) :
    (NormedSpace.exp K) v = v := by
  have hp : ∀ n : ℕ, (K^(n+1)) v = 0 := by
    intro n
    rw [pow_succ,mul_apply_eq_comp,h,map_zero]
  have he := (NormedSpace.expSeries_summable' (𝕂 := ℝ) K).hasSum.map
    (ContinuousLinearMap.apply ℝ E v).toAddMonoidHom
    (ContinuousLinearMap.apply ℝ E v).continuous
  have hs : HasSum (fun n : ℕ => (n.factorial:ℝ)⁻¹ • ((K^n) v)) v := by
    convert (hasSum_ite_eq (0:ℕ) v) using 1
    funext n
    cases n with
    | zero => simp
    | succ n => simp [hp n]
  have hx : HasSum (fun n : ℕ => (n.factorial:ℝ)⁻¹ • ((K^n) v))
      ((NormedSpace.exp K) v) := by
    rw [NormedSpace.exp_eq_tsum ℝ]
    change HasSum (fun n : ℕ => ((n.factorial:ℝ)⁻¹ • (K^n)) v)
      ((∑' n : ℕ, (n.factorial:ℝ)⁻¹ • (K^n)) v) at he
    simpa only [smul_apply] using he
  exact hx.unique hs
lemma clm_exp_selfAdjoint (G : E →L[ℝ] E →L[ℝ] ℝ) (K : E →L[ℝ] E)
    (hK : ∀ v w, G (K v) w = G v (K w)) (v w : E) :
    G ((NormedSpace.exp K) v) w = G v ((NormedSpace.exp K) w) := by
  have hp (n : ℕ) : ∀ v w, G ((K^n) v) w = G v ((K^n) w) := by
    induction n with
    | zero => intro v w; simp
    | succ n ih =>
      intro v w
      calc G ((K^(n+1)) v) w = G (K ((K^n) v)) w := by rw [pow_succ',mul_apply_eq_comp]
        _ = G ((K^n) v) (K w) := hK _ _
        _ = G v ((K^n) (K w)) := ih _ _
        _ = G v ((K^(n+1)) w) := by rw [pow_succ,mul_apply_eq_comp]
  let L : (E →L[ℝ] E) →L[ℝ] ℝ :=
    (G.flip w).comp (ContinuousLinearMap.apply ℝ E v) -
      (G v).comp (ContinuousLinearMap.apply ℝ E w)
  have hL (n : ℕ) : L (K^n) = 0 := sub_eq_zero.mpr (hp n v w)
  have he : L (NormedSpace.exp K) = 0 := by
    rw [NormedSpace.exp_eq_tsum ℝ,L.map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℝ) K)]
    simp only [map_smul,hL,smul_zero,tsum_zero]
  exact sub_eq_zero.mp he

lemma pinned_exp_pairing (G : E →L[ℝ] E →L[ℝ] ℝ) (K : E →L[ℝ] E)
    (hK : ∀ v w, G (K v) w = G v (K w)) {v : E} (hv : K v = 0) (w : E) :
    G ((NormedSpace.exp K) v) ((NormedSpace.exp K) w) = G v w := by
  rw [clm_exp_fix_kernel hv,← clm_exp_selfAdjoint G K hK v w,clm_exp_fix_kernel hv]

end YauCounterexamples

end

end OAI
