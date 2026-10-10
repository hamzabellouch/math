import OAI.Dynamics.StandardMap.MiddlePrefixBridge

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
noncomputable def transferVectorLog (M : ℝ) (v : ℕ → ℝ) (u : ℂ) (j : ℕ) : ℝ :=
  Real.log ‖transferProduct v j u‖/Real.log M
lemma transferVector_norm_pos (v : ℕ → ℝ) (u : ℂ) (hu : u≠0) (j : ℕ) :
    0 < ‖transferProduct v j u‖ := by
  apply norm_pos_iff.mpr
  intro he
  have hh := congrArg (transferProductInv v j) he
  simp only [transferProductInv_inverse,map_zero] at hh
  exact hu hh
lemma transferVectorLog_step (M : ℝ) (hM : 1 < M) (v : ℕ → ℝ)
    (u : ℂ) (hu : u≠0) (j : ℕ) (hv : |v (j+1)|+1≤M) :
    transferVectorLog M v u (j+1)-transferVectorLog M v u j≤1 := by
  have hp := transferVector_norm_pos v u hu j
  have hp' := transferVector_norm_pos v u hu (j+1)
  have hs : ‖transferProduct v (j+1) u‖≤M*‖transferProduct v j u‖ := by
    change ‖transferStep (v (j+1)) (transferProduct v j u)‖≤_
    exact ((transferStep _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((transferStep_norm _).trans hv) (norm_nonneg _))
  have hl := Real.log_le_log hp' hs
  rw [Real.log_mul (by linarith : M≠0) hp.ne'] at hl
  unfold transferVectorLog
  rw [← sub_div]
  exact (div_le_one (Real.log_pos hM)).mpr (by linarith)
lemma transferVectorLog_interval (M : ℝ) (hM : 1 < M) (v : ℕ → ℝ)
    (u : ℂ) (hu : u≠0) (i l : ℕ) (c : ℝ)
    (hgood : c*(l:ℝ)≤transferVectorLog M v u (i+l)-transferVectorLog M v u i) :
    M^(c*(l:ℝ))≤‖transferProduct (fun j => v (i+j)) l‖ := by
  have hi := transferVector_norm_pos v u hu i
  have hil := transferVector_norm_pos v u hu (i+l)
  have hD : 0 < ‖transferProduct (fun j => v (i+j)) l‖ := by
    have := (transferProduct_area (fun j => v (i+j)) l).singular_pair.choose_spec.2.2.2.2
    linarith
  have hb : ‖transferProduct v (i+l) u‖≤
      ‖transferProduct (fun j => v (i+j)) l‖*‖transferProduct v i u‖ := by
    rw [transferProduct_concat]
    exact (transferProduct _ _).le_opNorm _
  have hl := Real.log_le_log hil hb
  rw [Real.log_mul hD.ne' hi.ne'] at hl
  apply (Real.rpow_le_iff_le_log (by linarith) hD).mpr
  unfold transferVectorLog at hgood
  rw [← sub_div] at hgood
  have hh := (le_div_iff₀ (Real.log_pos hM)).mp hgood
  linarith
lemma torus_middle_prefix_of_vector (k : ℝ) (hk : 0≤k) (z : Torus) (N i : ℕ)
    (hi : i≤N) (u : ℂ) (hu : u≠0)
    (hg : MiddleLogGood (transferVectorLog (growthBase k) (torusSegmentCoefficient k z 0) u) N i) :
    torusPrefixGrowth k (N-i) (torusIter k (i:ℤ) z) ∧
      torusPrefixGrowth k i (torusIter k (i:ℤ) z).swap := by
  have hM : 1 < growthBase k := by linarith [growthBase_ge_four k hk]
  constructor
  · intro l hl hli
    rw [torusSegmentTransfer_shift,zero_add]
    change growthBase k^((49/50:ℝ)*(l:ℝ))≤‖transferProduct (torusSegmentCoefficient k z (i:ℤ)) l‖
    rw [← zero_add (i:ℤ),← torusSegmentCoefficient_shift]
    apply transferVectorLog_interval (growthBase k) hM _ u hu i l (49/50)
    have hh := hg.2 (i+l) (by omega) (by omega)
    simpa only [Nat.cast_add,add_sub_cancel_left] using hh
  · intro l hl hli
    rw [torusSegmentTransfer_reverse_norm,torusSegmentTransfer_shift]
    change growthBase k^((49/50:ℝ)*(l:ℝ))≤‖transferProduct (torusSegmentCoefficient k z (-(l:ℤ)+(i:ℤ))) l‖
    have hei : -(l:ℤ)+(i:ℤ)=0+((i-l:ℕ):ℤ) := by omega
    rw [hei,← torusSegmentCoefficient_shift]
    apply transferVectorLog_interval (growthBase k) hM _ u hu (i-l) l (49/50)
    have hh := hg.1 (i-l) (by omega)
    rw [Nat.sub_add_cancel hli]
    simpa only [Nat.cast_sub hli,sub_sub_cancel] using hh
end StandardMapEntropy

end OAI
