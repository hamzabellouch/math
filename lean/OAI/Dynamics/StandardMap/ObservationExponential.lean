import OAI.Dynamics.StandardMap.GridBridge

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma bridge_observation_exponent (N r B : ℕ) (hN : 100 ≤ N)
    (hr : (r:ℝ) ≤ (N:ℝ)/1000) (hB : (N:ℝ)/3-1 ≤ (B:ℝ)) (hB1 : 1 ≤ B) :
    2+(3*r:ℕ)-(4/5:ℝ)*(B-1:ℕ) ≤ -(1/10:ℝ)*(N:ℝ) := by
  have hBc : ((B-1:ℕ):ℝ)=(B:ℝ)-1 := by rw [Nat.cast_sub hB1]; norm_num
  rw [hBc,Nat.cast_mul,Nat.cast_ofNat]
  have hc : (100:ℝ) ≤ N := by exact_mod_cast hN
  linarith
lemma bridge_observation_scalar (M L : ℝ) (hM : 1 ≤ M) (hlog : 1 ≤ Real.log M)
    (hL : 0 ≤ L) (hLM : 16*Real.pi*L ≤ M)
    (N r B : ℕ) (hN : 100 ≤ N) (hr : (r:ℝ) ≤ (N:ℝ)/1000)
    (hB : (N:ℝ)/3-1 ≤ (B:ℝ)) (hB1 : 1 ≤ B) :
    L*(((2*Real.pi*M)/Real.log M)*M^(3*r)*(8/M^((4/5:ℝ)*(B-1:ℕ)))) ≤
      M^(-(1/10:ℝ)*(N:ℝ)) := by
  have hMp : 0 < M := by linarith
  have hlogp : 0 < Real.log M := by linarith
  have hden : 0 < M^((4/5:ℝ)*(B-1:ℕ)) := Real.rpow_pos_of_pos hMp _
  have hco : L*(2*Real.pi*M/Real.log M)*8 ≤ M^2 := by
    have hdiv : 2*Real.pi*M/Real.log M ≤ 2*Real.pi*M :=
      div_le_self (by positivity) hlog
    calc
      _ ≤ L*(2*Real.pi*M)*8 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv hL) (by norm_num)
      _ = (16*Real.pi*L)*M := by ring
      _ ≤ M*M := mul_le_mul_of_nonneg_right hLM hMp.le
      _ = M^2 := by ring
  calc
    _ = (L*(2*Real.pi*M/Real.log M)*8)*(M^(3*r)/M^((4/5:ℝ)*(B-1:ℕ))) := by ring
    _ ≤ M^2*(M^(3*r)/M^((4/5:ℝ)*(B-1:ℕ))) :=
      mul_le_mul_of_nonneg_right hco (by positivity)
    _ = M^(2+(3*r:ℕ)-(4/5:ℝ)*(B-1:ℕ)) := by
      rw [Real.rpow_sub hMp,Real.rpow_add hMp]
      simp only [Real.rpow_natCast,Real.rpow_two]
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hM
      (bridge_observation_exponent N r B hN hr hB hB1)
lemma endpoint_shortfall_observation (k : ℝ) (hk : 0 ≤ k) {R : ℕ}
    (a : Fin R → ℤ) (n : Fin R → ℕ) (hn : ∀ i, 0 < n i)
    (F : (Fin R → ℝ) → ℝ) (L : NNReal) (hF : LipschitzWith L F)
    (b : ℤ) (r N B : ℕ) (hlen : ∀ i, n i ≤ 2*r)
    (hwin : ∀ i j, 1 ≤ j → j ≤ n i → (a i+(j:ℤ)-1-b).natAbs ≤ r)
    (hN : 100 ≤ N) (hr : (r:ℝ) ≤ (N:ℝ)/1000)
    (hB : (N:ℝ)/3-1 ≤ (B:ℝ)) (hB1 : 1 ≤ B)
    (hlog : 1 ≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L ≤ growthBase k)
    (z w : ℝ × ℝ) (hd : dist (liftIter k b z) (liftIter k b w) ≤
      8/growthBase k^((4/5:ℝ)*(B-1:ℕ))) :
    |F (fun i => torusShortfall k (liftProjection z) (a i) (n i))-
      F (fun i => torusShortfall k (liftProjection w) (a i) (n i))| ≤
      growthBase k^(-(1/10:ℝ)*(N:ℝ)) := by
  have hMp : 0 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hh := shortfall_observation_transport k hk a n hn F L hF b r hlen hwin z w
  apply hh.trans
  apply le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hd (by positivity)) L.coe_nonneg)
  exact bridge_observation_scalar (growthBase k) L (by linarith [growthBase_ge_four k hk]) hlog L.coe_nonneg hLM
    N r B hN hr hB hB1
lemma eventually_bridge_observation_scalars (L : ℝ) :
    ∀ᶠ k : ℝ in atTop, 1 ≤ Real.log (growthBase k) ∧ 16*Real.pi*L ≤ growthBase k := by
  have hlog := (Real.tendsto_log_atTop.comp tendsto_growthBase).eventually (eventually_ge_atTop (1:ℝ))
  have hL := tendsto_growthBase.eventually (eventually_ge_atTop (16*Real.pi*L))
  exact hlog.and hL
end StandardMapEntropy

end OAI
