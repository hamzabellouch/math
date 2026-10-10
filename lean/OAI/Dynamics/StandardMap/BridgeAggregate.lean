import OAI.Dynamics.StandardMap.ProductSum

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma BridgeGrid.scale_bound {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (k : ℝ) (hc : BridgeScalarControl k) (lo len : ℕ) (ε : ℝ) (hε : 0< ε)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh)
    (hW0 : ∀d,0≤ arrayObservation B.sw B.tw Fw d) (hH0 : ∀d,0≤ arrayObservation B.sh B.th Fh d)
    (hlog : 1≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L≤ growthBase k)
    (hM : (2:ℝ)^10≤ growthBase k) (η : ℝ) (hη : 0<η)
    (hδ : 1/((B.N*2^lo:ℕ):ℝ)<η/2)
    (F : DistanceArray → ℝ) (hF : Continuous F) (D : ℝ) (hD : 0≤ D)
    (hFW : ∀d,F d≤ D*arrayObservation B.sw B.tw Fw d)
    (hzero : ∀d,¬((999/1000:ℝ)*((B.v:ℝ)-(B.u:ℝ))< d.val B.u B.v ∧ η< arrayObservation B.sh B.th Fh d) → F d=0)
    (C T : ℝ) (hC : 0≤ C)
    (hbW : ∀j<len,(∫ d,arrayObservation B.sw B.tw Fw d ∂sampleLaw k hc.nonneg (2^(B.p+lo+j)) (by positivity))≤ C*ε)
    (hbH : ∀j<len,(∫ d,arrayObservation B.sh B.th Fh d ∂sampleLaw k hc.nonneg (2^(B.p+lo+j)) (by positivity))≤ C*ε)
    (hT : (∫d,arrayObservation B.sw B.tw Fw d ∂scaleLaw k hc.nonneg (B.p+lo) len ε)≤ T ∨
      (∫d,arrayObservation B.sh B.th Fh d ∂scaleLaw k hc.nonneg (B.p+lo) len ε)≤ T) :
    (∫d,F d ∂scaleLaw k hc.nonneg (B.p+lo) len ε)≤
      (D*bridgeRealConstant/(η/2))*C*(T*ε+2/((B.N*2^lo:ℕ):ℝ)) := by
  let A (j : ℕ) := ∫d,arrayObservation B.sw B.tw Fw d ∂sampleLaw k hc.nonneg (2^(B.p+lo+j)) (by positivity)
  let H (j : ℕ) := ∫d,arrayObservation B.sh B.th Fh d ∂sampleLaw k hc.nonneg (2^(B.p+lo+j)) (by positivity)
  let E (j : ℕ) := growthBase k^(-(1/10:ℝ)*((B.N*2^(lo+j):ℕ):ℝ))
  let V (j : ℕ) := ∫d,F d ∂sampleLaw k hc.nonneg (2^(B.p+lo+j)) (by positivity)
  have hNp : 1≤ B.N*2^lo := by
    have hN : 0< B.N := by have := B.large; omega
    have hh : 0< B.N*2^lo := Nat.mul_pos hN (by positivity)
    omega
  have hE0 (j) : 0≤ E j := by apply Real.rpow_nonneg; linarith [growthBase_ge_four k hc.nonneg]
  have hEb (j) : E j≤1/((B.N*2^lo:ℕ):ℝ) := by
    have hh := bridge_error_inverse (growthBase k) hM (B.N*2^lo) j hNp
    have he : B.N*2^(lo+j)=(B.N*2^lo)*2^j := by rw [pow_add,mul_assoc]
    dsimp [E]
    rw [he]
    apply hh.trans
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.le_mul_of_pos_right (B.N*2^lo) (by positivity : 0<2^j)
  have hEs : (∑j∈Finset.range len,E j)≤2/((B.N*2^lo:ℕ):ℝ) := by
    simpa only [E,pow_add,mul_assoc] using bridge_error_sum (growthBase k) hM (B.N*2^lo) len hNp
  have hV (j) : V j≤ (D*bridgeRealConstant/(η/2))*((A j+E j)*H j) := by
    have hh := B.sample_bound k hc (lo+j) Fw Fh L hFw hFh hW0 hH0 hlog hLM η hη ((hEb j).trans_lt hδ)
      F hF D hD hFW hzero
    dsimp only [V,A,E,H]
    simpa only [Nat.add_assoc,mul_div_assoc,mul_assoc,div_mul_eq_mul_div] using hh
  have hT' : (∑j∈Finset.range len,A j)≤T*ε ∨ (∑j∈Finset.range len,H j)≤T*ε := by
    rcases hT with hT|hT
    · left
      rw [integral_scaleLaw k hc.nonneg (B.p+lo) len ε hε _ (continuous_arrayObservation _ _ _ hFw.continuous)] at hT
      exact (div_le_iff₀ hε).mp hT
    · right
      rw [integral_scaleLaw k hc.nonneg (B.p+lo) len ε hε _ (continuous_arrayObservation _ _ _ hFh.continuous)] at hT
      exact (div_le_iff₀ hε).mp hT
  have hp := sum_product_error (Finset.range len) A H E C ε T hC hε.le
    (fun j _ => integral_nonneg hW0) (fun j _ => integral_nonneg hH0) (fun j _ => hE0 j)
    (fun j hj => hbW j (Finset.mem_range.mp hj)) (fun j hj => hbH j (Finset.mem_range.mp hj)) hT'
  have hd : 0≤ D*bridgeRealConstant/(η/2) := div_nonneg (mul_nonneg hD bridgeRealConstant_nonneg) (by linarith)
  rw [integral_scaleLaw k hc.nonneg (B.p+lo) len ε hε F hF]
  apply (div_le_iff₀ hε).mpr
  calc
    _ ≤ ∑j∈Finset.range len,(D*bridgeRealConstant/(η/2))*((A j+E j)*H j) := Finset.sum_le_sum (fun j _ => hV j)
    _ = (D*bridgeRealConstant/(η/2))*(∑j∈Finset.range len,(A j+E j)*H j) := by rw [Finset.mul_sum]
    _ ≤ (D*bridgeRealConstant/(η/2))*(C*ε*(T*ε+∑j∈Finset.range len,E j)) := mul_le_mul_of_nonneg_left hp hd
    _ ≤ (D*bridgeRealConstant/(η/2))*(C*ε*(T*ε+2/((B.N*2^lo:ℕ):ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add le_rfl hEs) (mul_nonneg hC hε.le)) hd
    _ = _ := by ring
end StandardMapEntropy

end OAI
