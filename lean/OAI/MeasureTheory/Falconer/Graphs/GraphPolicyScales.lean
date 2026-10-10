import OAI.MeasureTheory.Falconer.Graphs.GraphScaleData
import OAI.MeasureTheory.Falconer.Estimates.FarPolicyScales

namespace OAI

/-! # Graph scales in the original integer-depth coordinates -/

namespace Falconer

noncomputable def policyGraphRadius (N a p : ℕ) (σ c₀ : ℝ) : ℝ :=
  min c₀ ((2:ℝ)^((a:ℝ)-p+10*σ*N))

noncomputable def policyGraphWidth (N p : ℕ) (σ : ℝ) : ℝ :=
  (2:ℝ)^(-(p:ℝ)+30*σ*N)

noncomputable def policyGraphScale (N a p L : ℕ) (σ c₀ C : ℝ) : ℝ :=
  graphDerivativeScale 2 (σ*N) a p L c₀ C

 theorem descriptor_graph_scale_identity (N L : ℕ) (σ : ℝ) :
    descriptorDerivativeScale N σ L =
      (2:ℝ)^(σ*N)*max 1 ((2:ℝ)^((L:ℝ)-50*σ*N)) := by
  unfold descriptorDerivativeScale
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) N σ,
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) N (-50*σ),
    ← Real.rpow_natCast (2:ℝ) L,← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 2 <;> ring_nf

 theorem policy_graph_scale_data (d : ℕ) {N a p t L : ℕ} {σ c₀ C : ℝ}
    (hN : 0 < N) (hσ : 0 < σ) (hc₀ : 0 < c₀) (hcsmall : c₀ ≤ 1/2)
    (hC : 1 ≤ C) (hCdim : 4*Real.sqrt d ≤ C)
    (hh : (p:ℝ)-a ≤ (t:ℝ)-p+2*σ*N)
    (hL : (L:ℝ) ≤ (t:ℝ)-p+2*σ*N)
    (hq : 10*σ*N ≤ (t:ℝ)-p)
    (hlarge : 40*Real.sqrt d ≤ ((2:ℝ)^N)^(20*σ))
    (hlargeπ : 4*Real.pi ≤ ((2:ℝ)^N)^(20*σ)) :
    0 < policyGraphRadius N a p σ c₀ ∧ policyGraphRadius N a p σ c₀ ≤ 1/2 ∧
    0 < policyGraphWidth N p σ ∧ 1 ≤ policyGraphScale N a p L σ c₀ C ∧
    (policyGraphRadius N a p σ c₀)⁻¹ ≤ policyGraphScale N a p L σ c₀ C ∧
    Real.sqrt d*(2:ℝ)^(-(a:ℝ)) ≤
      (policyGraphWidth N p σ/4)*policyGraphScale N a p L σ c₀ C ∧
    2*Real.sqrt d*(2:ℝ)^(-(p:ℝ))+
      8*policyGraphRadius N a p σ c₀*(Real.sqrt d*(2:ℝ)^(-(a:ℝ))) ≤
        policyGraphWidth N p σ/4 ∧
    4*Real.pi*((2:ℝ)^N)^(20*σ) ≤ (2:ℝ)^t*policyGraphWidth N p σ ∧
    16*policyGraphScale N a p L σ c₀ C/((2:ℝ)^t*policyGraphWidth N p σ) ≤
      (16*C*(4+c₀⁻¹))*((2:ℝ)^N)^(-26*σ) := by
  have hpow (r : ℝ) : ((2:ℝ)^N)^r = (2:ℝ)^(r*N) := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) N r]
    congr 1
    ring
  have he := graph_scale_data d (R := 2) (σ := σ*N) (a := a) (p := p) (v := t)
    (L := L) (frequency := t) (by norm_num)
    (mul_pos hσ (Nat.cast_pos.mpr hN)) hc₀ hcsmall hC hCdim
    (by nlinarith) (by nlinarith) (by nlinarith) rfl
    (by simpa only [hpow,mul_assoc] using hlarge)
    (by simpa only [hpow,mul_assoc] using hlargeπ)
  simpa only [policyGraphRadius,policyGraphWidth,policyGraphScale,hpow,mul_assoc,
    Real.rpow_natCast,neg_mul] using he

 theorem policy_graph_symbol_scale {N a p L : ℕ} {σ c₀ C E : ℝ}
    (hC : 1 ≤ C) (hc₀ : 0 < c₀) (hE : E ≤ descriptorDerivativeScale N σ L) :
    1+E ≤ policyGraphScale N a p L σ c₀ C := by
  have hE' : E ≤ (2:ℝ)^(σ*N)*max 1 ((2:ℝ)^((L:ℝ)-50*(σ*N))) := by
    simpa only [descriptor_graph_scale_identity,mul_assoc] using hE
  have hi : 0 ≤ (min c₀ ((2:ℝ)^((a:ℝ)-p+10*(σ*N))))⁻¹ :=
    inv_nonneg.mpr (le_min hc₀.le (by positivity))
  have hr : 0 ≤ (2:ℝ)^(-(a:ℝ))/(2:ℝ)^(-(p:ℝ)+30*(σ*N)) := by positivity
  let S := 1+(2:ℝ)^(σ*N)*max 1 ((2:ℝ)^((L:ℝ)-50*(σ*N)))+
    (min c₀ ((2:ℝ)^((a:ℝ)-p+10*(σ*N))))⁻¹+
    (2:ℝ)^(-(a:ℝ))/(2:ℝ)^(-(p:ℝ)+30*(σ*N))
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hfirst : 1+E ≤ S := by dsimp [S]; linarith
  exact hfirst.trans (le_mul_of_one_le_left hS hC)

 theorem policyGraphWidth_eq (N p : ℕ) (σ : ℝ) :
    policyGraphWidth N p σ = (1/(2:ℝ)^p)*((2:ℝ)^N)^(30*σ) := by
  unfold policyGraphWidth
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2),
    Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div,
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) N (30*σ)]
  congr 2
  ring

 theorem policyGraphRadius_le (N a p : ℕ) (σ c₀ : ℝ) :
    policyGraphRadius N a p σ c₀ ≤ ((2:ℝ)^a/(2:ℝ)^p)*((2:ℝ)^N)^(10*σ) := by
  apply (min_le_right _ _).trans_eq
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2),
    Real.rpow_sub (by norm_num : (0:ℝ) < 2),Real.rpow_natCast,Real.rpow_natCast,
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) N (10*σ)]
  congr 2
  ring

end Falconer

end OAI
