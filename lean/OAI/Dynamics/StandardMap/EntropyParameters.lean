import OAI.Dynamics.StandardMap.EntropyConjugacy

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma entropy_subdivision_parameters (M:ℝ) (hM:(1000:ℝ)^4≤M) :
    ∃N:ℕ,0<N ∧ 2*M≤(N:ℝ)^2 ∧ Real.log ((196*N:ℕ):ℝ)≤(3/4:ℝ)*Real.log M := by
  have hM1:1≤M := by nlinarith
  have hM0:0<M := by linarith
  let N:ℕ:=⌈Real.sqrt (2*M)⌉₊
  have hNp:0<N := Nat.ceil_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  have hNl:Real.sqrt (2*M)≤(N:ℝ) := Nat.le_ceil _
  have hNu:(N:ℝ)<Real.sqrt (2*M)+1 := Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have hMs:1≤Real.sqrt M := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hM1
  have hNs:Real.sqrt (2*M)≤2*Real.sqrt M := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hM0.le]
  have hN2:2*M≤(N:ℝ)^2 := by nlinarith [Real.sq_sqrt (show 0≤2*M by positivity),Real.sqrt_nonneg (2*M)]
  have hN3:(N:ℝ)≤3*Real.sqrt M := by linarith
  have hR:((196*N:ℕ):ℝ)≤1000*Real.sqrt M := by push_cast; nlinarith [Real.sqrt_nonneg M]
  have hRp:0<((196*N:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos (by norm_num : 0<196) hNp
  have hlogM:(4:ℝ)*Real.log 1000≤Real.log M := by
    have h:=Real.log_le_log (by positivity : (0:ℝ)<1000^4) hM
    simpa only [Real.log_pow,Nat.cast_ofNat] using h
  have hlogR:=Real.log_le_log hRp hR
  rw [Real.log_mul (by norm_num : (1000:ℝ)≠0) (Real.sqrt_pos.mpr hM0).ne',Real.log_sqrt hM0.le] at hlogR
  exact ⟨N,hNp,hN2,by linarith⟩
lemma entropy_grid_parameters (M:ℝ) (hM:1≤M) :
    ∃ε:ℝ,∃Q:ℕ,0<ε ∧ 0<Q ∧ 2*Real.pi*ε≤1 ∧ M*ε≤1 ∧ 6/(Q:ℝ)≤ε ∧
      Real.log (4*ε/(Q:ℝ))≤-Real.log M := by
  have hM0:0<M := by linarith
  let ε:ℝ:=1/(10*M)
  let Q:ℕ:=⌈60*M⌉₊
  have hε:0<ε := by dsimp [ε]; positivity
  have hQ:0<Q := Nat.ceil_pos.mpr (by positivity)
  have hQr:(0:ℝ)<Q := by exact_mod_cast hQ
  have hQ1:(1:ℝ)≤Q := by exact_mod_cast hQ
  have hQl:60*M≤(Q:ℝ) := Nat.le_ceil _
  have hε1:2*Real.pi*ε≤1 := by
    dsimp [ε]
    rw [← mul_div_assoc,mul_one]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<10*M)).mpr
    nlinarith [Real.pi_lt_four]
  have hε2:M*ε≤1 := by
    dsimp [ε]
    rw [← mul_div_assoc,mul_one]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<10*M)).mpr
    nlinarith
  have hQε:6/(Q:ℝ)≤ε := by
    calc
      _ ≤ 6/(60*M) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hQl
      _ = ε := by dsimp [ε]; field_simp; ring
  have hC:0<4*ε/(Q:ℝ) := by positivity
  have hCM:4*ε/(Q:ℝ)≤1/M := by
    calc
      _ ≤ 4*ε := div_le_self (by positivity) hQ1
      _ ≤ 1/M := by
        dsimp [ε]
        rw [← mul_div_assoc,mul_one]
        apply (div_le_div_iff₀ (show 0<10*M by positivity) hM0).mpr
        nlinarith
  have hlog:=Real.log_le_log hC hCM
  rw [one_div,Real.log_inv] at hlog
  exact ⟨ε,Q,hε,hQ,hε1,hε2,hQε,hlog⟩
end StandardMapEntropy

end OAI
