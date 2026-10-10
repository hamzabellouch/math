import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialSourceCover
import OAI.Combinatorics.SharpRamsey.Planar.HeavyPlanePublic

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real Filter SourceScales
open scoped Classical BigOperators Topology
noncomputable section

lemma spatial_cost {q P d τ H Q : ℝ} {M : ℕ}
    (hq : 1≤q) (hP : 1≤P) (hd : 0≤d) (hτ : τ≤1)
    (hM : (M:ℝ)≤2*q*P+1) (hH : log (H+1)≤4*q) (hQ : log (Q+1)≤4*q) :
    2*((M:ℝ)*(log 2+d)+4*P*τ+log 4+log (H+1))+log 3+log (Q+1)≤
      300*q*P*(d+P) := by
  have hqP := one_le_mul_of_one_le_of_one_le hq hP
  have hM' : (M:ℝ)≤3*q*P := by nlinarith
  have h2 : 0≤log (2:ℝ) := log_nonneg (by norm_num)
  have h2u : log (2:ℝ)≤1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have h4 : log (4:ℝ)≤3 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4); linarith
  have h3 : log (3:ℝ)≤2 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3); linarith
  have hm := mul_le_mul_of_nonneg_right hM' (add_nonneg h2 hd)
  have hl := mul_le_mul_of_nonneg_left h2u (show 0≤3*q*P by positivity)
  have ht := mul_le_mul_of_nonneg_left hτ (show 0≤4*P by linarith)
  have hPq : P≤q*P := le_mul_of_one_le_left (by linarith) hq
  have hqP' : q≤q*P := le_mul_of_one_le_right (by linarith) hP
  have hbig : q*P≤q*P*P := le_mul_of_one_le_right (by positivity) hP
  have hpos : 0≤q*P*d := by positivity
  nlinarith

lemma spatial_log_card {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype (Projectivization K V)] (hdim : Module.finrank K V=4) :
    log ((Fintype.card (Projectivization K V):ℝ)+1)≤4*Nat.card K ∧
    log ((Fintype.card (Projectivization K V):ℝ)*log 2+1)≤4*Nat.card K := by
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hc : (Fintype.card (Projectivization K V):ℝ)=1+Nat.card K+(Nat.card K:ℝ)^2+(Nat.card K:ℝ)^3 := by
    rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim]
    norm_num [sum_range_succ]
  have hQ : (Fintype.card (Projectivization K V):ℝ)+1≤(Nat.card K+1:ℝ)^4 := by
    rw [hc]
    nlinarith [sq_nonneg (Nat.card K:ℝ),sq_nonneg ((Nat.card K:ℝ)^2)]
  have hlog : log ((Nat.card K+1:ℝ)^4)≤4*Nat.card K := by
    rw [log_pow]
    have hh := log_le_sub_one_of_pos (show (0:ℝ)<Nat.card K+1 by linarith)
    norm_num only [Nat.cast_ofNat]
    linarith
  have hf := (log_le_log (by positivity) hQ).trans hlog
  refine ⟨hf,(log_le_log (by have := log_nonneg (by norm_num : (1:ℝ)≤2); positivity) ?_).trans hf⟩
  have hl : log (2:ℝ)≤1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  nlinarith [show (0:ℝ)≤Fintype.card (Projectivization K V) by positivity]

lemma eventually_header_budget : ∀ᶠ σ : ℝ in atTop,
    40*σ*(⌈exp (7*σ/10)⌉₊+1:ℕ)≤exp σ := by
  filter_upwards [ScaleSelection.eventually_polynomial_le_exp_rpow 120 1 1 (3/10)
    (by norm_num) (by norm_num),eventually_ge_atTop (1:ℝ)] with σ h hσ
  simp only [rpow_one] at h
  have he : 1≤exp (7*σ/10) := one_le_exp_iff.mpr (by linarith)
  have hJ : (⌈exp (7*σ/10)⌉₊+1:ℕ)≤3*exp (7*σ/10) := by
    have hh := Nat.ceil_lt_add_one (exp_pos (7*σ/10)).le
    push_cast
    linarith
  calc
    _ ≤ 40*σ*(3*exp (7*σ/10)) := by gcongr
    _ = (120*σ)*exp (7*σ/10) := by ring
    _ ≤ exp (3/10*σ)*exp (7*σ/10) := by gcongr
    _ = exp σ := by rw [←exp_add]; congr 1; ring

lemma header_log_bound {q σ : ℝ} {n N J : ℕ} (hq : 3≤q) (hex : exp σ=q)
    (hn : (n:ℝ)≤2*q^2) (hN : (N:ℝ)≤q^16)
    (hJ : J=⌈exp (7*σ/10)⌉₊) (hbudget : 40*σ*(J+1:ℕ)≤q) :
    log ((n+1:ℕ)*(J+1:ℕ)*((N*(n+1)+1:ℕ):ℝ)^J)≤q := by
  have hqp : 0<q := by linarith
  have hs : 0≤σ := by rw [←log_exp σ,hex]; exact log_nonneg (by linarith)
  have hlogq : log q=σ := by rw [←hex,log_exp]
  have hnq : (n+1:ℕ)≤q^3 := by push_cast; nlinarith [sq_nonneg q]
  have hnlog : log (n+1:ℕ)≤3*σ := by
    have hh := log_le_log (by positivity) hnq
    simpa only [log_pow,hlogq,Nat.cast_ofNat] using hh
  have hNq : (N*(n+1)+1:ℕ)≤q^20 := by
    have hh := mul_le_mul hN hnq (by positivity) (by positivity : 0≤q^16)
    have hh' : q^19+1≤q^20 := by
      rw [pow_succ q 19]
      have hpow : 1≤q^19 := one_le_pow₀ (by linarith)
      nlinarith
    push_cast at *
    calc
      _ ≤ q^16*q^3+1 := by linarith
      _ = q^19+1 := by rw [←pow_add]
      _ ≤ q^20 := hh'
  have hNlog : log (N*(n+1)+1:ℕ)≤20*σ := by
    have hh := log_le_log (by positivity) hNq
    simpa only [log_pow,hlogq,Nat.cast_ofNat] using hh
  have hJnum : (J+1:ℕ)≤3*q := by
    have hJe : exp (7*σ/10)≤exp σ := exp_le_exp.mpr (by linarith)
    have hceil := Nat.ceil_lt_add_one (exp_pos (7*σ/10)).le
    rw [←hJ] at hceil
    rw [hex] at hJe
    push_cast
    linarith
  have hJlog : log (J+1:ℕ)≤2*σ := by
    have hJq : (J+1:ℕ)≤q^2 := by nlinarith
    have hh := log_le_log (by positivity) hJq
    simpa only [log_pow,hlogq,Nat.cast_ofNat] using hh
  rw [log_mul (by positivity) (by positivity),log_mul (by positivity) (by positivity),log_pow]
  have hm := mul_le_mul_of_nonneg_left hNlog (show (0:ℝ)≤J by positivity)
  push_cast at hbudget
  nlinarith

lemma heavy_header_cost {q : ℝ} {N n m : ℕ} (hq : 3≤q) (hN0 : 0<N)
    (hN : (N:ℝ)≤q^16) (hn : (n:ℝ)≤2*q^2) (hm : log (m+1:ℕ)≤4*q) :
    log ((N:ℝ)*(q+1)*(n+1:ℕ)*(m+1:ℕ))≤24*q := by
  have hq0 : 0<q := by linarith
  have hNN : (0:ℝ)<N := by exact_mod_cast hN0
  have hlogq : log q≤q := (log_le_sub_one_of_pos hq0).trans (by linarith)
  have hlogN : log (N:ℝ)≤16*q := by
    have hh := log_le_log hNN hN
    rw [log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hnq : (n+1:ℕ)≤(q+1)^3 := by
    push_cast
    nlinarith [sq_nonneg q]
  have hlogn : log (n+1:ℕ)≤3*q := by
    have hh := log_le_log (by positivity) hnq
    rw [log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    have h := log_le_sub_one_of_pos (show 0<q+1 by linarith)
    linarith
  have hlog := log_le_sub_one_of_pos (show 0<q+1 by linarith)
  rw [log_mul (by positivity) (by positivity),log_mul (by positivity) (by positivity),
    log_mul hNN.ne' (by positivity)]
  linarith

lemma cover_log_bound {a H E B : ℝ} (ha : 0≤a) (hH : 0<H)
    (h : a≤H*exp E) (hB : 0≤B) (hlen : log H+E≤B) : log (a+1)≤B+log 2 := by
  have he : H*exp E≤exp B := by
    rw [←exp_log hH,←exp_add]
    exact exp_le_exp.mpr hlen
  have hone : 1≤exp B := one_le_exp_iff.mpr hB
  apply (log_le_log (by positivity) (show a+1≤2*exp B by linarith)).trans_eq
  rw [log_mul (by norm_num) (exp_pos _).ne',log_exp]
  ring

lemma union_log_bound {α : Type*} [DecidableEq α] (A B : Finset α) {E : ℝ}
    (hA : log ((A.card:ℝ)+1)≤E) (hB : log ((B.card:ℝ)+1)≤E) :
    log (((A∪B).card:ℝ)+1)≤E+log 2 := by
  have hA' := exp_le_exp.mpr hA
  have hB' := exp_le_exp.mpr hB
  rw [exp_log (by positivity)] at hA' hB'
  have hc : ((A∪B).card:ℝ)≤A.card+B.card := by exact_mod_cast card_union_le A B
  apply (log_le_log (by positivity) (show ((A∪B).card:ℝ)+1≤2*exp E by linarith)).trans_eq
  rw [log_mul (by norm_num) (exp_pos _).ne',log_exp]
  ring

end
end SharpLogRamsey.SpatialPublic

end

end OAI
