import OAI.InformationTheory.AmplitudeDamping.PhaseCoding

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Filter
namespace GAD

theorem averageError_nonneg (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (C : Code n) :
    0 ≤ averageError γ ν C := by
  have hM : 0 < (C.messages:ℝ) := by exact_mod_cast C.messages_pos
  have hDs (m : Fin C.messages) : (1-C.decoding m).PosSemidef := by
    rw [← C.decoding_sum]
    have hle : C.decoding m ≤ ∑ j, C.decoding j := Finset.single_le_sum
      (fun j _ ↦ Matrix.nonneg_iff_posSemidef.mpr (C.decoding_pos j)) (Finset.mem_univ m)
    exact Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hle)
  have hprob (m : Fin C.messages) : (C.decoding m*channel γ ν n (C.encoding m)).trace.re ≤ 1 := by
    have hA := channel_state γ ν hγ hν n (C.encoding_state m)
    have h := trace_product_mono hA.1 (hDs m)
    simpa only [Matrix.mul_one,Matrix.trace_mul_comm _ (C.decoding m),hA.2,Complex.one_re] using h
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun m _ ↦ hprob m)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hs
  dsimp [averageError]
  exact sub_nonneg.mpr ((div_le_one hM).mpr hs)

def trivialCode (n : ℕ) : Code n where
  messages := 1
  messages_pos := by norm_num
  encoding := fun _ ↦ phaseState 0 (fun _ ↦ 0)
  encoding_state := fun _ ↦ phaseState_state (by norm_num) _
  decoding := fun _ ↦ 1
  decoding_pos := fun _ ↦ Matrix.PosSemidef.one
  decoding_sum := by simp

theorem trivialCode_error (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) : averageError γ ν (trivialCode n)=0 := by
  have h := channel_state γ ν hγ hν n (phaseState_state (n := n) (p := 0) (by norm_num) (fun _ ↦ 0))
  dsimp only [averageError,trivialCode]
  simp only [Matrix.one_mul,Fin.sum_univ_one,Nat.cast_one,div_one]
  rw [h.2,Complex.one_re,sub_self]

theorem zero_achievable (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) : Achievable γ ν 0 := by
  refine ⟨trivialCode,?_,?_⟩
  · simpa only [trivialCode_error γ ν hγ hν] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (nhds 0))
  · intro ε hε
    apply Filter.Eventually.of_forall
    intro n
    simp only [trivialCode,Nat.cast_one,Real.log_one,zero_div,zero_sub]
    linarith

end GAD

end

open Filter
namespace GAD

def codingMessages (r : ℝ) (n : ℕ) : ℕ := ⌈Real.exp ((n:ℝ)*r)⌉₊

theorem codingMessages_pos (r : ℝ) (n : ℕ) : 0 < codingMessages r n :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

theorem codingMessages_bound {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    (codingMessages r n:ℝ) ≤ 2*Real.exp ((n:ℝ)*r) := by
  have h1 := Nat.ceil_lt_add_one (Real.exp_pos ((n:ℝ)*r)).le
  have h2 : 1 ≤ Real.exp ((n:ℝ)*r) := Real.one_le_exp_iff.mpr (mul_nonneg (Nat.cast_nonneg _) hr)
  dsimp only [codingMessages]
  linarith

theorem codingMessages_rate (r : ℝ) {n : ℕ} (hn : 0 < n) :
    r/Real.log 2 ≤ Real.log (codingMessages r n:ℝ)/Real.log 2/(n:ℝ) := by
  have h : (n:ℝ)*r ≤ Real.log (codingMessages r n:ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos ((n:ℝ)*r)) (Nat.le_ceil (Real.exp ((n:ℝ)*r)))
    simpa only [Real.log_exp,codingMessages] using hh
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right h hl.le) hn'.le
  have he : (n:ℝ)*r/Real.log 2/(n:ℝ)=r/Real.log 2 := by
    field_simp
  rw [he] at hh
  exact hh

theorem coding_cross_bound {r : ℝ} (hr : 0 ≤ r) (a : ℝ) (n : ℕ) :
    4*(codingMessages r n:ℝ)*Real.exp (-(n:ℝ)*a) ≤
      8*Real.exp (-(n:ℝ)*(a-r)) := by
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (codingMessages_bound hr n) (by norm_num : (0:ℝ) ≤ 4)) (Real.exp_pos (-(n:ℝ)*a)).le
  apply h.trans_eq
  rw [show 4*(2*Real.exp ((n:ℝ)*r))*Real.exp (-(n:ℝ)*a)=
    8*(Real.exp ((n:ℝ)*r)*Real.exp (-(n:ℝ)*a)) by ring,← Real.exp_add]
  congr 2
  ring

theorem coding_error_tendsto (K δ : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun n : ℕ ↦ K/((n:ℝ)*δ^2)+8*Real.exp (-(n:ℝ)*b)) atTop (nhds 0) := by
  have h1 : Tendsto (fun n : ℕ ↦ K/((n:ℝ)*δ^2)) atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat K).div_const (δ^2)
    simpa only [div_div,zero_div] using h
  have h2 : Tendsto (fun n : ℕ ↦ 8*Real.exp (-(n:ℝ)*b)) atTop (nhds 0) := by
    have he := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-b)).le
      (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hb))
    have h := he.const_mul (8:ℝ)
    simpa only [mul_zero,← Real.exp_nat_mul,mul_neg,neg_mul] using h
  simpa only [zero_add] using h1.add h2

end GAD

end

end OAI
