import OAI.InformationTheory.AmplitudeDamping.Holevo

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Filter
namespace GAD

def codeEnsemble {n : ℕ} (C : Code n) : Ensemble n where
  size := C.messages
  weight := fun _ ↦ (C.messages:ℝ)⁻¹
  weight_nonneg := fun _ ↦ by positivity
  weight_sum := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast C.messages_pos.ne')
  signal := C.encoding
  signal_state := C.encoding_state

theorem code_success_dim_bound (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (C : Code n) :
    (∑ m, (C.decoding m*channel γ ν n (C.encoding m)).trace.re) ≤ (2:ℝ)^n := by
  calc
    _ ≤ ∑ m, (C.decoding m).trace.re := Finset.sum_le_sum (fun m _ ↦
      state_measurement_prob_le_trace (channel_state γ ν hγ hν n (C.encoding_state m)) (C.decoding_pos m))
    _ = _ := by
      rw [← Complex.re_sum,← Matrix.trace_sum,C.decoding_sum,Matrix.trace_one]
      rw [basis_card,Nat.cast_pow,Nat.cast_ofNat]
      rw [← Complex.ofReal_ofNat,← Complex.ofReal_pow,Complex.ofReal_re]

theorem code_messages_bound (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (C : Code n)
    (he : averageError γ ν C ≤ 1/2) : (C.messages:ℝ) ≤ 2*(2:ℝ)^n := by
  have hM : 0 < (C.messages:ℝ) := by exact_mod_cast C.messages_pos
  have hs := code_success_dim_bound γ ν hγ hν C
  dsimp [averageError] at he
  have ht : (1/2:ℝ)*(C.messages:ℝ) ≤ ∑ m, (C.decoding m*channel γ ν n (C.encoding m)).trace.re := by
    apply (le_div_iff₀ hM).mp
    linarith
  linarith

theorem code_entropy_bound (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (C : Code n) {p : ℝ} (hp : Maximizes γ ν p)
    {ε : ℝ} (hε : 0 < ε) :
    Real.log (C.messages:ℝ) ≤ (n:ℝ)*objective γ ν p+
      2*factorError ε (2*averageError γ ν C) (2^n*C.messages) := by
  let : Nonempty (Fin C.messages) := Fin.pos_iff_nonempty.mp C.messages_pos
  have h := cq_decoding_entropy_bound (fun m ↦ channel γ ν n (C.encoding m)) C.decoding
    (fun m ↦ channel_state γ ν hγ hν n (C.encoding_state m)) C.decoding_pos C.decoding_sum hε
  have hw (m : Fin C.messages) : uniformWeight (Fin C.messages) m=(C.messages:ℝ)⁻¹ := by
    simp only [uniformWeight,Fintype.card_fin]
  have he : 1-∑ m, uniformWeight (Fin C.messages) m*(C.decoding m*channel γ ν n (C.encoding m)).trace.re =
      averageError γ ν C := by
    simp only [hw,← Finset.mul_sum,averageError,div_eq_mul_inv]
    ring
  rw [he,Fintype.card_prod,basis_card,Fintype.card_fin] at h
  have hu := ensemble_nats_upper γ ν hγ hν (codeEnsemble C) hp
  change entropy (∑ a, (((C.messages:ℝ)⁻¹:ℝ):ℂ) • channel γ ν n (C.encoding a)) -
    (∑ a, (C.messages:ℝ)⁻¹*entropy (channel γ ν n (C.encoding a))) ≤ (n:ℝ)*objective γ ν p at hu
  simp only [Complex.coe_smul] at hu
  simp only [hw] at h
  linarith

theorem code_log_dimension_bound (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (hn : 0 < n) (C : Code n)
    (he : averageError γ ν C ≤ 1/2) :
    Real.log (2^n*C.messages:ℕ) ≤ 3*(n:ℝ)*Real.log 2 := by
  have hM : 0 < (C.messages:ℝ) := by exact_mod_cast C.messages_pos
  have hpow : 0 < (2:ℝ)^n := by positivity
  have hb := code_messages_bound γ ν hγ hν C he
  have hl := Real.log_le_log hM hb
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hpow.ne',Real.log_pow] at hl
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Real.log_mul hpow.ne' hM.ne',Real.log_pow]
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

theorem code_log_rate_bound (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (hn : 0 < n) (C : Code n) {p : ℝ} (hp : Maximizes γ ν p)
    {ε : ℝ} (hε : 0 < ε) (he : averageError γ ν C ≤ 1/2)
    (heε : averageError γ ν C ≤ 2*ε^2) :
    Real.log (C.messages:ℝ) ≤ (n:ℝ)*objective γ ν p+
      12*ε*(n:ℝ)*Real.log 2+(2+4*ε)*Real.log 2 := by
  have h := code_entropy_bound γ ν hγ hν C hp hε
  have hd : 0 < 2^n*C.messages := Nat.mul_pos (pow_pos (by norm_num) n) C.messages_pos
  have hb := factorError_mono hε hd (show 2*averageError γ ν C ≤ 4*ε^2 by nlinarith)
  have hlog := code_log_dimension_bound γ ν hγ hν hn C he
  have ht : factorError ε (4*ε^2) (2^n*C.messages)=
      2*ε*Real.log (2^n*C.messages:ℕ)+(1+2*ε)*Real.log 2 := by
    dsimp [factorError]
    field_simp
    ring
  rw [ht] at hb
  have hh := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2*ε by positivity)
  nlinarith

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Filter
namespace GAD

theorem achievable_upper (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p R : ℝ} (hp : Maximizes γ ν p)
    (hR : Achievable γ ν R) : R ≤ objective γ ν p/Real.log 2 := by
  obtain ⟨C,herr,hrate⟩ := hR
  by_contra! hbad
  let χ := objective γ ν p/Real.log 2
  let ε := (R-χ)/28
  have hε : 0 < ε := by dsimp [ε,χ]; linarith
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he1 : ∀ᶠ n : ℕ in atTop, averageError γ ν (C n) < 1/2 :=
    herr.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))
  have he2 : ∀ᶠ n : ℕ in atTop, averageError γ ν (C n) < 2*ε^2 :=
    herr.eventually (gt_mem_nhds (by positivity : (0:ℝ) < 2*ε^2))
  obtain ⟨N,hN⟩ := exists_nat_gt ((2+4*ε)/ε)
  obtain ⟨n,hnR,hn1,hn2,hn⟩ := ((hrate ε hε).and (he1.and
    (he2.and (eventually_ge_atTop (max N 1))))).exists
  have hn0 : 0 < n := by omega
  have hnR0 : 0 < (n:ℝ) := by exact_mod_cast hn0
  have hNn : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast (le_trans (le_max_left N 1) hn)
  have hsmall : 2+4*ε ≤ ε*(n:ℝ) := by
    have hh := (div_lt_iff₀ hε).mp hN
    nlinarith
  have hupper := code_log_rate_bound γ ν hγ hν hn0 (C n) hp hε hn1.le hn2.le
  have hlower := (le_div_iff₀ hl).mp ((le_div_iff₀ hnR0).mp hnR)
  have hχ : χ*Real.log 2=objective γ ν p := div_mul_cancel₀ _ hl.ne'
  have hχn : (n:ℝ)*objective γ ν p=χ*(n:ℝ)*Real.log 2 := by rw [← hχ]; ring
  rw [hχn] at hupper
  have hsmall' := mul_le_mul_of_nonneg_right hsmall hl.le
  have hf : (R-χ-14*ε)*((n:ℝ)*Real.log 2) ≤ 0 := by nlinarith
  have hg : 0 < R-χ-14*ε := by dsimp [ε]; change χ < R at hbad; linarith
  exact (not_le_of_gt (mul_pos hg (mul_pos hnR0 hl))) hf

end GAD

end

end OAI
