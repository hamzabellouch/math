import OAI.NumberTheory.Ostmann.QuadraticSieveExponentIterationInitial

namespace OAI

namespace Ostmann.QuadraticSieve

theorem small_scale_exponent_budget {M N P η ξ : ℝ} (hM : 0 < M) (hN : 0 < N)
    (hP : 1 ≤ P) (hη : 0 ≤ η) (hξ1 : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hscale : M ≤ 4*N*P^η) :
    M+N^ξ ≤ 4*P^η*(M+M^(1-ξ)*N^(2*ξ-1)) := by
  have hT : 1 ≤ P^η := Real.one_le_rpow hP hη
  have hratio : M/N ≤ 4*P^η := (div_le_iff₀ hN).mpr (by nlinarith)
  have hpow : (M/N)^(ξ-1) ≤ 4*P^η := by
    calc
      _ ≤ (4*P^η)^(ξ-1) := Real.rpow_le_rpow (by positivity) hratio (by linarith)
      _ ≤ (4*P^η)^1 := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = _ := Real.rpow_one _
  have hid : M^(1-ξ)*N^(2*ξ-1)*(M/N)^(ξ-1) = N^ξ := by
    rw [Real.div_rpow hM.le hN.le,div_eq_mul_inv,← Real.rpow_neg hN.le]
    calc
      _ = (M^(1-ξ)*M^(ξ-1))*(N^(2*ξ-1)*N^(-(ξ-1))) := by ring
      _ = _ := by
        rw [← Real.rpow_add hM,← Real.rpow_add hN]
        rw [show 1-ξ+(ξ-1)=0 by ring,show 2*ξ-1+ -(ξ-1)=ξ by ring,Real.rpow_zero,one_mul]
  have hterm : N^ξ ≤ (M^(1-ξ)*N^(2*ξ-1))*(4*P^η) := by
    rw [← hid]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hfirst : M ≤ (4*P^η)*M := le_mul_of_one_le_left hM.le (by linarith)
  nlinarith

theorem quadraticNorm_small_scale_bootstrap {ξ : ℝ} (hξ1 : 1 < ξ) (hξ2 : ξ ≤ 2)
    (hξ : ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : ℝ) (M N : ℕ),
      0 ≤ η → η ≤ ε/2 → 0 < M → 0 < N →
      (M : ℝ) ≤ 4*(N : ℝ)*((M : ℝ)*N)^η →
      quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N) ≤
        C*((M : ℝ)*N)^ε*((M : ℝ)+(M : ℝ)^(1-ξ)*(N : ℝ)^(2*ξ-1)) := by
  obtain ⟨C,hC,hbound⟩ := hξ (ε/2) (by positivity)
  refine ⟨4*C,by positivity,?_⟩
  intro η M N hη hηε hM hN hscale
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hP : 1 ≤ (M : ℝ)*N := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hM) (by exact_mod_cast hN)
  have hs := small_scale_exponent_budget hMp hNp hP hη hξ1.le hξ2 hscale
  have hp : ((M : ℝ)*N)^(ε/2)*((M : ℝ)*N)^η ≤ ((M : ℝ)*N)^ε := by
    rw [← Real.rpow_add (by positivity : 0 < (M : ℝ)*N)]
    exact Real.rpow_le_rpow_of_exponent_le hP (by linarith)
  calc
    _ ≤ C*((M : ℝ)*N)^(ε/2)*((M : ℝ)+(N : ℝ)^ξ) := hbound M N hM hN
    _ ≤ C*((M : ℝ)*N)^(ε/2)*(4*((M : ℝ)*N)^η*
        ((M : ℝ)+(M : ℝ)^(1-ξ)*(N : ℝ)^(2*ξ-1))) := by gcongr
    _ = (4*C)*(((M : ℝ)*N)^(ε/2)*((M : ℝ)*N)^η)*
        ((M : ℝ)+(M : ℝ)^(1-ξ)*(N : ℝ)^(2*ξ-1)) := by ring
    _ ≤ _ := by gcongr

end Ostmann.QuadraticSieve

end OAI
