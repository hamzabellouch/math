import OAI.NumberTheory.Ostmann.QuadraticSieveExponentIterationBasic
import OAI.NumberTheory.Ostmann.QuadraticSieveExponentIterationThreshold

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

def ExponentBound (B : ℕ → ℕ → ℝ) (ξ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 0 < M → 0 < N →
    B M N ≤ C * ((M : ℝ) * N)^ε * ((M : ℝ) + (N : ℝ)^ξ)

theorem exponent_sum_absorb {M N ξ δ : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hδ : 0 ≤ δ) (hξ : ξ ≤ 1+δ) :
    M+N^ξ ≤ (M*N)^δ*(M+N) := by
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hNp : 0 < N := by linarith
  have hMN : 1 ≤ M*N := one_le_mul_of_one_le_of_one_le hM hN
  have hfirst : M ≤ M*(M*N)^δ :=
    le_mul_of_one_le_right hM0 (Real.one_le_rpow hMN hδ)
  have hbase : N ≤ M*N := le_mul_of_one_le_left hN0 hM
  have hp : N^δ ≤ (M*N)^δ := Real.rpow_le_rpow hN0 hbase hδ
  have hsecond : N^ξ ≤ N*(M*N)^δ := by
    calc
      N^ξ ≤ N^(1+δ) := Real.rpow_le_rpow_of_exponent_le hN hξ
      _ = N*N^δ := by rw [Real.rpow_add hNp,Real.rpow_one]
      _ ≤ N*(M*N)^δ := mul_le_mul_of_nonneg_left hp hN0
  nlinarith

theorem exponentBound_one_of_improvement (B : ℕ → ℕ → ℝ) (hinit : ExponentBound B 2)
    (himprove : ∀ ξ, 1 < ξ → ξ ≤ 2 → ExponentBound B ξ → ExponentBound B (2-1/ξ)) :
    ExponentBound B 1 := by
  intro ε hε
  let δ : ℝ := ε/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨r,hr⟩ := exists_descentExponent_le hδ
  have hPr := property_at_descentExponent (ExponentBound B) hinit himprove r
  obtain ⟨C,hC,hbound⟩ := hPr δ hδ
  refine ⟨C,hC,?_⟩
  intro M N hM hN
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hMNp : 0 < (M:ℝ)*N := by positivity
  have hp : (((M:ℝ)*N)^δ)*(((M:ℝ)*N)^δ) = ((M:ℝ)*N)^ε := by
    rw [← Real.rpow_add hMNp]
    congr 1
    dsimp [δ]
    ring
  have hs := exponent_sum_absorb hM1 hN1 hδ.le hr
  have hfinal : B M N ≤ C*((M:ℝ)*N)^ε*((M:ℝ)+N) := by
    calc
      B M N ≤ C*((M:ℝ)*N)^δ*((M:ℝ)+(N:ℝ)^descentExponent r) := hbound M N hM hN
      _ ≤ C*((M:ℝ)*N)^δ*(((M:ℝ)*N)^δ*((M:ℝ)+N)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = C*((((M:ℝ)*N)^δ)*(((M:ℝ)*N)^δ))*((M:ℝ)+N) := by ring
      _ = _ := by rw [hp]
  simpa only [Real.rpow_one] using hfinal

theorem epsilon_bound_of_exponent_improvement (B : ℕ → ℕ → ℝ)
    (hinit : ExponentBound B 2)
    (himprove : ∀ ξ, 1 < ξ → ξ ≤ 2 → ExponentBound B ξ → ExponentBound B (2-1/ξ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 0 < M → 0 < N →
      B M N ≤ C*((M:ℝ)*N)^ε*((M:ℝ)+N) := by
  simpa only [Real.rpow_one] using (exponentBound_one_of_improvement B hinit himprove) ε hε

end Ostmann.QuadraticSieve

end

end OAI
