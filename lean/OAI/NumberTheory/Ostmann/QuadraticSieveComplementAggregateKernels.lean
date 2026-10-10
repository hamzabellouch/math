import OAI.NumberTheory.Ostmann.QuadraticSieveComplementCorrelations
import OAI.NumberTheory.Ostmann.QuadraticSieveComplementRangeBootstrap
import OAI.NumberTheory.Ostmann.QuadraticSieveComplementWindows

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open ComplexConjugate
open scoped SchwartzMap FourierTransform ArithmeticFunction.Moebius

def complementLargeScalar (M T : ℝ) (Δ r d v : ℕ) : ℂ :=
  if Nat.Coprime v Δ ∧ complementWindowUpper M T v < (r*d : ℕ) then 1 else 0

def complementFourierScalar (W : 𝓢(ℝ,ℂ)) (M T : ℝ) (Δ r d v : ℕ) : ℂ :=
  if Nat.Coprime v Δ ∧ complementWindowLower M T v < (r*d : ℕ) ∧
      (r*d : ℕ) ≤ complementWindowUpper M T v then
    ∑ t ∈ nonzeroIntegerCutoff (16*T^2),
      𝓕 (squarePullback W 1 (by norm_num)) ((t:ℝ)*(Real.sqrt (M/v)/(r*d : ℕ)))
  else 0

def complementFourierBound (W : 𝓢(ℝ,ℂ)) : ℝ :=
  (SchwartzMap.seminorm ℝ 0 0) (𝓕 (squarePullback W 1 (by norm_num))) + 1

theorem complementFourierBound_pos (W : 𝓢(ℝ,ℂ)) : 0 < complementFourierBound W := by
  have hh := apply_nonneg (SchwartzMap.seminorm ℝ 0 0) (𝓕 (squarePullback W 1 (by norm_num)))
  unfold complementFourierBound
  linarith

theorem complementLargeScalar_norm_le (M T : ℝ) (Δ r d v : ℕ) :
    ‖complementLargeScalar M T Δ r d v‖ ≤ 1 := by
  unfold complementLargeScalar
  split_ifs <;> norm_num

theorem complementFourierScalar_norm_le (W : 𝓢(ℝ,ℂ)) (M T : ℝ) (Δ r d v : ℕ) :
    ‖complementFourierScalar W M T Δ r d v‖ ≤
      complementFourierBound W * (nonzeroIntegerCutoff (16*T^2)).card := by
  unfold complementFourierScalar
  split_ifs
  · apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _t ∈ nonzeroIntegerCutoff (16*T^2), complementFourierBound W := by
        apply Finset.sum_le_sum
        intro t ht
        exact (SchwartzMap.norm_le_seminorm ℝ (𝓕 (squarePullback W 1 (by norm_num))) _).trans
          (by unfold complementFourierBound; linarith)
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,mul_comm]
  · simp only [norm_zero]
    exact mul_nonneg (complementFourierBound_pos W).le (Nat.cast_nonneg _)

theorem complementaryLargeCorrection_eq_scalar (M T : ℝ) (I : ℂ) (K Δ N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    complementaryLargeCorrection M I K Δ N S a (complementWindowUpper M T) =
      -I * ∑ r ∈ (2*Δ).divisors, ∑ d ∈ Finset.Icc 1 (N^2), ∑ v ∈ oddSquarefreeUpTo K,
        (μ r:ℂ)*(μ d:ℂ)*((Real.sqrt (M/v)/((r:ℝ)*d):ℝ):ℂ)*
          complementLargeScalar M T Δ r d v*
            coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v:ℤ) := by
  classical
  unfold complementaryLargeCorrection
  congr 1
  have he (v : ℕ) :
      (if Nat.Coprime v Δ then (Real.sqrt (M/v):ℂ)*
        ∑ r ∈ (2*Δ).divisors, ∑ d ∈ Finset.Icc 1 (N^2),
          (μ r:ℂ)*(μ d:ℂ)*complementLargeKernel (complementWindowUpper M T) v (r*d)*
            coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v:ℤ) else 0) =
        ∑ r ∈ (2*Δ).divisors, ∑ d ∈ Finset.Icc 1 (N^2),
          (μ r:ℂ)*(μ d:ℂ)*((Real.sqrt (M/v)/((r:ℝ)*d):ℝ):ℂ)*
            complementLargeScalar M T Δ r d v*
              coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v:ℤ) := by
    by_cases hc : Nat.Coprime v Δ
    · rw [ite_eq_left hc]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hd' : complementWindowUpper M T v < (r*d:ℕ)
      · unfold complementLargeKernel complementLargeScalar
        rw [ite_eq_left hd',ite_eq_left (show Nat.Coprime v Δ ∧
          complementWindowUpper M T v < (r*d:ℕ) from ⟨hc,hd'⟩)]
        push_cast
        ring
      · unfold complementLargeKernel complementLargeScalar
        rw [ite_eq_right hd',ite_eq_right (show ¬(Nat.Coprime v Δ ∧
          complementWindowUpper M T v < (r*d:ℕ)) from fun h => hd' h.2)]
        simp
    · simp [hc,complementLargeScalar]
  rw [Finset.sum_congr rfl (fun v hv => he v),Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  exact Finset.sum_comm

theorem complementaryFourierCorrection_eq_scalar (W : 𝓢(ℝ,ℂ)) (M T : ℝ) (K Δ N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    complementaryFourierCorrection W M K Δ N S a (complementWindowLower M T)
      (complementWindowUpper M T) (fun _ => 16*T^2) =
      (1/2:ℂ) * ∑ r ∈ (2*Δ).divisors, ∑ d ∈ Finset.Icc 1 (N^2), ∑ v ∈ oddSquarefreeUpTo K,
        (μ r:ℂ)*(μ d:ℂ)*((Real.sqrt (M/v)/((r:ℝ)*d):ℝ):ℂ)*
          complementFourierScalar W M T Δ r d v*
            coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v:ℤ) := by
  classical
  unfold complementaryFourierCorrection
  congr 1
  have he (v : ℕ) :
      (if Nat.Coprime v Δ then ∑ r ∈ (2*Δ).divisors, ∑ d ∈ Finset.Icc 1 (N^2),
        (μ r:ℂ)*(μ d:ℂ)*complementFourierKernel W M
          (complementWindowLower M T) (complementWindowUpper M T) (fun _ => 16*T^2) v (r*d)*
          coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v:ℤ) else 0) =
      ∑ r ∈ (2*Δ).divisors, ∑ d ∈ Finset.Icc 1 (N^2),
        (μ r:ℂ)*(μ d:ℂ)*((Real.sqrt (M/v)/((r:ℝ)*d):ℝ):ℂ)*
          complementFourierScalar W M T Δ r d v*
            coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v:ℤ) := by
    by_cases hc : Nat.Coprime v Δ
    · rw [ite_eq_left hc]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro d hd
      unfold complementFourierKernel complementFourierScalar
      by_cases hg : complementWindowLower M T v < (r*d:ℕ) ∧
          (r*d:ℕ) ≤ complementWindowUpper M T v
      · rw [ite_eq_left hg,ite_eq_left (show Nat.Coprime v Δ ∧
          complementWindowLower M T v < (r*d:ℕ) ∧ (r*d:ℕ) ≤ complementWindowUpper M T v from ⟨hc,hg⟩)]
        push_cast
        ring
      · rw [ite_eq_right hg,ite_eq_right (show ¬(Nat.Coprime v Δ ∧
          complementWindowLower M T v < (r*d:ℕ) ∧ (r*d:ℕ) ≤ complementWindowUpper M T v) from fun h => hg h.2)]
        simp
    · simp [hc,complementFourierScalar]
  rw [Finset.sum_congr rfl (fun v hv => he v),Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  exact Finset.sum_comm

end Ostmann.QuadraticSieve

end

end OAI
