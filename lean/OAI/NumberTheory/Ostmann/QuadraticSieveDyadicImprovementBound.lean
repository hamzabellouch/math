import OAI.NumberTheory.Ostmann.QuadraticSieveDyadicImprovementPower
import OAI.NumberTheory.Ostmann.QuadraticSieveExponentIteration

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

def DyadicRecursiveBound (ξ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 0 < M → 0 < N →
    quadraticNorm (dyadicSquarefreeRows M) (oddSquarefreeUpTo N) ≤
      C*((M:ℝ)*N)^ε*((M:ℝ)+(M:ℝ)^(1-ξ)*(N:ℝ)^(2*ξ-1))

theorem dyadic_exponentBound_of_recursive {ξ : ℝ} (hξ : 1 ≤ ξ)
    (hrec : DyadicRecursiveBound ξ) :
    ExponentBound (fun M N => quadraticNorm (dyadicSquarefreeRows M) (oddSquarefreeUpTo N))
      (2-1/ξ) := by
  intro ε hε
  let δ : ℝ := min (ε/10) (1/2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hδε : 5*δ ≤ ε := by have hh := min_le_left (ε/10) (1/2); dsimp [δ]; linarith
  obtain ⟨B,hB,hinflate⟩ := exists_inflated_dyadic_threshold δ hδ
  obtain ⟨Ca,hCa,hbound⟩ := hrec δ hδ
  let C : ℝ := 20*Ca*(2*B)^δ*(B+1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro M N hM hN
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  let P : ℝ := (M:ℝ)*N
  let X : ℝ := (N:ℝ)^((2*ξ-1)/ξ)
  have hP1 : 1 ≤ P := one_le_mul_of_one_le_of_one_le hM1 hN1
  have hPp : 0 < P := by linarith
  have hXbounds := recursion_threshold_between hN1 hξ
  have hX1 : 1 ≤ X := hN1.trans hXbounds.1
  obtain ⟨M',hM',hMM',hXM',hM'bound,hQ⟩ :=
    hinflate M N X hM hN hX1 (oddSquarefreeUpTo N) (by rfl)
  have hrecursive := hbound M' N hM' hN
  have herror : (M':ℝ)^(1-ξ)*(N:ℝ)^(2*ξ-1) ≤ X :=
    recursion_threshold_bound hN1 hξ hXM'
  have hprod : (M':ℝ)*N ≤ 2*B*P^4 :=
    inflated_dyadic_product_le hM1 hN1 hXbounds.2 hB.le hδ.le hδ1 hM'bound
  have hprodPow : ((M':ℝ)*N)^δ ≤ (2*B)^δ*P^(4*δ) := by
    have hh := Real.rpow_le_rpow (by positivity) hprod hδ.le
    rw [Real.mul_rpow (show (0:ℝ)≤2*B by positivity) (show 0≤P^4 by positivity),
      ← Real.rpow_natCast P 4,← Real.rpow_mul hPp.le] at hh
    exact hh
  have hsum : (M':ℝ)+X ≤ (B+1)*P^δ*((M:ℝ)+X) :=
    inflated_dyadic_sum_le hM1 hN1 (by linarith) hδ.le hM'bound
  have hsum' : (M':ℝ)+(M':ℝ)^(1-ξ)*(N:ℝ)^(2*ξ-1) ≤
      (B+1)*P^δ*((M:ℝ)+X) := by linarith
  rw [← recursion_threshold_exponent hξ]
  change quadraticNorm (dyadicSquarefreeRows M) (oddSquarefreeUpTo N) ≤ C*P^ε*((M:ℝ)+X)
  calc
    _ ≤ 20*(Ca*((M':ℝ)*N)^δ*((M':ℝ)+(M':ℝ)^(1-ξ)*(N:ℝ)^(2*ξ-1))) :=
      hQ.trans (mul_le_mul_of_nonneg_left hrecursive (by norm_num))
    _ ≤ 20*(Ca*((2*B)^δ*P^(4*δ))*((B+1)*P^δ*((M:ℝ)+X))) := by gcongr
    _ = C*P^(5*δ)*((M:ℝ)+X) := by
      dsimp [C]
      rw [show 5*δ=4*δ+δ by ring,Real.rpow_add hPp]
      ring
    _ ≤ _ := by
      have hh := Real.rpow_le_rpow_of_exponent_le hP1 hδε
      gcongr

end Ostmann.QuadraticSieve

end

end OAI
