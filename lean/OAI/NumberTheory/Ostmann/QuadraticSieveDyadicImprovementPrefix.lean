import OAI.NumberTheory.Ostmann.QuadraticSieveDyadicImprovementBound
import OAI.NumberTheory.Ostmann.QuadraticSieveDyadicImprovementCover

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

theorem exponentBound_prefix_of_dyadic {ξ : ℝ} (hξ : 1 ≤ ξ)
    (hd : ExponentBound (fun M N => quadraticNorm (dyadicSquarefreeRows M) (oddSquarefreeUpTo N)) ξ) :
    ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ := by
  intro ε hε
  let δ : ℝ := ε/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Ca,hCa,hbound⟩ := hd δ hδ
  obtain ⟨Cd,hCd,hdepth⟩ := squarefree_dyadic_depth_le_rpow δ hδ
  refine ⟨2*Cd*(Ca+1),by positivity,?_⟩
  intro M N hM hN
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  let P : ℝ := (M:ℝ)*N
  let X : ℝ := (N:ℝ)^ξ
  have hP1 : 1 ≤ P := one_le_mul_of_one_le_of_one_le hM1 hN1
  have hPp : 0 < P := by linarith
  have hp1 : 1 ≤ P^δ := Real.one_le_rpow hP1 hδ.le
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hNX : (N:ℝ) ≤ X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 hξ
  have hblock : ∀ j ∈ Finset.range (Nat.log 2 M+2),
      quadraticNorm (dyadicPrefixCover j) (oddSquarefreeUpTo N) ≤ (Ca+1)*P^δ*((M:ℝ)+X) := by
    intro j hj
    by_cases hj0 : j=0
    · subst j
      simp only [dyadicPrefixCover,ite_true]
      have hprod : 1 ≤ (Ca+1)*P^δ := one_le_mul_of_one_le_of_one_le (by linarith) hp1
      have hsum : (M:ℝ)+X ≤ ((Ca+1)*P^δ)*((M:ℝ)+X) :=
        le_mul_of_one_le_left (by positivity) hprod
      exact (quadraticNorm_row_one_le N).trans (by nlinarith)
    · rw [dyadicPrefixCover,ite_eq_right hj0]
      have hb := dyadicPrefixCover_base_le hM hj hj0
      have hbp : 0 < (2:ℕ)^(j-1) := by positivity
      have hbr : (2:ℝ)^(j-1) ≤ M := by exact_mod_cast hb
      calc
        _ ≤ Ca*(((2:ℕ)^(j-1):ℝ)*N)^δ*(((2:ℕ)^(j-1):ℝ)+X) :=
          by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hbound _ N hbp hN
        _ ≤ Ca*P^δ*((M:ℝ)+X) := by dsimp [P]; gcongr
        _ ≤ _ := by gcongr; linarith
  have hMP : (M:ℝ) ≤ P := le_mul_of_one_le_right (by positivity) hN1
  have hMpow : (M:ℝ)^δ ≤ P^δ := Real.rpow_le_rpow (by positivity) hMP hδ.le
  have hdep := hdepth M hM
  have hdep' : ((Nat.log 2 M+2:ℕ):ℝ) ≤ 2*Cd*P^δ := by
    have hh := mul_le_mul_of_nonneg_left hMpow hCd.le
    push_cast at hdep ⊢
    nlinarith
  calc
    _ ≤ ∑ j ∈ Finset.range (Nat.log 2 M+2), quadraticNorm (dyadicPrefixCover j) (oddSquarefreeUpTo N) :=
      quadraticNorm_prefix_le_dyadic_cover M N
    _ ≤ ∑ _j ∈ Finset.range (Nat.log 2 M+2), (Ca+1)*P^δ*((M:ℝ)+X) := Finset.sum_le_sum hblock
    _ = ((Nat.log 2 M+2:ℕ):ℝ)*((Ca+1)*P^δ*((M:ℝ)+X)) := by simp
    _ ≤ (2*Cd*P^δ)*((Ca+1)*P^δ*((M:ℝ)+X)) := by gcongr
    _ = _ := by
      change _ = 2*Cd*(Ca+1)*P^ε*((M:ℝ)+X)
      rw [show ε=δ+δ by dsimp [δ]; ring,Real.rpow_add hPp]
      ring

theorem quadraticNorm_exponent_improvement_of_dyadic_recursive {ξ : ℝ}
    (hξ : 1 ≤ ξ) (hrec : DyadicRecursiveBound ξ) :
    ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) (2-1/ξ) := by
  have hξp : 0 < ξ := by linarith
  have hr : 1 ≤ (2*ξ-1)/ξ := (le_div_iff₀ hξp).mpr (by linarith)
  rw [recursion_threshold_exponent hξ] at hr
  exact exponentBound_prefix_of_dyadic hr (dyadic_exponentBound_of_recursive hξ hrec)

end Ostmann.QuadraticSieve

end

end OAI
