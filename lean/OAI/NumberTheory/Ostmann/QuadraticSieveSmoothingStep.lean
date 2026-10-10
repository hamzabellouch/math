import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothingRecursionSupport
import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothingSliceBootstrap
import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothingStepDefinition

namespace OAI

namespace Ostmann.QuadraticSieve

theorem smoothingStepBound_of_exponentBound {ξ : ℝ} (hξ1 : 1 < ξ) (hξ2 : ξ ≤ 2)
    (hξ : ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ) :
    SmoothingStepBound ξ := by
  intro δ hδ η hη hηδ
  have hδ2 : 0 < δ/2 := by positivity
  have hη2 : 0 < η/2 := by positivity
  obtain ⟨Cs,hCs,hslice⟩ := smoothing_small_gcd_binary_slice_bound hξ1 hξ2 hξ
    (δ/2) (η/2) hδ2 hη2 (by linarith)
  obtain ⟨Cg,hCg,hgcd⟩ := smoothing_large_gcd_removal (δ/2) hδ2
  obtain ⟨Cl,hCl,hdepth⟩ := squarefree_dyadic_depth_le_rpow (δ/2) hδ2
  let A : ℝ := 6+Cs+Cg
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨Cl*A,by positivity,?_⟩
  intro M K N₀ D n hM hK hN₀ hD hn hnN hNM hKM hcut hsqrt
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hN₀r : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  let P : ℝ := (M : ℝ)*N₀
  let U : ℝ := (M : ℝ)+Real.sqrt (M : ℝ)*(K : ℝ)^(ξ-1/2)
  let X : ℝ := smoothingNorm M K (oddSquarefreeUpTo (n/D))
  let Y : ℝ := (D : ℝ)^5*U
  have hP : 1 ≤ P := one_le_mul_of_one_le_of_one_le hMr hN₀r
  have hPp : 0 < P := by linarith
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hMU : (M : ℝ) ≤ U := le_add_of_nonneg_right (by positivity)
  have hX : 0 ≤ X := smoothingNorm_nonneg _ _ _
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hXY : 0 ≤ X+Y := add_nonneg hX hY
  have hPpow : 1 ≤ P^(δ/2) := Real.one_le_rpow hP hδ2.le
  have hnP : (n : ℝ) ≤ P := by
    have hnn : (n : ℝ) ≤ N₀ := by exact_mod_cast hnN
    have hNP : (N₀ : ℝ) ≤ P := by dsimp [P]; nlinarith
    exact hnn.trans hNP
  have hnpow : (n : ℝ)^(δ/2) ≤ P^(δ/2) := Real.rpow_le_rpow (Nat.cast_nonneg _) hnP hδ2.le
  have hcut' : (2*(N₀ : ℝ)^2/M)*((M : ℝ)*N₀)^(η/2) ≤ K := by
    apply le_trans _ hcut
    apply mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP (by linarith)) (by positivity)
  have hD25 : (D : ℝ)^2 ≤ (D : ℝ)^5 := by
    calc
      _ ≤ (D : ℝ)^2*(D : ℝ)^3 := le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ hDr)
      _ = _ := by ring
  have hsmall : 6*(M : ℝ)*(D : ℝ)^2 ≤ A*P^(δ/2)*(X+Y) := by
    have h6A : 6 ≤ A := by dsimp [A]; linarith
    calc
      _ ≤ 6*U*(D : ℝ)^5 := by gcongr
      _ = 6*Y := by dsimp [Y]; ring
      _ ≤ A*Y := mul_le_mul_of_nonneg_right h6A hY
      _ ≤ (A*P^(δ/2))*(X+Y) := mul_le_mul
        (le_mul_of_one_le_right hA.le hPpow) (le_add_of_nonneg_left hX) hY (by positivity)
  have hblock (j : ℕ) : smoothingNorm M K (binarySquarefreeRows n j) ≤ A*P^(δ/2)*(X+Y) := by
    by_cases hsmallj : 2^j ≤ D^2
    · exact (smoothingNorm_small_binary_le M K n j D hsmallj).trans hsmall
    by_cases hne : (binarySquarefreeRows n j).Nonempty
    · apply weightedNumeratorNorm_le_of_bound _ _ _ (by positivity)
      intro a
      let E : ℝ := coefficientEnergy (binarySquarefreeRows n j) a
      have hE : 0 ≤ E := coefficientEnergy_nonneg _ _
      have hsum : (∑ d ∈ Finset.Icc 1 D,
          ‖weightedGcdCorrelation (smoothingRows M K) (binarySquarefreeRows n j)
            (smoothingWeight M) a d‖) ≤ Cs*P^(δ/2)*Y*E := by
        calc
          _ ≤ ∑ d ∈ Finset.Icc 1 D, Cs*P^(δ/2)*(D : ℝ)^4*U*E := by
            apply Finset.sum_le_sum
            intro d hd
            have hp := hslice M K N₀ D n j d a hM hK hN₀ hD hn
              (Finset.mem_Icc.mp hd).1 hnN hNM hKM hcut' hsqrt
              (lt_of_not_ge hsmallj) hne (Finset.mem_Icc.mp hd).2
            apply hp.trans
            dsimp only [P,U,E]
            gcongr
            exact_mod_cast (Finset.mem_Icc.mp hd).2
          _ = _ := by simp only [Finset.sum_const,Nat.card_Icc,nsmul_eq_mul]; dsimp [Y]; ring
      have hg := hgcd M K n D (binarySquarefreeRows n j) a (Finset.filter_subset _ _) hD
      change weightedNumeratorEnergy _ _ _ a ≤ _
      change smoothingEnergy M K (binarySquarefreeRows n j) a ≤ _
      calc
        _ ≤ (∑ d ∈ Finset.Icc 1 D,
            ‖weightedGcdCorrelation (smoothingRows M K) (binarySquarefreeRows n j)
              (smoothingWeight M) a d‖) + Cg*(n : ℝ)^(δ/2)*X*E := hg
        _ ≤ Cs*P^(δ/2)*Y*E+Cg*P^(δ/2)*X*E := by gcongr
        _ ≤ A*P^(δ/2)*(X+Y)*E := by
          have hsA : Cs ≤ A := by dsimp [A]; linarith
          have hgA : Cg ≤ A := by dsimp [A]; linarith
          have hh := add_le_add
            (mul_le_mul_of_nonneg_right hsA (show 0 ≤ P^(δ/2)*Y*E by positivity))
            (mul_le_mul_of_nonneg_right hgA (show 0 ≤ P^(δ/2)*X*E by positivity))
          convert hh using 1 <;> ring
    · have hz : binarySquarefreeRows n j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hh := smoothingNorm_le_trivial M K (binarySquarefreeRows n j)
      rw [hz,Finset.card_empty,Nat.cast_zero,mul_zero] at hh
      rw [hz]
      exact hh.trans (show 0 ≤ A*P^(δ/2)*(X+Y) by positivity)
  obtain ⟨j,hj,hjbound⟩ := exists_smoothingNorm_binary_control M K n
  have hdepthP : (Nat.log 2 n+1 : ℕ) ≤ Cl*P^(δ/2) :=
    (hdepth n hn).trans (mul_le_mul_of_nonneg_left hnpow hCl.le)
  calc
    _ ≤ (Nat.log 2 n+1 : ℕ)*smoothingNorm M K (binarySquarefreeRows n j) := hjbound
    _ ≤ (Cl*P^(δ/2))*(A*P^(δ/2)*(X+Y)) :=
      mul_le_mul hdepthP (hblock j) (smoothingNorm_nonneg _ _ _) (by positivity)
    _ = (Cl*A)*(P^(δ/2)*P^(δ/2))*(X+Y) := by ring
    _ = _ := by
      rw [← Real.rpow_add hPp,show δ/2+δ/2=δ by ring]

end Ostmann.QuadraticSieve

end OAI
