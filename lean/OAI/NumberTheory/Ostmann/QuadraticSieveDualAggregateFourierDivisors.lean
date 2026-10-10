import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateDyadic
import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateFourierBoundary
import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateFourierScale

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate
open scoped SchwartzMap FourierTransform

theorem dual_fourier_divisor_sum_bound (W : 𝓢(ℝ,ℂ)) (σ δ : ℝ)
    (hσ : 0 < σ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P M H T x R A : ℝ) (K j e N : ℕ)
      (S : Finset ℕ) (a : ℕ → ℂ) (s : ℤ) (g : ℕ → ℕ → ℂ),
      1 ≤ P → 0 < M → M ≤ P → 0 < H → 1 ≤ T → 0 ≤ x → 0 ≤ R → 0 ≤ A →
      0 < K → 0 < e → 0 < N → (N : ℝ) ≤ P → (K : ℝ) ≤ P^3 →
      j ∈ Finset.range (Nat.log 2 K+1) →
      (N : ℝ) ≤ 2*H → S ⊆ oddSquarefreeUpTo N → (∀ n ∈ S, H ≤ (n : ℝ)) →
      s ∈ signedSquarefreeMultipliers →
      (∀ q : ℕ, 0 < q → quadraticNorm (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/q)) ≤
        R*(x+(N : ℝ)/q)) →
      (∀ d, ∀ v ∈ binarySquarefreeRows K j, ‖g d v‖ ≤ A) →
      (∀ d, ∀ v ∈ binarySquarefreeRows K j, g d v ≠ 0 → dualWindowLower M H T e v < (d : ℝ)) →
      ‖∑ d ∈ Finset.Icc 1 (N^2), ∑ v ∈ binarySquarefreeRows K j,
        ((Real.sqrt (M/((e : ℝ)*v))/d : ℝ) : ℂ)*g d v*
          (∑ l ∈ nonzeroIntegerCutoff (16*T^2), dualAggregateFourierRow W M e S a s l d v)‖ ≤
        (Nat.log 2 (N^2)+2 : ℕ)*(16*A*C*T^3*R)*(N : ℝ)^δ*
          (2*Real.sqrt 2*P^4)^σ*(M+Real.sqrt (M/(2^j : ℕ))*x)*coefficientEnergy S a := by
  obtain ⟨Ca,hCa,ha⟩ := dual_fourier_active_range_bound W σ δ hσ hδ
  obtain ⟨Cb,hCb,hb⟩ := dual_fourier_active_boundary_bound W σ δ hσ hδ
  refine ⟨Ca+Cb,by positivity,?_⟩
  intro P M H T x R A K j e N S a s g hP hM hMP hH hT hx hR hA hK he hN hNP hKP hj hNH hS hSH hs hnorm hg hsupp
  have hbase := binary_base_le_cutoff hK hj
  have hE := coefficientEnergy_nonneg S a
  let B : ℝ := (16*A*(Ca+Cb)*T^3*R)*(N : ℝ)^δ*(2*Real.sqrt 2*P^4)^σ*
    (M+Real.sqrt (M/(2^j : ℕ))*x)*coefficientEnergy S a
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfirst : ‖∑ v ∈ binarySquarefreeRows K j,
      ((Real.sqrt (M/((e : ℝ)*v))/(1 : ℕ) : ℝ) : ℂ)*g 1 v*
        (∑ l ∈ nonzeroIntegerCutoff (16*T^2), dualAggregateFourierRow W M e S a s l 1 v)‖ ≤ B := by
    have hh := hb M H T x R A K j e N S a s (g 1) hM hH hT hx hR hA he hN hNH hS hSH hs
      hnorm (hg 1) (by simpa only [Nat.cast_one] using hsupp 1)
    have hscale := Real.rpow_le_rpow (by positivity : 0 ≤ Real.sqrt (2*(2^j : ℕ))*Real.sqrt (M/e))
      (dual_fourier_ambient_boundary_scale_le hP hM hMP he hN hNP hKP hbase) hσ.le
    simp only [Nat.cast_one]
    apply hh.trans
    dsimp [B]
    gcongr
    linarith
  have hblock (k : ℕ) (hk : k ∈ Finset.range (Nat.log 2 (N^2)+1)) :
      ‖∑ d ∈ aggregateDivisorBlock (N^2) k, ∑ v ∈ binarySquarefreeRows K j,
        ((Real.sqrt (M/((e : ℝ)*v))/d : ℝ) : ℂ)*g d v*
          (∑ l ∈ nonzeroIntegerCutoff (16*T^2), dualAggregateFourierRow W M e S a s l d v)‖ ≤ B := by
    let g' : ℕ → ℕ → ℂ := fun d v => if d ≤ N^2 then g d v else 0
    have hg' : ∀ d ∈ Finset.Ioc (2^k : ℕ) (2*2^k), ∀ v ∈ binarySquarefreeRows K j, ‖g' d v‖ ≤ A := by
      intro d hd v hv
      dsimp [g']
      split_ifs with hdN
      · exact hg d v hv
      · simpa using hA
    have hs' : ∀ d ∈ Finset.Ioc (2^k : ℕ) (2*2^k), ∀ v ∈ binarySquarefreeRows K j, g' d v ≠ 0 →
        dualWindowLower M H T e v < (d : ℝ) := by
      intro d hd v hv hnz
      have hh : g d v ≠ 0 := by
        intro hz
        apply hnz
        simp [g',hz]
      exact hsupp d v hv hh
    have hh := ha M H T x R A K j e (2^k) N S a s g' hM hH hT hx hR hA he (by positivity) hN
      hNH hS hSH hs hnorm hg' hs'
    have heq : (∑ d ∈ aggregateDivisorBlock (N^2) k, ∑ v ∈ binarySquarefreeRows K j,
        ((Real.sqrt (M/((e : ℝ)*v))/d : ℝ) : ℂ)*g d v*
          (∑ l ∈ nonzeroIntegerCutoff (16*T^2), dualAggregateFourierRow W M e S a s l d v)) =
        ∑ d ∈ Finset.Ioc (2^k : ℕ) (2*2^k), ∑ v ∈ binarySquarefreeRows K j,
        ((Real.sqrt (M/((e : ℝ)*v))/d : ℝ) : ℂ)*g' d v*
          (∑ l ∈ nonzeroIntegerCutoff (16*T^2), dualAggregateFourierRow W M e S a s l d v) := by
      rw [aggregateDivisorBlock,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdN : d ≤ N^2 <;> simp [g',hdN]
    rw [heq]
    apply hh.trans
    have hD := binary_base_le_cutoff (by positivity : 0 < N^2) hk
    have hscale := Real.rpow_le_rpow (by positivity : 0 ≤
      (((2*(2^k) : ℕ) : ℝ)*Real.sqrt (2*(2^j : ℕ))*Real.sqrt (M/e)))
      (dual_fourier_ambient_scale_le hP hM hMP he hNP hKP hD hbase) hσ.le
    dsimp [B]
    gcongr
    linarith
  have hh := norm_sum_Icc_one_le_boundary_dyadic (N^2) (by positivity)
    (fun d => ∑ v ∈ binarySquarefreeRows K j,
      ((Real.sqrt (M/((e : ℝ)*v))/d : ℝ) : ℂ)*g d v*
        (∑ l ∈ nonzeroIntegerCutoff (16*T^2), dualAggregateFourierRow W M e S a s l d v)) B hfirst hblock
  convert hh using 1
  dsimp [B]
  ring

end Ostmann.QuadraticSieve

end OAI
