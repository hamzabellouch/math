import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateBlocks
import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateNormBlocks
import OAI.NumberTheory.Ostmann.QuadraticSieveFourierRange

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory ComplexConjugate
open scoped SchwartzMap FourierTransform

noncomputable def dualAggregateFourierRow (W : 𝓢(ℝ,ℂ)) (M : ℝ) (e : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (s l : ℤ) (d v : ℕ) : ℂ :=
  ∑ n ∈ S, ∑ t ∈ S,
    rootGaussMellinKernel a (fun n => conj (a n)) ((e : ℤ)*s) d v n t *
      𝓕 (dualSignedSquareWeight W s)
        (((l : ℝ)*Real.sqrt ((e : ℝ)/M))*Real.sqrt ((n : ℝ)*t)/((d : ℝ)*Real.sqrt v))

theorem norm_weighted_three_le {ι κ ν : Type*} (D : Finset ι) (V : Finset κ) (L : Finset ν)
    (w : ι → κ → ℂ) (f : ν → ι → κ → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hw : ∀ d ∈ D, ∀ v ∈ V, ‖w d v‖ ≤ A) :
    ‖∑ d ∈ D, ∑ v ∈ V, w d v*(∑ l ∈ L, f l d v)‖ ≤
      A*∑ l ∈ L, ∑ d ∈ D, ∑ v ∈ V, ‖f l d v‖ := by
  apply (norm_weighted_rectangle_le D V w (fun d v => ∑ l ∈ L, f l d v) A hA hw).trans
  apply mul_le_mul_of_nonneg_left _ hA
  calc
    _ ≤ ∑ d ∈ D, ∑ v ∈ V, ∑ l ∈ L, ‖f l d v‖ := by
      exact Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun v hv => norm_sum_le _ _))
    _ = ∑ d ∈ D, ∑ l ∈ L, ∑ v ∈ V, ‖f l d v‖ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem dual_fourier_active_range_bound (W : 𝓢(ℝ,ℂ)) (σ δ : ℝ)
    (hσ : 0 < σ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M H T x R A : ℝ) (K j e D N : ℕ)
      (S : Finset ℕ) (a : ℕ → ℂ) (s : ℤ) (g : ℕ → ℕ → ℂ),
      0 < M → 0 < H → 1 ≤ T → 0 ≤ x → 0 ≤ R → 0 ≤ A → 0 < e → 0 < D → 0 < N →
      (N : ℝ) ≤ 2*H → S ⊆ oddSquarefreeUpTo N → (∀ n ∈ S, H ≤ (n : ℝ)) →
      s ∈ signedSquarefreeMultipliers →
      (∀ q : ℕ, 0 < q → quadraticNorm (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/q)) ≤
        R*(x+(N : ℝ)/q)) →
      (∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ binarySquarefreeRows K j, ‖g d v‖ ≤ A) →
      (∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ binarySquarefreeRows K j, g d v ≠ 0 →
        dualWindowLower M H T e v < (d : ℝ)) →
      ‖∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ binarySquarefreeRows K j,
        ((Real.sqrt (M/((e : ℝ)*v))/d : ℝ) : ℂ)*g d v*
          (∑ l ∈ nonzeroIntegerCutoff (16*T^2), dualAggregateFourierRow W M e S a s l d v)‖ ≤
        (16*A*C*T^3*R)*(N : ℝ)^δ*
          (((2*D : ℕ) : ℝ)*Real.sqrt (2*(2^j : ℕ))*Real.sqrt (M/e))^σ*
          (M+Real.sqrt (M/(2^j : ℕ))*x)*coefficientEnergy S a := by
  obtain ⟨C,hC,hbound⟩ := dual_fourier_frequency_divisor_range_bound W σ δ hσ hδ
  refine ⟨C,hC,?_⟩
  intro M H T x R A K j e D N S a s g hM hH hT hx hR hA he hD hN hNH hS hSH hs hnorm hg hsupp
  have hTp : 0 < T := by linarith
  have hep : (0 : ℝ) < e := by exact_mod_cast he
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  have hB : (0 : ℝ) < (2^j : ℕ) := by positivity
  have hrows : ∀ v ∈ binarySquarefreeRows K j, 0 < v ∧ Odd v ∧ (v : ℝ) ≤ 2*(2^j : ℕ) := by
    intro v hv
    obtain ⟨hv',hlo,hhi⟩ := Finset.mem_filter.mp hv
    have hsf := mem_oddSquarefreeUpTo.mp hv'
    refine ⟨hsf.1,hsf.2.2.1,?_⟩
    exact_mod_cast (show v ≤ 2*(2^j : ℕ) by simpa only [pow_succ,mul_comm] using hhi.le)
  have hE := coefficientEnergy_nonneg S a
  by_cases hactive : ∃ d ∈ Finset.Ioc D (2*D), ∃ v ∈ binarySquarefreeRows K j, g d v ≠ 0
  · obtain ⟨d,hd,v,hv,hnz⟩ := hactive
    obtain ⟨p,hp,hrow⟩ := hbound M e D N T (2*(2^j : ℕ)) H
      (binarySquarefreeRows K j) S a hM he hD hN hT (by positivity) hH hrows hS hSH
    obtain ⟨hp1,hp2,hplo,hphi,hpu1,hpu2⟩ := mem_divisorRangeScales.mp hp
    have hp1r : (1 : ℝ) ≤ p.1 := by exact_mod_cast hp1
    have hp2r : (1 : ℝ) ≤ p.2 := by exact_mod_cast hp2
    have hPr : (0 : ℝ) < (p.1 : ℝ)*p.2 := by positivity
    have hPD : (p.1 : ℝ)*p.2 ≤ 2*D := by exact_mod_cast hphi
    have hdcut := hsupp d hd v hv hnz
    rw [dualWindowLower, squarefreeDyadicBase_eq_of_mem hv] at hdcut
    have hdD : (d : ℝ) ≤ 2*D := by exact_mod_cast (Finset.mem_Ioc.mp hd).2
    have hcut : Real.sqrt ((e : ℝ)*H^2/(M*(2^j : ℕ))) ≤ 4*T*D := by
      have hh := (div_lt_iff₀ (show 0 < 2*T by positivity)).mp hdcut
      have hmul := mul_le_mul_of_nonneg_right hdD (show 0 ≤ 2*T by positivity)
      nlinarith
    have hscale := dual_reciprocal_min_scale hM hNp hB hH he1 hT hPr hDp hNH hPD hcut
    have hQ1 := quadraticNorm_nonneg (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/p.1))
    have hQ2 := quadraticNorm_nonneg (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/p.2))
    have hboot := dual_range_bootstrap_scale hM hNp hB hx hp1r hp2r hR
      (show 0 ≤ 16*T by positivity)
      (show 0 ≤ ((N : ℝ)/H)*(Real.sqrt (M/((e : ℝ)*(2^j : ℕ)))/D) by positivity)
      hQ1 hQ2 (hnorm p.1 hp1) (hnorm p.2 hp2) hscale
    have hw : ∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ binarySquarefreeRows K j,
        ‖((Real.sqrt (M/((e : ℝ)*v))/d : ℝ) : ℂ)*g d v‖ ≤
          (Real.sqrt (M/((e : ℝ)*(2^j : ℕ)))/D)*A := by
      intro d hd v hv
      exact dual_large_weight_le (g d v) hM hep hB hA hD (Finset.mem_Ioc.mp hd).1.le
        (by exact_mod_cast (Finset.mem_filter.mp hv).2.1) (hg d hd v hv)
    apply (norm_weighted_three_le _ _ _ _ _ _ (by positivity) hw).trans
    apply (mul_le_mul_of_nonneg_left (hrow s hs) (show 0 ≤ (Real.sqrt (M/((e : ℝ)*(2^j : ℕ)))/D)*A by positivity)).trans
    have hh := mul_le_mul_of_nonneg_left hboot
      (show 0 ≤ A*C*T^2*(N : ℝ)^δ*
        (((2*D : ℕ) : ℝ)*Real.sqrt (2*(2^j : ℕ))*Real.sqrt (M/e))^σ*coefficientEnergy S a by positivity)
    convert hh using 1 <;> push_cast <;> ring
  · have hz : ∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ binarySquarefreeRows K j, g d v = 0 := by
      intro d hd v hv
      by_contra hnz
      exact hactive ⟨d,hd,v,hv,hnz⟩
    have heq : (∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ binarySquarefreeRows K j,
        ((Real.sqrt (M/((e : ℝ)*v))/d : ℝ) : ℂ)*g d v*
          (∑ l ∈ nonzeroIntegerCutoff (16*T^2), dualAggregateFourierRow W M e S a s l d v)) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      apply Finset.sum_eq_zero
      intro v hv
      rw [hz d hd v hv]
      ring
    rw [heq,norm_zero]
    positivity

end Ostmann.QuadraticSieve

end OAI
