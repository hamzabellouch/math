import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateZeroLargeLargeAmbient
import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateZeroLargeOuter

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open ComplexConjugate MeasureTheory
open scoped SchwartzMap ArithmeticFunction.Moebius

theorem dual_large_correction_ambient (W : 𝓢(ℝ,ℂ)) {ξ : ℝ}
    (hξ1 : 1<ξ) (hξ2 : ξ≤2)
    (hξ : ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (M H P η : ℝ) (Δ K N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ),
      1≤M → 0<H → 1≤P → 0<η → η≤ε/100 → 0<Δ → 0<K → 0<N →
      (N:ℝ)≤P → (K:ℝ)≤P^3 → (N:ℝ)≤2*H →
      S ⊆ oddSquarefreeUpTo N → (∀ n ∈ S,H≤(n:ℝ)) →
      ‖dualCorrelationLargeCorrection W M Δ K S a (dualWindowUpper M H (P^η))‖ ≤
        C*P^ε*(Δ:ℝ)^2*(M+Real.sqrt M*(K:ℝ)^(ξ-1/2))*coefficientEnergy S a := by
  obtain ⟨C₀,hC₀,hrows⟩ := dual_large_all_rows_ambient hξ1 hξ2 hξ ε hε
  let A : ℤ → ℝ := fun s => ‖(∫x:ℝ,dualSignedSquareWeight W s x)‖
  have hA (s : ℤ) : 0≤A s := norm_nonneg _
  have hAsum : 0≤∑ s ∈ signedSquarefreeMultipliers,A s :=
    Finset.sum_nonneg (fun s hs => hA s)
  refine ⟨2*(1+∑ s ∈ signedSquarefreeMultipliers,A s)*C₀,by positivity,?_⟩
  intro M H P η Δ K N S a hM hH hP hη hηε hΔ hK hN hNP hKP hNH hS hSH
  have hMp : 0<M := by linarith
  have hT : 1≤P^η := Real.one_le_rpow hP hη.le
  have hE := coefficientEnergy_nonneg S a
  have hSP (n : ℕ) (hn : n ∈ S) : 0<n ∧ n≤N := by
    have hh := mem_oddSquarefreeUpTo.mp (hS hn)
    exact ⟨hh.1,hh.2.1⟩
  have heach (e : ℕ) (he : e ∈ (2*Δ).divisors)
      (s : ℤ) (hs : s ∈ signedSquarefreeMultipliers) :
      ‖∑ v ∈ oddSquarefreeUpTo K,
        dualLargeDivisorRows W M N S a e s v (dualWindowUpper M H (P^η))‖ ≤
        A s*(C₀*P^ε*(M+Real.sqrt M*(K:ℝ)^(ξ-1/2))*coefficientEnergy S a) := by
    let Z : ℂ := -(1/2:ℂ)*(μ e:ℂ)*((∫x:ℝ,dualSignedSquareWeight W s x))
    let g := dualLargeCutoffWeight Z (dualWindowUpper M H (P^η) e)
    have hweight (d v : ℕ) : ‖g d v‖≤‖Z‖ := dualLargeCutoffWeight_norm _ _ _ _
    have hsupp (d v : ℕ) (hh : g d v≠0) : dualWindowLower M H (P^η) e v<(d:ℝ) := by
      exact (dualWindowLower_le_upper M H hT e v).trans_lt
        (dualLargeCutoffWeight_support _ _ _ _ hh)
    have hb := hrows M H P η ‖Z‖ K e N S a ((e:ℤ)*s) g
      hM hH hP hη hηε (norm_nonneg _) hK (Nat.pos_of_mem_divisors he) hN
      hNP hKP hNH hS hSH hweight hsupp
    simp_rw [dualLargeDivisorRows_eq_weighted]
    change ‖∑ v ∈ oddSquarefreeUpTo K, ∑ d ∈ Finset.Icc 1 (N^2),
      ((Real.sqrt (M/((e:ℝ)*v))/(d:ℝ):ℝ):ℂ)*g d v*gaussProductDivisorJacobiRow S S (sqrtCoefficients a)
        (sqrtCoefficients (fun n => conj (a n))) ((e:ℤ)*s) d (v:ℤ)‖≤_
    apply hb.trans
    have hz : ‖Z‖≤A s := dual_correction_scalar_norm e _
    calc
      _ ≤ C₀*(A s)*P^ε*(M+Real.sqrt M*(K:ℝ)^(ξ-1/2))*coefficientEnergy S a := by gcongr
      _ = _ := by ring
  rw [dualCorrelationLargeCorrection_eq_rows W M hMp Δ K N S a _ hSP]
  have hb := dual_zero_large_outer_bound hΔ
    (fun e s => ∑ v ∈ oddSquarefreeUpTo K,
      dualLargeDivisorRows W M N S a e s v (dualWindowUpper M H (P^η)))
    A hA (show 0≤C₀*P^ε*(M+Real.sqrt M*(K:ℝ)^(ξ-1/2))*coefficientEnergy S a by positivity) heach
  convert hb using 1
  ring

end Ostmann.QuadraticSieve

end

end OAI
