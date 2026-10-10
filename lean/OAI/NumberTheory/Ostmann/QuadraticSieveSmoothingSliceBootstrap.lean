import OAI.NumberTheory.Ostmann.QuadraticSieveCorrelationBootstrap
import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothingRecursionSupport

namespace OAI

namespace Ostmann.QuadraticSieve

theorem smoothing_small_gcd_binary_slice_bound {ξ : ℝ}
    (hξ1 : 1 < ξ) (hξ2 : ξ ≤ 2)
    (hξ : ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) (hηε : η ≤ ε/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M K N₀ D n j d : ℕ) (a : ℕ → ℂ),
      0 < M → 0 < K → 0 < N₀ → 0 < D → 0 < n → 0 < d →
      n ≤ N₀ → N₀ ≤ M → K ≤ M →
      2*(N₀ : ℝ)^2/(M : ℝ)*((M : ℝ)*N₀)^η ≤ K →
      Real.sqrt ((M : ℝ)/K)*N₀ ≤ M →
      D^2 < 2^j → (binarySquarefreeRows n j).Nonempty → d ≤ D →
      ‖weightedGcdCorrelation (smoothingRows M K) (binarySquarefreeRows n j) (smoothingWeight M) a d‖ ≤
        C*((M : ℝ)*N₀)^ε*(d : ℝ)^4*
          ((M : ℝ)+Real.sqrt M*(K : ℝ)^(ξ-1/2))*coefficientEnergy (binarySquarefreeRows n j) a := by
  obtain ⟨C,hC,hbound⟩ := correlation_difference_bootstrap sieveWeight sieveWeight_compact
    sieveWeight_support_pos hξ1 hξ2 hξ ε η hε hη hηε
  refine ⟨C,hC,?_⟩
  intro M K N₀ D n j d a hM hK hN₀ hD hn hd hnN hNM hKM hcut hsqrt hlarge hne hdD
  let S := binarySquarefreeRows n j
  have hS : S ⊆ oddSquarefreeUpTo n := Finset.filter_subset _ _
  have hSsf : ∀ m ∈ S, Odd m ∧ Squarefree m := fun m hm =>
    (mem_oddSquarefreeUpTo.mp (hS hm)).2.2
  have hE := coefficientEnergy_nonneg S a
  by_cases hodd : Odd d
  · let Nq := binaryColumnEndpoint n j/d
    let H : ℝ := ((2^j : ℕ) : ℝ)/d
    let P : ℝ := (M : ℝ)*N₀
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hN1 : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd
    have hMP : (M : ℝ) ≤ P := by dsimp [P]; nlinarith
    have hP1 : 1 ≤ P := hM1.trans hMP
    have hHp : 0 < H := by dsimp [H]; positivity
    obtain ⟨hqpos,hdq,hqn,hqH,hqsub,hqdata⟩ := binary_column_quotient_data hD hlarge hne hd hdD
    have hqN : Nq ≤ N₀ := hqn.trans hnN
    have hqM : (Nq : ℝ) ≤ M := by exact_mod_cast hqN.trans hNM
    have hqHr : (Nq : ℝ) ≤ 2*H := by simpa only [H,mul_div_assoc] using hqH
    have hqsub' : quotientSupport S d ⊆ oddSquarefreeUpTo Nq := hqsub
    have hdP : (d : ℝ) ≤ P := by
      exact (by exact_mod_cast hdq.trans (hqN.trans hNM) : (d : ℝ) ≤ M).trans hMP
    have hKp : (K : ℝ) ≤ P := (by exact_mod_cast hKM : (K : ℝ) ≤ M).trans hMP
    have hP3 : P ≤ P^3 := by
      have hh : 0 ≤ (P-1)*(P^2+P) := mul_nonneg (by linarith) (by positivity)
      nlinarith
    have hKP : (K : ℝ) ≤ P^3 := hKp.trans hP3
    have hdqN : d*Nq ≤ N₀ := by
      have hh : d*Nq ≤ binaryColumnEndpoint n j := by
        simpa only [Nq,Nat.mul_comm] using Nat.div_mul_le_self (binaryColumnEndpoint n j) d
      exact hh.trans ((Nat.min_le_left _ _).trans hnN)
    have hcore : ((2*d : ℕ) : ℝ)*(Nq : ℝ)^2 ≤ 2*(N₀ : ℝ)^2 := by
      have hp := mul_le_mul
        (by exact_mod_cast hdqN : (d : ℝ)*Nq ≤ N₀)
        (by exact_mod_cast hqN : (Nq : ℝ) ≤ N₀)
        (Nat.cast_nonneg Nq) (Nat.cast_nonneg N₀)
      push_cast
      nlinarith
    have hlocalcut : ((2*d : ℕ) : ℝ)*(Nq : ℝ)^2/(M : ℝ)*P^η ≤ K := by
      exact (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcore hMr.le)
        (Real.rpow_nonneg (by positivity) η)).trans hcut
    have hlocalsqrt : Real.sqrt ((M : ℝ)/K)*Nq ≤ M :=
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hqN : (Nq : ℝ) ≤ N₀)
        (Real.sqrt_nonneg _)).trans hsqrt
    have hqcop : ∀ m ∈ quotientSupport S d, Nat.Coprime m d := fun m hm => (hqdata m hm).1
    have hq1 : ∀ m ∈ quotientSupport S d, 1 < m := fun m hm => (hqdata m hm).2.1
    have hqdyadic : ∀ m ∈ quotientSupport S d, H ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2*H := by
      intro m hm
      have hh := hqdata m hm
      exact ⟨hh.2.2.1.le,by simpa only [H,mul_div_assoc] using hh.2.2.2⟩
    have hh := hbound (M : ℝ) P H K d Nq (quotientSupport S d) (fun m => a (d*m))
      hM1 hMP hP1 hHp hK hd hqpos hKP hdP hqM hqHr hodd hdq hqsub' hqcop hq1 hqdyadic hlocalcut hlocalsqrt
    rw [smoothing_gcdCorrelation_eq_of_oddSquarefree hM hd K S a hS]
    apply hh.trans
    exact mul_le_mul_of_nonneg_left (coefficientEnergy_quotientSupport_le S a d) (by positivity)
  · rw [weightedGcdCorrelation_zero_of_bad_factor (smoothingRows M K) (smoothingWeight M) a hd hSsf
      (fun hh => hodd hh.1),norm_zero]
    positivity

end Ostmann.QuadraticSieve

end OAI
