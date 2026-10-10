import OAI.NumberTheory.Ostmann.QuadraticSieveDescentScales
import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothingColumnDyadicBasic
import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothingStepDefinition

namespace OAI

namespace Ostmann.QuadraticSieve

lemma smoothingNorm_prefix_trivial (M K n : ℕ) :
    smoothingNorm M K (oddSquarefreeUpTo n)≤3*(M:ℝ)*n := by
  have hcard : (oddSquarefreeUpTo n).card≤n := by
    calc
      _ ≤ (Finset.Icc 1 n).card := Finset.card_filter_le _ _
      _ = n := by simp
  exact (smoothingNorm_le_trivial M K _).trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by positivity))

theorem SmoothingStepBound.finite_descent {ξ : ℝ} (hstep : SmoothingStepBound ξ)
    {δ η : ℝ} (hδ : 0<δ) (hη : 0<η) (hηδ : η≤δ/100) :
    ∃ C : ℝ, 1≤C ∧ ∀ (M K N D R : ℕ),
      0<M → 0<K → 0<N → 1≤D → N≤M → K≤M →
      (2*(N:ℝ)^2/M)*((M:ℝ)*N)^η≤(K:ℝ) →
      Real.sqrt ((M:ℝ)/(K:ℝ))*N≤M → (N:ℝ)≤(D:ℝ)^R →
      smoothingNorm M K (oddSquarefreeUpTo N)≤
        (C*((M:ℝ)*N)^δ)^R*
          (3*(M:ℝ)*D+(R:ℝ)*(D:ℝ)^5*((M:ℝ)+Real.sqrt (M:ℝ)*(K:ℝ)^(ξ-1/2))) := by
  obtain ⟨C₀,hC₀,hbound⟩ := hstep δ hδ η hη hηδ
  refine ⟨C₀+1,by linarith,?_⟩
  intro M K N D R hM hK hN hD hNM hKM hcut hsqrt hsize
  have hP1 : (1:ℝ)≤(M:ℝ)*N := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hM) (by exact_mod_cast hN)
  have hpow : 1≤((M:ℝ)*N)^δ := Real.one_le_rpow hP1 hδ.le
  have hH : 1≤(C₀+1)*((M:ℝ)*N)^δ := by nlinarith
  have hDr : (1:ℝ)≤D := by exact_mod_cast hD
  have he := finite_recursion_descent_at
    (fun n => smoothingNorm M K (oddSquarefreeUpTo n)) N R hDr hH
    (show 0≤(D:ℝ)^5*((M:ℝ)+Real.sqrt (M:ℝ)*(K:ℝ)^(ξ-1/2)) by positivity)
    (show 0≤3*(M:ℝ)*D by positivity) hsize
    (fun n hn hsmall => (smoothingNorm_prefix_trivial M K n).trans
      (mul_le_mul_of_nonneg_left hsmall (by positivity))) ?_
  · convert he using 1; ring
  · intro n hn hbig
    have hn0 : 0<n := by
      have hn1 : (1:ℝ)<n := hDr.trans_lt hbig
      exact_mod_cast (show (0:ℝ)<n by linarith)
    refine ⟨n/D,(Nat.div_le_self n D).trans hn,Nat.cast_div_le,?_⟩
    have hh := hbound M K N D n hM hK hN (by omega) hn0 hn hNM hKM hcut hsqrt
    apply hh.trans
    have hz := smoothingNorm_nonneg M K (oddSquarefreeUpTo (n/D))
    gcongr
    linarith

end Ostmann.QuadraticSieve

end OAI
