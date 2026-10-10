import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothingDescentBudget
import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothingDescentFinite

namespace OAI

namespace Ostmann.QuadraticSieve

theorem SmoothingStepBound.optimized_smoothing {ξ : ℝ} (hstep : SmoothingStepBound ξ)
    (ε : ℝ) (hε : 0<ε) :
    ∃ η : ℝ, 0<η ∧ η≤ε/100 ∧ ∃ C : ℝ, 0<C ∧ ∀ (M K N : ℕ),
      0<M → 0<K → 0<N → N≤M → K≤M →
      (2*(N:ℝ)^2/M)*((M:ℝ)*N)^η≤(K:ℝ) →
      Real.sqrt ((M:ℝ)/(K:ℝ))*N≤M →
      smoothingNorm M K (oddSquarefreeUpTo N)≤
        C*((M:ℝ)*N)^(ε/2)*((M:ℝ)+Real.sqrt (M:ℝ)*(K:ℝ)^(ξ-1/2)) := by
  obtain ⟨R,hR,hscale⟩ := exists_smoothing_descent_scale (ε/8) (by positivity)
  let δ : ℝ := ε/(8*((R:ℝ)+1))
  let η : ℝ := δ/100
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hη : 0<η := by dsimp [η]; positivity
  have hδle : δ≤ε/8 := by
    dsimp only [δ]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<8*((R:ℝ)+1))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) R]
  have hηle : η≤ε/100 := by dsimp only [η]; linarith
  have hδR : δ*(R:ℝ)≤ε/8 := by
    dsimp only [δ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<8*((R:ℝ)+1))).mpr
    nlinarith
  obtain ⟨C,hC,hbound⟩ := hstep.finite_descent hδ hη (show η≤δ/100 from le_rfl)
  refine ⟨η,hη,hηle,32*C^R*(3+(R:ℝ)),by positivity,?_⟩
  intro M K N hM hK hN hNM hKM hcut hsqrt
  let D := smoothingDescentScale N R
  obtain ⟨hD,hsize,hD5⟩ := hscale N hN
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hP1 : (1:ℝ)≤(M:ℝ)*N := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hM) (by exact_mod_cast hN)
  have hNP : (N:ℝ)≤(M:ℝ)*N := le_mul_of_one_le_left (Nat.cast_nonneg N) (by exact_mod_cast hM)
  have hD5' : (D:ℝ)^5≤32*((M:ℝ)*N)^(ε/8) := hD5.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg N) hNP (by positivity)) (by norm_num))
  have hd := hbound M K N D R hM hK hN hD hNM hKM hcut hsqrt hsize
  have hs := smoothing_descent_scalar_budget (ξ := ξ) R hMr (Nat.cast_nonneg K) hP1
    (by exact_mod_cast hD) (by linarith : 0≤C) hD5' hδR
  apply hd.trans (hs.trans ?_)
  gcongr
  linarith

end Ostmann.QuadraticSieve

end OAI
