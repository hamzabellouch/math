import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevFlowNeighborhood

namespace OAI

/-! # Openness and continuous dependence throughout the forward lifespan -/

open Filter Topology Set

namespace DefocusingNLS

/-- Finitely many uniform local restarts propagate continuous dependence to every
nonnegative time in a maximal solution's lifespan. -/
theorem hasSobolevFlowNeighborhood_of_nonneg
    (k : ℝ) (hk : 6 < k) (m : ℕ) (f : FourierL2) (T : ℝ) (hT : 0 ≤ T)
    (hdom : T ∈ maximalSobolevInteractionDomain k hk m f) :
    HasSobolevFlowNeighborhood k hk m f T := by
  rcases hT.eq_or_lt with hT | hT
  · subst T
    exact hasSobolevFlowNeighborhood_zero k hk m f
  have hseg : Icc 0 T ⊆ maximalSobolevInteractionDomain k hk m f :=
    (isPreconnected_maximalSobolevInteractionDomain k hk m f).Icc_subset
      (zero_mem_maximalSobolevInteractionDomain k hk m f) hdom
  have hc : ContinuousOn (maximalSobolevSchrodingerFlow k hk m f) (Icc 0 T) :=
    (continuousOn_maximalSobolevSchrodingerFlow k hk m f).mono hseg
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  let R := max C 0 + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨δ, hδ, hlocalDom, hlocalCont⟩ :=
    exists_continuous_maximalSobolevSchrodingerFlow_on_ball k hk m R hR
  obtain ⟨N, hN⟩ := exists_nat_gt (T / δ)
  have hNpos : (0 : ℝ) < N := (div_pos hT hδ).trans hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  let h := T / N
  have hh : 0 < h := div_pos hT hNpos
  have hhδ : h < δ := by
    apply (div_lt_iff₀ hNpos).2
    have hmul := (div_lt_iff₀ hδ).1 hN
    simpa only [mul_comm] using hmul
  have hNh : (N : ℝ) * h = T := mul_div_cancel₀ T hNne
  have hstep : ∀ n : ℕ, n ≤ N → (n : ℝ) * h ∈ Icc 0 T := by
    intro n hn
    refine ⟨mul_nonneg (Nat.cast_nonneg n) hh.le, ?_⟩
    calc
      (n : ℝ) * h ≤ (N : ℝ) * h :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hh.le
      _ = T := hNh
  have hsteps : ∀ n : ℕ, n ≤ N → HasSobolevFlowNeighborhood k hk m f ((n : ℝ) * h) := by
    intro n
    induction n with
    | zero =>
        intro hn
        simpa only [Nat.cast_zero, zero_mul] using hasSobolevFlowNeighborhood_zero k hk m f
    | succ n ih =>
        intro hn
        have hn' : n ≤ N := (Nat.le_succ n).trans hn
        have hbound : ‖maximalSobolevSchrodingerFlow k hk m f ((n : ℝ) * h)‖ < R := by
          have hb := hC ((n : ℝ) * h) (hstep n hn')
          have hCm : C ≤ max C 0 := le_max_left C 0
          dsimp [R]
          linarith
        have hnext := HasSobolevFlowNeighborhood.advance k hk m R δ hδ hlocalDom hlocalCont
          f ((n : ℝ) * h) h (hstep n hn').1 (ih hn') hbound ⟨hh, hhδ⟩
        simpa only [Nat.cast_succ, add_mul, one_mul] using hnext
  simpa only [hNh] using hsteps N le_rfl

/-- Existence up to any prescribed forward time is an open condition on the initial datum. -/
theorem isOpen_sobolevForwardExistenceSet
    (k : ℝ) (hk : 6 < k) (m : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    IsOpen {f : FourierL2 | T ∈ maximalSobolevInteractionDomain k hk m f} := by
  apply isOpen_iff_mem_nhds.mpr
  intro f hf
  have h := hasSobolevFlowNeighborhood_of_nonneg k hk m f T hT hf
  exact (continuous_id.prodMk continuous_const).continuousAt.tendsto.eventually h.1

/-- The maximal physical flow is jointly continuous throughout its forward existence domain. -/
theorem continuousOn_maximalSobolevForwardFlow
    (k : ℝ) (hk : 6 < k) (m : ℕ) :
    ContinuousOn (fun p : FourierL2 × ℝ => maximalSobolevSchrodingerFlow k hk m p.1 p.2)
      {p | 0 ≤ p.2 ∧ p.2 ∈ maximalSobolevInteractionDomain k hk m p.1} := by
  intro p hp
  exact (hasSobolevFlowNeighborhood_of_nonneg k hk m p.1 p.2 hp.1 hp.2).2.continuousWithinAt

end DefocusingNLS

end OAI
