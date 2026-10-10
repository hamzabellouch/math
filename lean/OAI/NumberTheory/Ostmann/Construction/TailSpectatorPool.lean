import OAI.NumberTheory.Ostmann.Construction.TailSpectatorSupply
import OAI.NumberTheory.Ostmann.Construction.WholeShellRetainedLinearMass

namespace OAI

/-! # A harmonic spectator pool for the original initial prior -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.tail_spectator_pool
    (hBonami : PublishedBonamiBound) (P0 : PublishedProgressionInput)
    (H : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
    {C : ℝ} (hM : MertensEstimate C)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (cutoff : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      ∃ Q : Finset ℕ,
        Q ⊆ primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
          (Real.exp ((6 / 10000 : ℝ) * L)) \ D ∧
        L / 320000 ≤ ∑ p ∈ Q, (p : ℝ)⁻¹ ∧
        ∀ p ∈ Q, cutoff ≤ p ∧ 3 ≤ p ∧
          (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
          residueDensity (tailDensityMask A N p) ≤ 2 / 3 ∧
          tailCharacterBias A N p ≤ ε / 2 ∧
          ∀ hp : p.Prime, @MixedFourierBound p ⟨hp⟩
            (@normalizedResidueTransform p ⟨hp.ne_zero⟩ (tailDensityMask A N p)) ε := by
  have hscale := tendsto_id.const_mul_atTop (show (0 : ℝ) < 1 / 10 by norm_num)
  have hmass := hscale.eventually (whole_shell_retained_linear_mass hM 10 (by norm_num))
  have hsupply := h.tail_spectator_supply hBonami P0 H hSiegel sieve hsize hM hA hB N hN
    (4 / 10000) (6 / 10000) ε (1 / 320000) (by norm_num) (by norm_num) hε (by norm_num)
  have hgrowth := Real.tendsto_exp_atTop.comp (Real.tendsto_exp_atTop.comp
    (tendsto_id.const_mul_atTop (show (0 : ℝ) < 4 / 10000 by norm_num)))
  filter_upwards [hmass, hsupply, hgrowth.eventually (eventually_ge_atTop (cutoff : ℝ))]
    with L hmass hsupply hlarge D hD
  simp only [id_eq, Function.comp_apply] at hmass hlarge
  let S := primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
    (Real.exp ((6 / 10000 : ℝ) * L))
  let P := S \ D
  have hmassP : L / 160000 ≤ ∑ p ∈ P, (p : ℝ)⁻¹ := by
    have hh := hmass D (by convert hD using 1; congr 1; ring)
    rw [show (1 / 10 : ℝ) * L / 16000 = L / 160000 by ring,
      show (4 / 1000 : ℝ) * ((1 / 10) * L) = (4 / 10000) * L by ring,
      show (6 / 1000 : ℝ) * ((1 / 10) * L) = (6 / 10000) * L by ring] at hh
    exact hh
  have hPband : P ⊆ closedLogLogPrimeBand (4 / 10000) (6 / 10000) L := by
    intro p hp
    obtain ⟨hpp, _, hlo, hhi⟩ := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp hp).1
    apply (mem_closedLogLogPrimeBand_iff _ _ _ _).mpr
    exact ⟨hpp, (Real.le_log_iff_exp_le (Real.log_pos (by exact_mod_cast hpp.one_lt))).mpr hlo.le,
      (Real.log_le_iff_le_exp (Real.log_pos (by exact_mod_cast hpp.one_lt))).mpr hhi⟩
  obtain ⟨Q, hQP, hmassQ, hgood⟩ := hsupply P hPband
  refine ⟨Q, hQP, by linarith only [hmassP, hmassQ], ?_⟩
  intro p hp
  obtain ⟨hpp, _, hlo, _⟩ := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp (hQP hp)).1
  have hcutoff : (cutoff : ℝ) ≤ p := hlarge.trans
    ((Real.lt_log_iff_exp_lt (by exact_mod_cast hpp.pos)).mp hlo).le
  exact ⟨by exact_mod_cast hcutoff, hgood p hp⟩

end Ostmann

end OAI
