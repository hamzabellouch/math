import OAI.NumberTheory.Ostmann.Construction.TailSpectatorSupply
import OAI.NumberTheory.Ostmann.Construction.WholeShellRetainedLinearMass
import OAI.NumberTheory.Ostmann.Construction.PrimeFamilyEnumeration
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale

namespace OAI

/-! # The prescribed finite spectator family, after the actual allowed deletion -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.finite_tail_spectators
    (hBonami : PublishedBonamiBound) (P0 : PublishedProgressionInput)
    (H : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
    {C : ℝ} (hM : MertensEstimate C)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (k cutoff : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      ∃ p : Fin (spectatorBulkCount k L) → ℕ, Function.Injective p ∧
        ∀ i, (p i).Prime ∧ cutoff ≤ p i ∧ p i ∉ D ∧
          Real.exp (Real.exp ((4 / 10000 : ℝ) * L)) ≤ p i ∧
          (p i : ℝ) ≤ Real.exp (Real.exp ((6 / 10000 : ℝ) * L)) ∧
          (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N (p i)) ∧
          residueDensity (tailDensityMask A N (p i)) ≤ 2 / 3 ∧
          tailCharacterBias A N (p i) ≤ ε / 2 ∧
          ∀ hp : (p i).Prime,
            @MixedFourierBound (p i) ⟨hp⟩
              (@normalizedResidueTransform (p i) ⟨hp.ne_zero⟩ (tailDensityMask A N (p i))) ε := by
  classical
  have hscale := tendsto_id.const_mul_atTop (show (0 : ℝ) < 1 / 10 by norm_num)
  have hmass := hscale.eventually (whole_shell_retained_linear_mass hM 10 (by norm_num))
  have hsupply := h.tail_spectator_supply hBonami P0 H hSiegel sieve hsize hM hA hB N hN
    (4 / 10000) (6 / 10000) ε (1 / 320000) (by norm_num) (by norm_num) hε (by norm_num)
  let Ccount : ℝ := 320000 * ((k : ℝ) ^ 4 + 1)
  have hCcount : 0 < Ccount := by dsimp [Ccount]; positivity
  have hgrowth := Real.tendsto_exp_atTop.comp (Real.tendsto_exp_atTop.comp
    (tendsto_id.const_mul_atTop (show (0 : ℝ) < 4 / 10000 by norm_num)))
  filter_upwards [hmass, hsupply, hgrowth.eventually (eventually_ge_atTop (max Ccount cutoff)),
    eventually_ge_atTop (0 : ℝ)] with L hmass hsupply hlarge hL D hD
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
  have hPrange (p : ℕ) (hp : p ∈ P) : p.Prime ∧
      Real.exp (Real.exp ((4 / 10000 : ℝ) * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp ((6 / 10000 : ℝ) * L)) := by
    obtain ⟨hprime, _, hlo, hhi⟩ := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp hp).1
    refine ⟨hprime, ?_, ?_⟩
    · exact ((Real.lt_log_iff_exp_lt (by exact_mod_cast hprime.pos)).mp hlo).le
    · exact (Real.log_le_iff_le_exp (by exact_mod_cast hprime.pos)).mp hhi
  have hPband : P ⊆ closedLogLogPrimeBand (4 / 10000) (6 / 10000) L := by
    intro p hp
    obtain ⟨hpp, _, hlo, hhi⟩ := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp hp).1
    apply (mem_closedLogLogPrimeBand_iff _ _ _ _).mpr
    exact ⟨hpp, (Real.le_log_iff_exp_le (Real.log_pos (by exact_mod_cast hpp.one_lt))).mpr hlo.le,
      (Real.log_le_iff_le_exp (Real.log_pos (by exact_mod_cast hpp.one_lt))).mpr hhi⟩
  obtain ⟨Q, hQP, hmassQ, hgood⟩ := hsupply P hPband
  have hQmass : L / 320000 ≤ ∑ p ∈ Q, (p : ℝ)⁻¹ := by linarith only [hmassP, hmassQ]
  have hQmin (p : ℕ) (hp : p ∈ Q) : Ccount ≤ (p : ℝ) :=
    (le_max_left _ _).trans (hlarge.trans (hPrange p (hQP hp)).2.1)
  have hQupper : (∑ p ∈ Q, (p : ℝ)⁻¹) ≤ (Q.card : ℝ) / Ccount := by
    calc
      _ ≤ ∑ _p ∈ Q, Ccount⁻¹ := Finset.sum_le_sum (fun p hp =>
        by simpa only [one_div] using one_div_le_one_div_of_le hCcount (hQmin p hp))
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  have hQcard : spectatorBulkCount k L ≤ Q.card := by
    have hh := (le_div_iff₀ hCcount).mp (hQmass.trans hQupper)
    have he : L / 320000 * Ccount = ((k : ℝ) ^ 4 + 1) * L := by dsimp [Ccount]; ring
    rw [he] at hh
    have hm := spectatorBulkCount_upper k L hL
    have hh' : (spectatorBulkCount k L : ℝ) ≤ Q.card :=
      hm.trans (by nlinarith only [hh, hL])
    exact_mod_cast hh'
  let e : Fin (spectatorBulkCount k L) ↪ Fin Q.card :=
    ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt hQcard⟩, by
      intro i j hij
      apply Fin.ext
      exact congrArg (fun x : Fin Q.card => x.val) hij⟩
  let p := fun i => primeFamilyEnumeration Q (e i)
  refine ⟨p, (primeFamilyEnumeration_injective Q).comp e.injective, ?_⟩
  intro i
  have hpi : p i ∈ Q := primeFamilyEnumeration_mem Q (e i)
  have hpiP := hQP hpi
  obtain ⟨hpp, hlo, hhi⟩ := hPrange _ hpiP
  obtain ⟨_, hbal1, hbal2, hbias, hmix⟩ := hgood _ hpi
  have hcutoff : (cutoff : ℝ) ≤ p i :=
    (le_max_right _ _).trans (hlarge.trans hlo)
  exact ⟨hpp, by exact_mod_cast hcutoff, (Finset.mem_sdiff.mp hpiP).2,
    hlo, hhi, hbal1, hbal2, hbias, hmix⟩

end Ostmann

end OAI
