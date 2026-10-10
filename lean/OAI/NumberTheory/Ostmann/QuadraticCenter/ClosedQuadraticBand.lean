import OAI.NumberTheory.Ostmann.QuadraticCenter.MaximalQuadraticBias
import OAI.NumberTheory.Ostmann.Construction.PositiveFourierCutoff

namespace OAI

/-! # The closed prime band used in the manuscript's quadratic proposition -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

noncomputable def closedLogPrimeBand (T : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊Real.exp (2 * T)⌋₊).filter (fun p => T ≤ Real.log (p : ℝ))

noncomputable def closedQuadraticBandMass (A : Set ℕ) (N : ℕ) (T : ℝ) : ℝ :=
  ∑ p ∈ closedLogPrimeBand T, (Real.log (p : ℝ) / p) * maximalQuadraticBias (tailSupport A N p) p

theorem mem_closedLogPrimeBand_iff (T : ℝ) (p : ℕ) :
    p ∈ closedLogPrimeBand T ↔ p.Prime ∧ T ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 2 * T := by
  simp only [closedLogPrimeBand, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hp, hprime⟩, hlo⟩
    refine ⟨hprime, hlo, (Real.log_le_iff_le_exp (by exact_mod_cast hprime.pos)).mpr ?_⟩
    exact (by exact_mod_cast hp : (p : ℝ) ≤ ⌊Real.exp (2 * T)⌋₊).trans (Nat.floor_le (Real.exp_nonneg _))
  · rintro ⟨hprime, hlo, hhi⟩
    exact ⟨⟨Nat.le_floor ((Real.log_le_iff_le_exp (by exact_mod_cast hprime.pos)).mp hhi), hprime⟩, hlo⟩

theorem logPrimeBand_subset_closed (T : ℝ) : logPrimeBand T ⊆ closedLogPrimeBand T := by
  intro p hp
  have hh := logPrimeBand_mem hp
  exact (mem_closedLogPrimeBand_iff T p).mpr ⟨hh.1, hh.2.1.le, hh.2.2⟩

private theorem deleted_log_eq (T : ℝ) {p : ℕ}
    (hp : p ∈ closedLogPrimeBand T \ logPrimeBand T) : Real.log (p : ℝ) = T := by
  obtain ⟨hclosed, hnot⟩ := Finset.mem_sdiff.mp hp
  have hc := (mem_closedLogPrimeBand_iff T p).mp hclosed
  have hup : p ∈ Nat.primesLE ⌊Real.exp (2 * T)⌋₊ := (Finset.mem_filter.mp hclosed).1
  have hlo : p ∈ Nat.primesLE ⌊Real.exp T⌋₊ := by
    by_contra hn
    exact hnot (Finset.mem_sdiff.mpr ⟨hup, hn⟩)
  have hple : (p : ℝ) ≤ Real.exp T :=
    (by exact_mod_cast Nat.le_of_mem_primesLE hlo : (p : ℝ) ≤ ⌊Real.exp T⌋₊).trans (Nat.floor_le (Real.exp_nonneg _))
  exact le_antisymm ((Real.log_le_iff_le_exp (by exact_mod_cast hc.1.pos)).mpr hple) hc.2.1

theorem closedQuadraticBandMass_le (A : Set ℕ) (N : ℕ) (T : ℝ) :
    closedQuadraticBandMass A N T ≤ quadraticBandMass A N T + 1 := by
  let E := closedLogPrimeBand T \ logPrimeBand T
  have hcard : E.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    have hpprime := ((mem_closedLogPrimeBand_iff T p).mp (Finset.mem_sdiff.mp hp).1).1
    have hqprime := ((mem_closedLogPrimeBand_iff T q).mp (Finset.mem_sdiff.mp hq).1).1
    have he := congrArg Real.exp ((deleted_log_eq T hp).trans (deleted_log_eq T hq).symm)
    rw [Real.exp_log (by exact_mod_cast hpprime.pos), Real.exp_log (by exact_mod_cast hqprime.pos)] at he
    exact_mod_cast he
  have hsum : (∑ p ∈ E, (Real.log (p : ℝ) / p) * maximalQuadraticBias (tailSupport A N p) p) ≤ 1 := by
    calc
      _ ≤ ∑ _p ∈ E, (1 : ℝ) := Finset.sum_le_sum (fun p hp => by
        have hprime := ((mem_closedLogPrimeBand_iff T p).mp (Finset.mem_sdiff.mp hp).1).1
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
        have hweight : 0 ≤ Real.log (p : ℝ) / p :=
          div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) hp0.le
        have hweightU : Real.log (p : ℝ) / p ≤ 1 :=
          (div_le_one hp0).mpr (Real.log_le_self hp0.le)
        exact (mul_le_mul_of_nonneg_left (maximalQuadraticBias_le_one _ _) hweight).trans
          (by simpa using hweightU))
      _ = (E.card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast hcard
  have he := Finset.sum_sdiff (f := fun (p : ℕ) => (Real.log (p : ℝ) / p) * maximalQuadraticBias (tailSupport A N p) p)
    (logPrimeBand_subset_closed T)
  change _ + quadraticBandMass A N T = closedQuadraticBandMass A N T at he
  linarith

theorem closedQuadraticBandMass_nonneg (A : Set ℕ) (N : ℕ) (T : ℝ) :
    0 ≤ closedQuadraticBandMass A N T := by
  apply Finset.sum_nonneg
  intro p hp
  have hprime := ((mem_closedLogPrimeBand_iff T p).mp hp).1
  exact mul_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) (Nat.cast_nonneg _))
    (maximalQuadraticBias_nonneg _ _)

theorem closedQuadraticBandMass_isLittleO_of_halfopen (A : Set ℕ) (N : ℕ)
    (h : (fun T => quadraticBandMass A N T) =o[atTop] (fun T : ℝ => T)) :
    (fun T => closedQuadraticBandMass A N T) =o[atTop] (fun T : ℝ => T) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  filter_upwards [h.bound (show 0 < c / 2 by positivity), eventually_ge_atTop (2 / c)] with T hh hT
  have hTpos : 0 ≤ T := (by positivity : (0 : ℝ) ≤ 2 / c).trans hT
  have hone : 1 ≤ c / 2 * T := by have := (div_le_iff₀ hc).mp hT; nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (closedQuadraticBandMass_nonneg A N T), Real.norm_eq_abs, abs_of_nonneg hTpos]
  rw [Real.norm_eq_abs, abs_of_nonneg (quadraticBandMass_nonneg A N T), Real.norm_eq_abs, abs_of_nonneg hTpos] at hh
  linarith [closedQuadraticBandMass_le A N T]

/-- Proposition 3.1 with its exact closed prime band, conditionally only on the
recorded published inputs. The positive Fourier cutoff is constructed. -/
theorem EventuallyPrimeSumset.quadratic_smallness
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (hBonami : PublishedBonamiBound) (P₀ : PublishedProgressionInput)
    (H : PublishedRealZeroInput P₀) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
    (C₀ : ℝ) (hM : MertensEstimate C₀) :
    ∃ N, (∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p)) ∧
      (fun T => closedQuadraticBandMass A N T) =o[atTop] (fun T : ℝ => T) := by
  obtain ⟨N, hN⟩ := h.disjoint_tail_residues
  obtain ⟨c, ψ, hc, hreal, hψ0, hψ1, hsupp⟩ := exists_positive_fourier_cutoff
  refine ⟨N, hN, closedQuadraticBandMass_isLittleO_of_halfopen A N ?_⟩
  exact quadraticBandMass_isLittleO hBonami P₀ H hSiegel sieve hsize hA hB h N hN C₀ hM
    c 3 hc le_rfl ψ hreal hψ0 hψ1 hsupp

end Ostmann

end OAI
