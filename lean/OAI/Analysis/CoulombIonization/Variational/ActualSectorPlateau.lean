import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.ActualPricedParticleBound

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Filter
open scoped Topology

namespace CoulombAtom
attribute [local irreducible] fermionGraph fermionGraphValue graphFormVector
  formEnergy energy

lemma quantum_strict_binding_particle_bound {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (hstep : energy Z (N+1) < energy Z N) : (N:ℝ) ≤ 2*Z := by
  have hl : 0 < energy Z N-energy Z (N+1) := sub_pos.mpr hstep
  apply quantum_positive_price_binding_bound hZ hl
  linarith

lemma quantum_energy_step_at_coarse_fence (Z n : ℕ) (hn : 2*Z+1 ≤ n) :
    energy Z (n+1) = energy Z n := by
  apply le_antisymm (quantum_energy_antitone (Nat.cast_nonneg Z) (Nat.le_succ n))
  apply le_of_not_gt
  intro hs
  have hb := quantum_strict_binding_particle_bound (Nat.cast_nonneg Z) hs
  have hc : (2:ℝ)*Z+1 ≤ n := by exact_mod_cast hn
  linarith only [hb,hc]

theorem quantum_energy_plateau (Z n : ℕ) (hn : 2*Z+1 ≤ n) :
    energy Z n = energy Z (2*Z+1) := by
  have h (k : ℕ) : energy Z (2*Z+1+k) = energy Z (2*Z+1) := by
    induction k with
    | zero => simp only [Nat.add_zero]
    | succ k hk =>
      rw [show 2*Z+1+(k+1)=(2*Z+1+k)+1 by omega,
        quantum_energy_step_at_coarse_fence Z _ (by omega),hk]
  simpa only [Nat.add_sub_of_le hn] using h (n-(2*Z+1))

lemma quantum_energy_coarse_fence_minimum (Z n : ℕ) :
    energy Z (2*Z+1) ≤ energy Z n := by
  by_cases hn : n ≤ 2*Z+1
  · exact quantum_energy_antitone (Nat.cast_nonneg Z) hn
  · exact (quantum_energy_plateau Z n (by omega)).symm.le

theorem quantum_unpriced_infimum_finite (Z : ℕ) :
    sInf (Set.range (energy (Z:ℝ))) = energy Z (2*Z+1) := by
  have hb : BddBelow (Set.range (energy (Z:ℝ))) := by
    refine ⟨energy Z (2*Z+1),?_⟩
    rintro x ⟨n,rfl⟩
    exact quantum_energy_coarse_fence_minimum Z n
  apply le_antisymm
  · exact csInf_le hb ⟨2*Z+1,rfl⟩
  · apply le_csInf (s := Set.range (energy (Z:ℝ))) ⟨_,2*Z+1,rfl⟩
    rintro x ⟨n,rfl⟩
    exact quantum_energy_coarse_fence_minimum Z n

theorem actual_priced_particle_bound_three (Z : ℕ) (hZ : 1 ≤ Z)
    {lam : ℝ} (hlam : 0 < lam) {N : ℕ}
    (hN : PriceMinimizes (energy Z) lam N) : N ≤ 3*Z := by
  have h := actual_priced_particle_bound (Nat.cast_nonneg Z) hlam hN
  have hz : (1:ℝ) ≤ Z := by exact_mod_cast hZ
  have hh : (N:ℝ) ≤ 3*Z := by linarith only [h,hz]
  exact_mod_cast hh

end CoulombAtom

end

end OAI
