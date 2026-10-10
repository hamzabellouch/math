import OAI.NumberTheory.Ostmann.QuadraticCenter.HighWeightDecay
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityCorrelationMass

namespace OAI

/-! # Summing the high-weight bound against the actual periodic residue mass -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem eventual_high_weight_periodic_mass (C : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (N L : ℕ) (S : Finset ℕ) (u : ℝ),
      0 < L → 2 * L ^ 2 ≤ N → (2 * N : ℝ) ≤ Real.exp (C * T) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s ∈ Finset.Ioc N (2 * N)) →
      (∀ s ∈ S, L.Coprime s) → 2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      (∀ s ∈ S, Real.exp (T ^ (9999999 / 10000000 : ℝ) / 200) < u ^ s.primeFactors.card) →
      ∀ [NeZero L] (F : ZMod L → ℂ), (∑ x : ZMod L, ‖F x‖) ≤ L →
        (∑ s ∈ S, u ^ s.primeFactors.card * ‖F (s : ZMod L)‖) ≤
          N * Real.exp (-10 * T ^ (9999999 / 10000000 : ℝ)) := by
  classical
  filter_upwards [eventual_high_weight_residue_mass C] with T hT N L S u hL hsize hcut
    hS hrange hcop hu huU hhigh inst F hF
  have hmaps (s : ℕ) (_hs : s ∈ S) : (s : ZMod L) ∈ (Finset.univ : Finset (ZMod L)) :=
    Finset.mem_univ _
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  let E := Real.exp (-10 * T ^ (9999999 / 10000000 : ℝ))
  calc
    _ = ∑ x : ZMod L, (∑ s ∈ S.filter (fun s : ℕ => (s : ZMod L) = x), u ^ s.primeFactors.card) * ‖F x‖ := by
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      rw [(Finset.mem_filter.mp hs).2]
    _ ≤ ∑ x : ZMod L, (((N : ℝ) / L) * E) * ‖F x‖ := by
      apply Finset.sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply hT N L x.val (S.filter (fun s => (s : ZMod L) = x)) u hL hsize hcut
      · intro s hs; exact hS s (Finset.mem_filter.mp hs).1
      · intro s hs; exact hrange s (Finset.mem_filter.mp hs).1
      · intro s hs
        apply (ZMod.natCast_eq_natCast_iff s x.val L).mp
        exact (Finset.mem_filter.mp hs).2.trans (ZMod.natCast_zmod_val x).symm
      · intro s hs; exact hcop s (Finset.mem_filter.mp hs).1
      · exact hu
      · exact huU
      · intro s hs; exact hhigh s (Finset.mem_filter.mp hs).1
    _ = (((N : ℝ) / L) * E) * ∑ x : ZMod L, ‖F x‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ (((N : ℝ) / L) * E) * L := mul_le_mul_of_nonneg_left hF (by positivity)
    _ = (N : ℝ) * E := by field_simp

end Ostmann

end OAI
