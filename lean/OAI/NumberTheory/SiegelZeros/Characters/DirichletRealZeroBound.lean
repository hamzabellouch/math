import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.EntireFunctions.RealZeroUniformMasterBound

namespace OAI

namespace SiegelZeros

section
namespace WeightedTorusJets

open Filter Topology

theorem dirichlet_real_zero_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
        (∀ a : ZMod q, (χ a).im = 0) → ∀ β : ℝ,
          (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
            c ≤ (1 - β) * Real.log (q : ℝ) := by
  by_contra hnot
  obtain ⟨q, hq, χ, β, hadm, hqtop, hgap⟩ := exists_contrary_sequence hnot
  obtain ⟨C, _hC, hsource⟩ := source_real_zero_uniform_master_bound
  obtain ⟨H, hH, γ, hγ, hno⟩ := exists_fixed_parameters_not_eventually_uniform_bound C
  obtain ⟨CH, hCH⟩ := hsource H hH
  have hqreal : Tendsto (fun n => (q n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hqtop
  apply hno (fun n => (q n : ℝ)) (fun n => (1 - β n) * Real.log (q n : ℝ)) CH hqreal hgap
  have hNtop : Tendsto (fun n => ⌈(q n : ℝ) ^ γ⌉₊) atTop atTop :=
    (tendsto_natCeil_rpow_atTop hγ).comp hqreal
  filter_upwards [hNtop.eventually_ge_atTop H, hNtop.eventually_ge_atTop 18818,
    hqtop.eventually_ne_atTop 8] with n hnH hnN hn8
  let := hq n
  exact hCH (q n) (hadm n).1 hn8 (χ n) (hadm n).2.2.2.1
    (hadm n).2.1 (hadm n).2.2.1 (β n) (hadm n).2.2.2.2.1
    (hadm n).2.2.2.2.2.1 (hadm n).2.2.2.2.2.2
    ⌈(q n : ℝ) ^ γ⌉₊ hnH hnN

end WeightedTorusJets

end

end SiegelZeros

end OAI
