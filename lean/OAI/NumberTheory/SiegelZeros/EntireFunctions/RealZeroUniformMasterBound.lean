import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Characters.CharacterGlobalGreedyDeterminantMasterBounds
import OAI.NumberTheory.SiegelZeros.Selection.GlobalWeightSortedJetEquiv
import OAI.NumberTheory.SiegelZeros.Structure.NotEventuallyMaster
import OAI.NumberTheory.SiegelZeros.Structure.QuadraticEigencharacter

namespace OAI

namespace SiegelZeros

section
namespace WeightedTorusJets

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

end WeightedTorusJets

end

section
namespace WeightedTorusJets

open scoped BigOperators NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

theorem source_real_zero_uniform_master_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 86713344 ≤ H → ∃ CH : ℝ,
      ∀ (q : ℕ) [NeZero q], 3 ≤ q → q ≠ 8 →
      ∀ χ : DirichletCharacter ℂ q,
        (∀ x : ZMod q, (χ x).im = 0) → χ.IsPrimitive → χ ≠ 1 →
      ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      ∀ N : ℕ, H ≤ N → 18818 ≤ N →
      let U : ℝ := (N : ℝ) ^ (4 / 3 : ℝ)
      let D : ℝ := (H : ℝ) ^ (2 / 3 : ℝ) / (4 * 97 ^ 2)
      1 ≤ 13 / 16 + (C + 13 / 24) * (Real.log (q : ℝ) / Real.log U) +
        C * ((1 - β) * Real.log (q : ℝ)) * (Real.log U / Real.log (q : ℝ)) +
        (CH + 13 / 12 * Real.log 8) / Real.log U +
        C / (D * Real.log U) + 3 / (2 * D * U) := by
  classical
  obtain ⟨C, hC, _hC4, CH, hsource⟩ :=
    source_character_global_greedy_determinant_master_bounds
  refine ⟨C, hC, ?_⟩
  intro H hH
  have hHnat : 0 < H := by omega
  obtain ⟨e, he⟩ := exists_global_weight_sorted_jet_equiv H hHnat
  refine ⟨CH H, ?_⟩
  intro q _ hq hq8 χ hreal hprim hne
  have hfield := characterField_ne_sourceSqrtTwoField_of_ne_eight q χ hprim
    (real_character_isQuadratic χ hreal) hne hq8
  obtain ⟨d, a, b, _hd, _hdsize, _hddiv, _hdns, _ha, _hb, _hfield, _hdisc,
    _hfund, _hformula, v, _hv, _hint, _hdegree, σ, τ, _hσa, _hσb, _hτa, _hτb,
    _hcard, _hall, _hcomm, hdata⟩ := hsource q χ hreal hprim hne hfield
  intro β hβ0 hβ1 hzero N hHN hN U D
  let n : Fin (N ^ 4) ≃ (Fin 4 → Fin N) :=
    (Fintype.equivFinOfCardEq (by simp : Fintype.card (Fin 4 → Fin N) = N ^ 4)).symm
  obtain ⟨g, α, _hg, _hα, hrange, _hmono, _hweight, _hstable,
    Δ, _hΔ, _hΔne, harch, _hdiv, _hraw, hfinite, hlarge⟩ := hdata N H hHnat hHN n e he
  obtain ⟨hpivot₁, hpivot₂, _hSpos, _hmaster⟩ := hlarge hN
  have hS₁eq := sum_embedding_eq_sum_finset_of_range α _ hrange (fun a => (a 0 : ℝ))
  have hS₂eq := sum_embedding_eq_sum_finset_of_range α _ hrange
    (fun a => ((a 1 : ℝ) + a 2))
  rw [← hS₁eq] at hpivot₁
  rw [← hS₂eq] at hpivot₂
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hHnat.trans_le hHN
  have hM : 0 < (N : ℝ) ^ 4 := pow_pos hNpos _
  have hUone : 1 < U := Real.one_lt_rpow
    (by exact_mod_cast (show 1 < N by omega)) (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  have hS₁ : D * (N : ℝ) ^ 4 * U ≤ ∑ i, (α i 0 : ℝ) := by
    convert hpivot₁ using 1
    dsimp [D, U]
    ring
  have hratio : (∑ i, ((α i 1 : ℝ) + α i 2)) / (∑ i, (α i 0 : ℝ)) ≤ 1 / 12 :=
    pivot_ratio_le_one_twelfth (H := (H : ℝ)) (M := (N : ℝ) ^ 4) (U := U)
      (by exact_mod_cast hH) hM (zero_lt_one.trans hUone)
      (by simpa only [U] using hpivot₁)
      (by simpa only [U, neg_div] using hpivot₂)
  have hlower := hfinite β hβ0 hβ1 hzero U (zero_lt_one.trans hUone).le
  have hlogM : Real.log ((N : ℝ) ^ 4) = 3 * Real.log U :=
    log_degree_four_eq_three_log_scale hNpos
  have hlogN : Real.log (N : ℝ) = 3 / 4 * Real.log U :=
    log_eq_three_quarters_log_scale hNpos
  apply FinalComparison.uniform_master_bound hM hUone
    (Real.log_pos (by exact_mod_cast (show 1 < q by omega))) hD hC.le hS₁ hratio hlogM
    ?_ hlower
  simpa only [hlogN] using harch

end WeightedTorusJets

end

end SiegelZeros

end OAI
