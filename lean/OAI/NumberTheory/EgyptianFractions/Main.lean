import OAI.NumberTheory.EgyptianFractions.Defs
import OAI.NumberTheory.EgyptianFractions.DenominatorBound
import OAI.NumberTheory.EgyptianFractions.FiniteBox
import OAI.NumberTheory.EgyptianFractions.MissingSemantics
import OAI.NumberTheory.EgyptianFractions.LengthBasic
import OAI.NumberTheory.EgyptianFractions.EgyptianExistence
import OAI.NumberTheory.EgyptianFractions.MarkerOccurrence
import OAI.NumberTheory.EgyptianFractions.PrescribedCorollary
import OAI.NumberTheory.EgyptianFractions.ExactPadding
import OAI.NumberTheory.EgyptianFractions.CountingUpper
import OAI.NumberTheory.EgyptianFractions.CountingFromMarkers
import OAI.NumberTheory.EgyptianFractions.CountingFromMain
import OAI.NumberTheory.EgyptianFractions.MainLowerVerified
import OAI.NumberTheory.EgyptianFractions.RawDensityUpper
import OAI.NumberTheory.EgyptianFractions.RawDensityExistence
import OAI.NumberTheory.EgyptianFractions.MarkedThreePrimeReduction
import OAI.NumberTheory.EgyptianFractions.MangoldtMajorArcReduction
import OAI.NumberTheory.EgyptianFractions.CompositeSupplyFinal

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

theorem egyptian_length_is_minimum :
    ∀ a b : ℕ, 1 ≤ a → a < b →
  (∃ n : Fin (egyptianLength a b) → ℕ,
    IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n) ∧
  (∀ k : ℕ, (∃ n : Fin k → ℕ,
    IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n) →
    egyptianLength a b ≤ k) := by
  intro a b ha hab
  constructor
  · exact egyptianLength_attained_of_exists (exists_strict_unit_fraction_sum a b ha hab)
  · intro k hk
    exact egyptianLength_le_of_expansion hk

theorem main_double_log_order :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧ ∃ b0 : ℕ,
  ∀ b : ℕ, b0 ≤ b →
    c1 * Real.log (Real.log (b : ℝ)) ≤ (maxEgyptianLength b : ℝ) ∧
    (maxEgyptianLength b : ℝ) ≤ c2 * Real.log (Real.log (b : ℝ)) := by
  -- The unconditional arithmetic construction supplies the actual residue
  -- lists, common denominator, and divisor moments for the density descent.
  obtain ⟨DM, L, c, K, r, hDM, hL, hc, hK, hr, hKr, hsupply⟩ :
      ∃ DM L c K r : ℝ, 1 < DM ∧ 0 < L ∧ 0 < c ∧ 0 ≤ K ∧
        2 ≤ r ∧ 8 * K ≤ r ∧
        ∀ᶠ S : ℝ in Filter.atTop, ∀ C : ℕ,
          Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
          (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * S) →
          RawDensitySupply DM L c K r S C := exists_raw_density_supply
  obtain ⟨c2, hc2, b0, hupper⟩ :=
    main_upper_of_raw_density_supply DM L c K r hDM hL hc hK hr hKr hsupply
  refine ⟨1 / 2, c2, by norm_num, hc2, max 2 b0, ?_⟩
  intro b hb
  exact ⟨main_double_log_lower_bound b ((le_max_left 2 b0).trans hb),
    hupper b ((le_max_right 2 b0).trans hb)⟩

theorem one_expansions_finite_and_bounded :
    (∀ k : ℕ, Set.Finite (OneExpansions k) ∧
    F k ≤ k ^ (2 ^ k - 1)) ∧
  (∀ k : ℕ, ∀ n : Fin k → ℕ, IsOneExpansion n →
    ∀ i : Fin k, n i ≤ k ^ (2 ^ i.val)) := by
  constructor
  · intro k
    exact finite_ncard_le_egyptian_box k (OneExpansions k)
      (fun n hn => hn.1) (fun n hn => one_expansion_denominator_bound n hn)
  · intro k n hn
    exact one_expansion_denominator_bound n hn

theorem exact_marker_padding :
    ∀ r : ℕ, 3 ≤ r → ∀ n : Fin r → ℕ, IsOneExpansion n →
  ∀ m : ℕ, (∃ i : Fin r, n i = m) →
    ∃ n' : Fin (r + 1) → ℕ,
      IsOneExpansion n' ∧ ∃ i : Fin (r + 1), n' i = m := by
  exact exact_marker_padding_proof

theorem every_exact_marker_occurs :
    ∀ m : ℕ, 2 ≤ m → ∃ k : ℕ, m ∈ D k := by
  exact every_exact_marker_occurs_proof

theorem quantitative_marked_length :
    ∀ ε : ℝ, 0 < ε → ∃ mε : ℕ, 2 ≤ mε ∧
  ∀ m : ℕ, mε ≤ m →
    ∃ k : ℕ, ∃ n : Fin k → ℕ,
      IsOneExpansion n ∧
      (∃ i : Fin k, n i = m) ∧
      (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
  exact CompositeSupply.quantitative_marked_length

theorem missing_denominator_semantics :
    ∀ k : ℕ,
  Set.Finite (D k) ∧
  (∃ m : ℕ, m ∈ missingDenominators k) ∧
  2 ≤ v k ∧ v k ∉ D k ∧
  (∀ m : ℕ, 2 ≤ m → m < v k → m ∈ D k) ∧
  (1 ≤ k → v k ≤ 1 + k ^ (2 ^ (k - 1))) := by
  exact missing_denominator_semantics_of_bound
    (fun k n hn => one_expansion_denominator_bound n hn)

theorem prescribed_denominator_corollary :
    (∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
    Real.exp (Real.exp ((k : ℝ) / 600)) ≤ (v k : ℝ) ∧
    v k ≤ 1 + k ^ (2 ^ (k - 1))) ∧
  (Real.log 2 / 257 ≤ Filter.liminf prescribedSlope Filter.atTop ∧
    Filter.liminf prescribedSlope Filter.atTop ≤
      Filter.limsup prescribedSlope Filter.atTop ∧
    Filter.limsup prescribedSlope Filter.atTop ≤ Real.log 2) ∧
  (∀ c : ℝ, c < Real.log 2 / 257 → ∃ k0 : ℕ,
    ∀ k : ℕ, k0 ≤ k →
      Real.exp (Real.exp (c * (k : ℝ))) ≤ (v k : ℝ)) := by
  exact prescribed_denominator_corollary_of_inputs
    exact_marker_padding every_exact_marker_occurs quantitative_marked_length
    (fun k => ⟨(missing_denominator_semantics k).2.2.1,
      (missing_denominator_semantics k).2.2.2.1⟩)
    (fun k => (missing_denominator_semantics k).2.2.2.2.2)

theorem counting_double_log_order :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k0 : ℕ,
  ∀ k : ℕ, k0 ≤ k →
    c * (k : ℝ) ≤ Real.log (Real.log (F k : ℝ)) ∧
    Real.log (Real.log (F k : ℝ)) ≤ C * (k : ℝ) := by
  apply counting_order_of_main_upper
  obtain ⟨c1, c2, hc1, hc2, b0, hbounds⟩ := main_double_log_order
  refine ⟨c2, hc2, Filter.eventually_atTop.2 ⟨b0, ?_⟩⟩
  intro b hb
  exact (hbounds b hb).2

end Problem337

end

end OAI
