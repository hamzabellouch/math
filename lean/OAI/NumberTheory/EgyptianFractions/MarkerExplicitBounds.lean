import OAI.NumberTheory.EgyptianFractions.MarkerOccurrence
import OAI.NumberTheory.EgyptianFractions.MarkerCoverage
import OAI.NumberTheory.EgyptianFractions.ExactPadding
import OAI.NumberTheory.EgyptianFractions.DenominatorBound
import OAI.NumberTheory.EgyptianFractions.MissingSemantics

namespace OAI
noncomputable section

namespace Problem337

/-- A marker smaller than the prescribed length always occurs at that exact length. -/
theorem marker_occurs_at_length_of_lt {m k : ℕ} (hm : 2 ≤ m) (hmk : m < k) :
    m ∈ D k := by
  obtain ⟨r, hr, hmarker⟩ := every_exact_marker_occurs_bounded m hm
  exact D_mono_of_padding exact_marker_padding_proof (by omega : r ≤ k) hmarker

/-- The qualitative finite-exception cutoff can be chosen explicitly. -/
theorem bounded_markers_at_explicit_length {B k : ℕ} (hBk : B < k) :
    ∀ m : ℕ, 2 ≤ m → m ≤ B → m ∈ D k := by
  intro m hm hmB
  exact marker_occurs_at_length_of_lt hm (by omega)

/-- A basic unconditional lower bound for the first missing denominator. -/
theorem length_le_first_missing (k : ℕ) : k ≤ v k := by
  have hsem := missing_denominator_semantics_of_bound
    (fun _ n hn => one_expansion_denominator_bound n hn) k
  by_contra h
  have hvk : v k < k := by omega
  exact hsem.2.2.2.1 (marker_occurs_at_length_of_lt hsem.2.2.1 hvk)

theorem first_missing_tendsto_atTop :
    Filter.Tendsto v Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_mono length_le_first_missing Filter.tendsto_id

end Problem337

end

end OAI
