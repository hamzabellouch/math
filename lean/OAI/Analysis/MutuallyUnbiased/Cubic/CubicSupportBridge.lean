import OAI.Analysis.MutuallyUnbiased.Cubic.CubicSupport
import OAI.Analysis.MutuallyUnbiased.Cubic.CubicMultiplicity

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem cubed_entries_twoValuePattern (v : Fin 6 → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) :
    TwoValuePattern (fun i => v i ^ 3) := by
  classical
  have ht := cube_values_at_most_two v hv h1 h2
  refine ⟨ht, ?_⟩
  intro a ha hb
  obtain ⟨ia, hia⟩ := ha
  obtain ⟨ib, hib⟩ := hb
  change v ia ^ 3 = a at hia
  change v ib ^ 3 ≠ a at hib
  have hne : v ia ^ 3 ≠ v ib ^ 3 := by rw [hia]; exact Ne.symm hib
  have hvalues : ∀ i, v i ^ 3 = a ∨ v i ^ 3 = v ib ^ 3 := by
    simpa [hia] using value_pair_exhausts (fun i => v i ^ 3) ht ia ib hne
  have hc := two_cube_classes_card_three v hv h1 h2 a (v ib ^ 3)
    (Ne.symm hib) hvalues ia ib hia rfl
  exact hc.1

end MUB6

end

end OAI
