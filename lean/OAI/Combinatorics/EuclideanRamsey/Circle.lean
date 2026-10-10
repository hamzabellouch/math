import OAI.Combinatorics.EuclideanRamsey.CircleRows
import OAI.Combinatorics.EuclideanRamsey.CircleSpan
import OAI.Combinatorics.EuclideanRamsey.CircleExtension
import OAI.Combinatorics.EuclideanRamsey.Quadratic

namespace OAI

noncomputable section
namespace EuclideanRamsey.CircleConsequence

/-- Every five-point subset of a circle is Ramsey. -/
theorem five_circle_points_ramsey (a : Fin 5 → Space 2)
    (ha : Function.Injective a) (c : Space 2) (r : ℝ)
    (hc : ∀ i, dist (a i) c = r) : Ramsey a := by
  exact spherical_quadraticIndependent_ramsey a (by decide) ha
    (circle_five_affineSpan a ha c r hc) ⟨c, r, hc⟩
    (circle_five_rows_independent a ha c r hc)

/-- Every nonempty set of at most five distinct circle points is Ramsey,
including singletons and zero-radius circles. -/
theorem at_most_five_circle_points_ramsey {s : ℕ} (a : Fin s → Space 2)
    (hs : 0 < s) (hs5 : s ≤ 5) (ha : Function.Injective a)
    (hsphere : ∃ c : Space 2, ∃ r : ℝ, ∀ i, dist (a i) c = r) : Ramsey a := by
  obtain ⟨c, r, hc⟩ := hsphere
  have hr : 0 ≤ r := by
    rw [← hc ⟨0, hs⟩]
    exact dist_nonneg
  by_cases hr0 : r = 0
  · exact zero_radius_ramsey a c (by simpa [hr0] using hc)
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    obtain ⟨b, hb, hbc, f, hf⟩ := extend_to_five a hs5 ha c r hrpos hc
    have hramsey := ramsey_restrict b f (five_circle_points_ramsey b hb c r hbc)
    have he : b ∘ f = a := funext hf
    rwa [he] at hramsey

end EuclideanRamsey.CircleConsequence

end

end OAI
