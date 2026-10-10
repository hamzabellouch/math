import OAI.Combinatorics.BalancedRyser.Incidence.ProfileEmpiricalIncidence
import OAI.Combinatorics.BalancedRyser.Probability.MultiplicityLimit
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileCoordinates

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter MeasureTheory
open scoped Topology

universe u

theorem multiplicityFailureClass_visibleExcess
    (k : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    ProfileVisibleExcess (multiplicityFailureClass.{u} k τ) := by
  intro F _ _ _ D C hclass hq c P νD νC hlim
  have hc := multiplicityFailureClass_limit_density_zero k τ D C hclass hlim
  have hmass : (νD : Measure Profile).real Set.univ = (k : ℝ) :=
    profile_mass_weak_limit hlim.2.2.1
      (FiniteProfile.empiricalProfileMeasure_deletion_mass_tendsto D C
        (fun n => (hclass n).1) hq)
  have hinc (i : ℕ) :
      (∫ x : Profile, x (i + 1, 0) ∂(νD : Measure Profile)) =
        (i + 1 : ℝ) * P (i + 1, 0) := by
    apply ambient_profile_incidence_weak_limit (i + 1, 0) hlim.2.2.1 hlim.2.1
    · intro n
      filter_upwards [FiniteProfile.empiricalProfileMeasure_unit_coordinates
        (D n) (C n) (D n)] with x hx
      exact hx (i + 1, 0)
    · intro n
      simpa only [Nat.cast_add, Nat.cast_one] using
        FiniteProfile.empiricalProfileMeasure_deletion_incidence (D n) (C n) (i + 1) 0
  have hnorm := (multiplicityFailureClass_limit_probability k τ D C hclass hlim).2
  have htv := multiplicityFailureClass_limit_tv k τ D C hclass hlim
  have hvisible := deletionVisible_positive_of_tv k P (νD : Measure Profile)
    hmass hnorm hinc (lt_of_lt_of_le hτ htv)
  rw [hc]
  exact lt_of_lt_of_le hvisible (le_add_of_nonneg_right measureReal_nonneg)

theorem robustMultiplicity_of_profileCounting
    (hcounting : ProfileCountingResult.{u})
    (k : ℕ) (hk : 1 ≤ k) (K τ : ℝ) (hτ : 0 < τ) :
    UniformDeletionVanishing.{u} k K
      (fun _ _ _ _ D => τ ≤ deletionMultiplicityTV k D.val) := by
  exact multiplicityVanishing_of_profileCounting hcounting k hk K τ
    (multiplicityFailureClass_visibleExcess k τ hτ)

end Balanced

end OAI
