import OAI.Combinatorics.BalancedRyser.Incidence.ProfileEmpiricalIncidence
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileCoordinates
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileMeans

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

universe u

variable {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
  [∀ n, DecidableEq (F n)]
  {D C : ∀ n, Finset (Line (F n))}
  {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}

theorem ProfileSequenceLimit.deletion_incidence
    (hlim : ProfileSequenceLimit D C c P νD νC) (ij : ℕ × ℕ) :
    (∫ x, x ij ∂(νD : Measure Profile)) = (ij.1 : ℝ) * P ij := by
  apply ambient_profile_incidence_weak_limit ij hlim.2.2.1 hlim.2.1
  · intro n
    filter_upwards [FiniteProfile.empiricalProfileMeasure_unit_coordinates
      (D n) (C n) (D n)] with x hx
    exact hx ij
  · intro n
    exact FiniteProfile.empiricalProfileMeasure_deletion_incidence
      (D n) (C n) ij.1 ij.2

theorem ProfileSequenceLimit.cover_incidence
    (hlim : ProfileSequenceLimit D C c P νD νC) (ij : ℕ × ℕ) :
    (∫ x, x ij ∂(νC : Measure Profile)) = (ij.2 : ℝ) * P ij := by
  apply ambient_profile_incidence_weak_limit ij hlim.2.2.2 hlim.2.1
  · intro n
    filter_upwards [FiniteProfile.empiricalProfileMeasure_unit_coordinates
      (D n) (C n) (C n)] with x hx
    exact hx ij
  · intro n
    exact FiniteProfile.empiricalProfileMeasure_cover_incidence
      (D n) (C n) ij.1 ij.2

theorem ProfileSequenceLimit.cover_mass
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    (νC : Measure Profile).real Set.univ = c := by
  apply profile_mass_weak_limit hlim.2.2.2
  simpa only [FiniteProfile.empiricalProfileMeasure_mass] using hlim.1

theorem ProfileSequenceLimit.deletion_mass {k : ℕ}
    (hlim : ProfileSequenceLimit D C c P νD νC)
    (hD : ∀ n, IsDeletionSet k (D n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    (νD : Measure Profile).real Set.univ = (k : ℝ) := by
  exact profile_mass_weak_limit hlim.2.2.1
    (FiniteProfile.empiricalProfileMeasure_deletion_mass_tendsto D C hD hq)

theorem ProfileSequenceLimit.deletion_mean {k : ℕ} {M : ℝ}
    (hlim : ProfileSequenceLimit D C c P νD νC)
    (hD : ∀ n, IsDeletionSet k (D n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    (hsupp : ∀ᵐ x ∂(νD : Measure Profile), IsBoundedProfile M x) :
    HasSum (fun ij : ℕ × ℕ => (ij.1 : ℝ) * P ij) (k : ℝ) := by
  apply deletion_profile_first_mean (νD : Measure Profile)
    (fun ij x => x ij) P k
  · intro ij
    exact (continuous_apply ij).aestronglyMeasurable
  · intro ij
    exact hsupp.mono (fun x hx => hx.1 ij)
  · exact hsupp.mono (fun x hx => hx.2.1)
  · exact hlim.deletion_incidence
  · exact hlim.deletion_mass hD hq

theorem ProfileSequenceLimit.cover_mean {M : ℝ}
    (hlim : ProfileSequenceLimit D C c P νD νC)
    (hsupp : ∀ᵐ x ∂(νC : Measure Profile), IsBoundedProfile M x) :
    HasSum (fun ij : ℕ × ℕ => (ij.2 : ℝ) * P ij) c := by
  apply deletion_profile_second_mean (νC : Measure Profile)
    (fun ij x => x ij) P c
  · intro ij
    exact (continuous_apply ij).aestronglyMeasurable
  · intro ij
    exact hsupp.mono (fun x hx => hx.1 ij)
  · exact hsupp.mono (fun x hx => hx.2.1)
  · exact hlim.cover_incidence
  · exact hlim.cover_mass

end Balanced

namespace Balanced.FiniteProfile
open scoped _root_.Balanced

variable {K : ℕ → Type*} [∀ n, Field (K n)] [∀ n, Fintype (K n)]
  [∀ n, DecidableEq (K n)]
  {D C : ∀ n, Finset (Line (K n))}
  {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}

theorem profileSequenceLimit_deletion_incidence
    (hlim : ProfileSequenceLimit D C c P νD νC) (ij : ℕ × ℕ) :
    (∫ x, x ij ∂(νD : Measure Profile)) = (ij.1 : ℝ) * P ij :=
  hlim.deletion_incidence ij

theorem profileSequenceLimit_cover_incidence
    (hlim : ProfileSequenceLimit D C c P νD νC) (ij : ℕ × ℕ) :
    (∫ x, x ij ∂(νC : Measure Profile)) = (ij.2 : ℝ) * P ij :=
  hlim.cover_incidence ij

theorem profileSequenceLimit_deletion_mass {k : ℕ}
    (hD : ∀ n, IsDeletionSet k (D n))
    (hq : Tendsto (fun n => Fintype.card (K n)) atTop atTop)
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    (νD : Measure Profile).real Set.univ = k :=
  hlim.deletion_mass hD hq

theorem profileSequenceLimit_cover_mass
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    (νC : Measure Profile).real Set.univ = c := hlim.cover_mass

theorem profileSequenceLimit_mass_incidence (k : ℕ)
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (K n)) atTop atTop)
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    (νD : Measure Profile).real Set.univ = k ∧
    (νC : Measure Profile).real Set.univ = c ∧
    (∀ ij, (∫ x, x ij ∂(νD : Measure Profile)) = (ij.1 : ℝ) * P ij) ∧
    (∀ ij, (∫ x, x ij ∂(νC : Measure Profile)) = (ij.2 : ℝ) * P ij) :=
  ⟨profileSequenceLimit_deletion_mass (fun n => (hpair n).1) hq hlim,
    profileSequenceLimit_cover_mass hlim,
    profileSequenceLimit_deletion_incidence hlim,
    profileSequenceLimit_cover_incidence hlim⟩

end Balanced.FiniteProfile

end

end OAI
