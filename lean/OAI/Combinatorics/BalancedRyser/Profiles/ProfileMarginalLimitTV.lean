import OAI.Combinatorics.BalancedRyser.Profiles.ProfileEmpiricalSupport
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileMarginalTV

namespace OAI

open Filter MeasureTheory
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

universe u
variable {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
  [∀ n, DecidableEq (F n)]
  {D C : ∀ n, Finset (Line (F n))}
  {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile} {k : ℕ}

theorem ProfileSequenceLimit.marginal_totalVariation_tendsto
    (hlim : ProfileSequenceLimit D C c P νD νC)
    (hpair : ∀ n, IsProfilePair k (D n) (C n)) :
    Tendsto (fun n => (1 / 2 : ℝ) *
      ∑' i, |empiricalMultiplicityMass (D n) i - ∑' j, P (i,j)|)
      atTop (𝓝 0) := by
  have hP := (ProfileEmpiricalSupport.profileSequenceLimit_bounded k D C hpair hlim).1
  exact ProfileMarginalTV.empiricalMultiplicity_tendsto_marginal D C hP.1 hP.2.1
    (tendsto_pi_nhds.mp hlim.2.1)

theorem ProfileSequenceLimit.deletionMultiplicityTV_tendsto
    (hlim : ProfileSequenceLimit D C c P νD νC)
    (hpair : ∀ n, IsProfilePair k (D n) (C n)) :
    Tendsto (fun n => deletionMultiplicityTV k (D n)) atTop
      (𝓝 ((1 / 2 : ℝ) * ∑' i, |(∑' j, P (i,j)) - deletionPoissonMass k i|)) := by
  have hP := (ProfileEmpiricalSupport.profileSequenceLimit_bounded k D C hpair hlim).1
  exact ProfileMarginalTV.deletionMultiplicityTV_tendsto D C k hP.1 hP.2.1
    (tendsto_pi_nhds.mp hlim.2.1)

theorem ProfileSequenceLimit.bad_multiplicityTV_persists
    (hlim : ProfileSequenceLimit D C c P νD νC)
    (hpair : ∀ n, IsProfilePair k (D n) (C n)) {τ : ℝ}
    (hbad : ∀ n, τ ≤ deletionMultiplicityTV k (D n)) :
    τ ≤ (1 / 2 : ℝ) * ∑' i, |(∑' j, P (i,j)) - deletionPoissonMass k i| :=
  ge_of_tendsto (hlim.deletionMultiplicityTV_tendsto hpair)
    (Eventually.of_forall hbad)

theorem ProfileSequenceLimit.poisson_marginal_of_vanishing_tolerance
    (hlim : ProfileSequenceLimit D C c P νD νC)
    (hpair : ∀ n, IsProfilePair k (D n) (C n)) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hsmall : ∀ n, deletionMultiplicityTV k (D n) ≤ ε n) :
    ∀ i, (∑' j, P (i,j)) = deletionPoissonMass k i := by
  have hP := (ProfileEmpiricalSupport.profileSequenceLimit_bounded k D C hpair hlim).1
  exact ProfileMarginalTV.poisson_marginal_of_vanishing_tolerance D C k hε hsmall
    hP.1 hP.2.1 (tendsto_pi_nhds.mp hlim.2.1)

end Balanced

end OAI
