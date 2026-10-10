import OAI.Combinatorics.BalancedRyser.Profiles.ProfileDetectionLimit
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileEmpiricalSupport

namespace OAI

open MeasureTheory Filter
open scoped Topology

namespace Balanced.ProfileDetectionSource

open ProfileDetection ProfileDetectionBridge ProfileParameterLaw ProfileDetectionLimit

universe u

theorem profileSequenceLimit_cutoff_sum_visible_mass
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC) :
    Tendsto (fun n : ℕ =>
      ((νD : Measure Profile).prod (parameterLaw 1)).real
        (cutoffDetection Prod.snd (dDiscrepancy P) n) +
      ((νC : Measure Profile).prod (parameterLaw (Real.sqrt 2))).real
        (cutoffDetection Prod.snd (cDiscrepancy P) n)) atTop
      (𝓝 ((νD : Measure Profile).real (deletionVisible P) +
        (νC : Measure Profile).real (coverVisible P))) := by
  obtain ⟨hP, hD, hC⟩ :=
    ProfileEmpiricalSupport.profileSequenceLimit_bounded k D C hpair ht
  obtain ⟨hD0, hC0⟩ :=
    ProfileEmpiricalSupport.profileSequenceLimit_zero_coordinates k D C hpair ht
  apply tendsto_cutoff_sum_visible_mass νD νC P hP.2.1.summable
  · filter_upwards [hD, hD0] with x hx hx0
    exact ⟨hx.2.1.summable, hx0⟩
  · filter_upwards [hC, hC0] with x hx hx0
    exact ⟨hx.2.1.summable, hx0⟩

theorem exists_cutoff_of_visible_excess
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC)
    (hexcess : c < (νD : Measure Profile).real (deletionVisible P) +
      (νC : Measure Profile).real (coverVisible P)) :
    ∃ n : ℕ, c <
      ((νD : Measure Profile).prod (parameterLaw 1)).real
        (cutoffDetection Prod.snd (dDiscrepancy P) n) +
      ((νC : Measure Profile).prod (parameterLaw (Real.sqrt 2))).real
        (cutoffDetection Prod.snd (cDiscrepancy P) n) := by
  exact ((tendsto_order.mp
    (profileSequenceLimit_cutoff_sum_visible_mass k D C hpair ht)).1 c hexcess).exists

end Balanced.ProfileDetectionSource

end OAI
