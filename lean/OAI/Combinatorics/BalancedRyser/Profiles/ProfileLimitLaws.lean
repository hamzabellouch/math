import OAI.Combinatorics.BalancedRyser.Incidence.ProfileLimitIncidence
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileEmpiricalSupport

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

theorem ProfileSequenceLimit.mean_laws {k : ℕ}
    (hlim : ProfileSequenceLimit D C c P νD νC)
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    HasSum (fun ij : ℕ × ℕ => (ij.1 : ℝ) * P ij) (k : ℝ) ∧
    HasSum (fun ij : ℕ × ℕ => (ij.2 : ℝ) * P ij) c := by
  have hs := ProfileEmpiricalSupport.profileSequenceLimit_bounded k D C hpair hlim
  exact ⟨hlim.deletion_mean (fun n => (hpair n).1) hq hs.2.1,
    hlim.cover_mean hs.2.2⟩

theorem ProfileSequenceLimit.deletion_recurrence {k : ℕ}
    (hlim : ProfileSequenceLimit D C c P νD νC)
    (hD : ∀ n, IsDeletionSet k (D n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    (hinvisible : ∀ᵐ x ∂(νD : Measure Profile), deletionInvisible P x) :
    ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1, j) = (k : ℝ) * P (i, j) := by
  apply invisible_profile_recurrence (νD : Measure Profile)
    (fun ij x => x ij) (fun i j => P (i, j)) k
  · intro i j
    simpa only [Nat.cast_add, Nat.cast_one] using hlim.deletion_incidence (i + 1, j)
  · intro i j
    filter_upwards [hinvisible] with x hx
    simpa only [deletionInvisible, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ite_false, Nat.add_sub_cancel] using hx (i + 1) j
  · exact hlim.deletion_mass hD hq

theorem ProfileSequenceLimit.cover_recurrence
    (hlim : ProfileSequenceLimit D C c P νD νC)
    (hinvisible : ∀ᵐ x ∂(νC : Measure Profile), coverInvisible P x) :
    ∀ i j : ℕ, (j + 1 : ℝ) * P (i, j + 1) = c * P (i, j) := by
  apply invisible_cover_profile_recurrence (νC : Measure Profile)
    (fun ij x => x ij) (fun i j => P (i, j)) c
  · intro i j
    simpa only [Nat.cast_add, Nat.cast_one] using hlim.cover_incidence (i, j + 1)
  · intro i j
    filter_upwards [hinvisible] with x hx
    simpa only [coverInvisible, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ite_false, Nat.add_sub_cancel] using hx i (j + 1)
  · exact hlim.cover_mass

end Balanced

end

end OAI
