import Mathlib.MeasureTheory.Measure.Real
import OAI.Combinatorics.BalancedRyser.Profiles.Profile

namespace OAI

open MeasureTheory

namespace Balanced.ProfileVisibility

def deletionShift (P : Profile) : Profile := fun ij =>
  if ij.1 = 0 then 0 else P (ij.1 - 1, ij.2)

def coverShift (P : Profile) : Profile := fun ij =>
  if ij.2 = 0 then 0 else P (ij.1, ij.2 - 1)

theorem deletionInvisible_iff_eq (P x : Profile) :
    deletionInvisible P x ↔ x = deletionShift P := by
  constructor
  · intro h
    funext ij
    exact h ij.1 ij.2
  · intro h
    subst x
    intro i j
    rfl

theorem coverInvisible_iff_eq (P x : Profile) :
    coverInvisible P x ↔ x = coverShift P := by
  constructor
  · intro h
    funext ij
    exact h ij.1 ij.2
  · intro h
    subst x
    intro i j
    rfl

theorem continuous_deletionShift : Continuous deletionShift := by
  apply continuous_pi
  intro ij
  by_cases hi : ij.1 = 0
  · simpa [deletionShift, hi] using (continuous_const : Continuous (fun _ : Profile => (0 : ℝ)))
  · simpa [deletionShift, hi] using (continuous_apply (ij.1 - 1, ij.2))

theorem continuous_coverShift : Continuous coverShift := by
  apply continuous_pi
  intro ij
  by_cases hj : ij.2 = 0
  · simpa [coverShift, hj] using (continuous_const : Continuous (fun _ : Profile => (0 : ℝ)))
  · simpa [coverShift, hj] using (continuous_apply (ij.1, ij.2 - 1))

theorem isClosed_deletionInvisible :
    IsClosed {u : Profile × Profile | deletionInvisible u.1 u.2} := by
  simpa only [deletionInvisible_iff_eq, Function.comp_def] using
    (isClosed_eq continuous_snd (continuous_deletionShift.comp continuous_fst))

theorem isClosed_coverInvisible :
    IsClosed {u : Profile × Profile | coverInvisible u.1 u.2} := by
  simpa only [coverInvisible_iff_eq, Function.comp_def] using
    (isClosed_eq continuous_snd (continuous_coverShift.comp continuous_fst))

theorem isOpen_joint_deletionVisible :
    IsOpen {u : Profile × Profile | u.2 ∈ deletionVisible u.1} :=
  isClosed_deletionInvisible.isOpen_compl

theorem isOpen_joint_coverVisible :
    IsOpen {u : Profile × Profile | u.2 ∈ coverVisible u.1} :=
  isClosed_coverInvisible.isOpen_compl

theorem deletionVisible_eq_compl_singleton (P : Profile) :
    deletionVisible P = {deletionShift P}ᶜ := by
  ext x
  simp [deletionVisible, deletionInvisible_iff_eq]

theorem coverVisible_eq_compl_singleton (P : Profile) :
    coverVisible P = {coverShift P}ᶜ := by
  ext x
  simp [coverVisible, coverInvisible_iff_eq]

theorem isOpen_deletionVisible (P : Profile) : IsOpen (deletionVisible P) := by
  rw [deletionVisible_eq_compl_singleton]
  exact isClosed_singleton.isOpen_compl

theorem isOpen_coverVisible (P : Profile) : IsOpen (coverVisible P) := by
  rw [coverVisible_eq_compl_singleton]
  exact isClosed_singleton.isOpen_compl

theorem measurableSet_deletionVisible (P : Profile) :
    MeasurableSet (deletionVisible P) := (isOpen_deletionVisible P).measurableSet

theorem measurableSet_coverVisible (P : Profile) :
    MeasurableSet (coverVisible P) := (isOpen_coverVisible P).measurableSet

theorem measureReal_deletionVisible (μ : Measure Profile) [IsFiniteMeasure μ]
    (P : Profile) :
    μ.real (deletionVisible P) = μ.real Set.univ - μ.real {deletionShift P} := by
  rw [deletionVisible_eq_compl_singleton]
  exact measureReal_compl (measurableSet_singleton _)

theorem measureReal_coverVisible (μ : Measure Profile) [IsFiniteMeasure μ]
    (P : Profile) :
    μ.real (coverVisible P) = μ.real Set.univ - μ.real {coverShift P} := by
  rw [coverVisible_eq_compl_singleton]
  exact measureReal_compl (measurableSet_singleton _)

end Balanced.ProfileVisibility

end OAI
