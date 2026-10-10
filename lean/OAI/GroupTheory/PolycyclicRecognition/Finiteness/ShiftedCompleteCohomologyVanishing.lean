import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ShiftedCompletedCohomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompletedCohomologyProjective
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompletedCohomologyColimitSurjectivity

namespace OAI

/-! # Projective vanishing and coefficient limits in nonnegative complete degrees -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem normalizedSyzygy_delta_eq_zero_of_eq (A : Rep.{0} ℤ G) [Projective A]
    (i j : ℕ) (h : i + 1 = j) :
    groupCohomology.δ (normalizedSyzygySequence_shortExact A) i j h = 0 := by
  subst j
  exact normalizedSyzygy_delta_eq_zero A i

theorem shiftedSyzygyConnecting_eq_zero (p : ℕ) (A : Rep.{0} ℤ G)
    [Projective A] (n : ℕ) : shiftedSyzygyConnecting p A n = 0 :=
  normalizedSyzygy_delta_eq_zero_of_eq ((iteratedNormalizedSyzygy n).obj A)
    (n + p) (n + 1 + p) (by omega)

theorem shiftedCompleteCohomology_subsingleton_of_finite_projectiveDimension
    (p : ℕ) (A : Rep.{0} ℤ G) (d : ℕ) [HasProjectiveDimensionLE A d] :
    Subsingleton (ShiftedCompletedCohomology p A) := by
  apply subsingleton_of_forall_eq (0 : ShiftedCompletedCohomology p A)
  intro z
  obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
  let m := max i d
  have hAm : HasProjectiveDimensionLE A (m + 0) :=
    hasProjectiveDimensionLT_of_ge A (d + 1) (m + 0 + 1) (by dsimp [m]; omega)
  let : Projective ((iteratedNormalizedSyzygy m).obj A) :=
    (projective_iff_hasProjectiveDimensionLE_zero _).mpr
      (iteratedNormalizedSyzygy_projectiveDimension A m 0 hAm)
  let y := shiftedCohomologyForward p A i m (le_max_left i d) x
  have hz : shiftedCohomologyForward p A m (m + 1) (Nat.le_succ m) y = 0 := by
    change Nat.leRecOn (C := shiftedCohomologyStage p A) (Nat.le_succ m)
      (fun {k} => (shiftedSyzygyConnecting p A k).hom) y = 0
    rw [Nat.leRecOn_succ (le_refl m), Nat.leRecOn_self]
    change (shiftedSyzygyConnecting p A m).hom y = 0
    rw [show shiftedSyzygyConnecting p A m = 0 from
      normalizedSyzygy_delta_eq_zero_of_eq ((iteratedNormalizedSyzygy m).obj A)
        (m + p) (m + 1 + p) (by omega)]
    rfl
  have he := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ)
    (G := shiftedCohomologyStage p A) (f := shiftedCohomologyForward p A)
    (hij := Nat.le_succ m) (x := y)
  rw [hz, map_zero] at he
  have hi := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ)
    (G := shiftedCohomologyStage p A) (f := shiftedCohomologyForward p A)
    (hij := le_max_left i d) (x := x)
  exact hi.symm.trans he.symm

theorem TypeFPInfinity.shiftedCompleteCohomology_colimit_surj
    (hG : TypeFPInfinity G) (p : ℕ) (D : SequentialRepresentationDiagram G)
    (A : Rep.{0} ℤ G) (c : D.ColimitCocone A) (x : ShiftedCompletedCohomology p A) :
    ∃ (i : ℕ) (y : ShiftedCompletedCohomology p (D.obj i)),
      shiftedCompletedCohomologyMap p (c.ι i) y = x := by
  obtain ⟨n, z, rfl⟩ := Module.DirectLimit.exists_of x
  let E := D.mapFunctor (iteratedNormalizedSyzygy n)
  let ec := c.iteratedNormalizedSyzygy n
  obtain ⟨i, y, hy⟩ := hG.cohomology_colimit_surj E
    ((iteratedNormalizedSyzygy n).obj A) ec (n + p) z
  change shiftedCohomologyStage p (D.obj i) n at y
  refine ⟨i, Module.DirectLimit.of ℤ ℕ _ (shiftedCohomologyForward p (D.obj i)) n y, ?_⟩
  rw [shiftedCompletedCohomologyMap_of]
  have hy' : shiftedCohomologyStageMap p (c.ι i) n y = z := by
    rw [SequentialRepresentationDiagram.ColimitCocone.iteratedNormalizedSyzygy_ι] at hy
    exact hy
  rw [hy']

theorem TypeFPInfinity.shiftedCompleteCohomology_colimit_subsingleton
    (hG : TypeFPInfinity G) (p : ℕ) (D : SequentialRepresentationDiagram G)
    (A : Rep.{0} ℤ G) (c : D.ColimitCocone A)
    (hz : ∀ i, Subsingleton (ShiftedCompletedCohomology p (D.obj i))) :
    Subsingleton (ShiftedCompletedCohomology p A) := by
  apply subsingleton_of_forall_eq (0 : ShiftedCompletedCohomology p A)
  intro x
  obtain ⟨i, y, rfl⟩ := hG.shiftedCompleteCohomology_colimit_surj p D A c x
  rw [(hz i).elim y 0, map_zero]

end PolycyclicRecognition

end

end OAI
