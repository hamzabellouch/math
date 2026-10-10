import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompletedCohomology

namespace OAI

/-! # Complete cohomology vanishes on projective coefficients -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

instance normalizedSyzygy_projective (A : Rep.{0} ℤ G) [Projective A] :
    Projective (normalizedSyzygy A) := by
  apply (projective_iff_hasProjectiveDimensionLE_zero _).mpr
  exact (normalizedSyzygySequence_shortExact A).hasProjectiveDimensionLT_X₁ 1
    (inferInstance : HasProjectiveDimensionLT (normalizedFreeRepresentation A) 1)
    (hasProjectiveDimensionLT_of_ge A 1 2 (by omega))

instance iteratedNormalizedSyzygy_projective (A : Rep.{0} ℤ G) [Projective A] (n : ℕ) :
    Projective ((iteratedNormalizedSyzygy n).obj A) := by
  induction n with
  | zero => exact inferInstanceAs (Projective A)
  | succ n ih =>
    let := ih
    change Projective (normalizedSyzygy ((iteratedNormalizedSyzygy n).obj A))
    infer_instance

theorem normalizedSyzygy_delta_eq_zero (A : Rep.{0} ℤ G) [Projective A] (n : ℕ) :
    groupCohomology.δ (normalizedSyzygySequence_shortExact A) n (n + 1) rfl = 0 := by
  let s := Projective.factorThru (𝟙 A) (normalizedFreeAugmentation A)
  have hs : s ≫ normalizedFreeAugmentation A = 𝟙 A := Projective.factorThru_comp _ _
  let F := groupCohomology.functor ℤ G n
  let δ : F.obj A ⟶ groupCohomology (normalizedSyzygy A) (n + 1) :=
    groupCohomology.δ (normalizedSyzygySequence_shortExact A) n (n + 1) rfl
  change δ = 0
  have hs' : F.map s ≫ F.map (normalizedFreeAugmentation A) = 𝟙 _ := by
    rw [← F.map_comp, hs, F.map_id]
  have hz := (groupCohomology.mapShortComplex₃
    (normalizedSyzygySequence_shortExact A) (rfl : n + 1 = n + 1)).zero
  change F.map (normalizedFreeAugmentation A) ≫ δ = 0 at hz
  have he : (F.map s ≫ F.map (normalizedFreeAugmentation A)) ≫ δ = 0 := by
    rw [Category.assoc, hz, comp_zero]
  simpa only [hs', Category.id_comp] using he

theorem normalizedSyzygyConnecting_eq_zero (A : Rep.{0} ℤ G) [Projective A] (n : ℕ) :
    normalizedSyzygyConnecting A n = 0 :=
  normalizedSyzygy_delta_eq_zero ((iteratedNormalizedSyzygy n).obj A) n

theorem completedCohomology_subsingleton_of_projective (A : Rep.{0} ℤ G) [Projective A] :
    Subsingleton (CompletedCohomology A) := by
  apply subsingleton_of_forall_eq (0 : CompletedCohomology A)
  intro z
  obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
  have hz : normalizedCohomologyForward A i (i + 1) (Nat.le_succ i) x = 0 := by
    change Nat.leRecOn (C := normalizedCohomologyStage A) (Nat.le_succ i)
      (fun {k} => (normalizedSyzygyConnecting A k).hom) x = 0
    rw [Nat.leRecOn_succ (le_refl i), Nat.leRecOn_self]
    change (normalizedSyzygyConnecting A i).hom x = 0
    rw [normalizedSyzygyConnecting_eq_zero]
    rfl
  have he := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ)
    (G := normalizedCohomologyStage A) (f := normalizedCohomologyForward A)
    (hij := Nat.le_succ i) (x := x)
  rw [hz, map_zero] at he
  exact he.symm

theorem iteratedNormalizedSyzygy_projectiveDimension
    (A : Rep.{0} ℤ G) (n d : ℕ) (hA : HasProjectiveDimensionLE A (n + d)) :
    HasProjectiveDimensionLE ((iteratedNormalizedSyzygy n).obj A) d := by
  induction n generalizing d with
  | zero => simpa only [Nat.zero_add, iteratedNormalizedSyzygy, Functor.id_obj] using hA
  | succ n ih =>
    have hA' : HasProjectiveDimensionLE A (n + (d + 1)) := by
      simpa only [Nat.succ_add, Nat.add_succ] using hA
    have hprev := ih (d + 1) hA'
    exact (normalizedSyzygySequence_shortExact ((iteratedNormalizedSyzygy n).obj A)).hasProjectiveDimensionLT_X₁ (d + 1)
        (hasProjectiveDimensionLT_of_ge
          (normalizedFreeRepresentation ((iteratedNormalizedSyzygy n).obj A))
          1 (d + 1) (by omega)) hprev

theorem completedCohomology_subsingleton_of_finite_projectiveDimension
    (A : Rep.{0} ℤ G) (d : ℕ) [HasProjectiveDimensionLE A d] :
    Subsingleton (CompletedCohomology A) := by
  apply subsingleton_of_forall_eq (0 : CompletedCohomology A)
  intro z
  obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
  let m := max i d
  have hAm : HasProjectiveDimensionLE A (m + 0) :=
    hasProjectiveDimensionLT_of_ge A (d + 1) (m + 0 + 1)
      (by dsimp [m]; omega)
  let : Projective ((iteratedNormalizedSyzygy m).obj A) :=
    (projective_iff_hasProjectiveDimensionLE_zero _).mpr
      (iteratedNormalizedSyzygy_projectiveDimension A m 0 hAm)
  let y := normalizedCohomologyForward A i m (le_max_left i d) x
  have hz : normalizedCohomologyForward A m (m + 1) (Nat.le_succ m) y = 0 := by
    change Nat.leRecOn (C := normalizedCohomologyStage A) (Nat.le_succ m)
      (fun {k} => (normalizedSyzygyConnecting A k).hom) y = 0
    rw [Nat.leRecOn_succ (le_refl m), Nat.leRecOn_self]
    change (normalizedSyzygyConnecting A m).hom y = 0
    rw [show normalizedSyzygyConnecting A m = 0 from
      normalizedSyzygy_delta_eq_zero ((iteratedNormalizedSyzygy m).obj A) m]
    rfl
  have he := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ)
    (G := normalizedCohomologyStage A) (f := normalizedCohomologyForward A)
    (hij := Nat.le_succ m) (x := y)
  rw [hz, map_zero] at he
  have hi := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ)
    (G := normalizedCohomologyStage A) (f := normalizedCohomologyForward A)
    (hij := le_max_left i d) (x := x)
  exact hi.symm.trans he.symm

end PolycyclicRecognition

end

end OAI
