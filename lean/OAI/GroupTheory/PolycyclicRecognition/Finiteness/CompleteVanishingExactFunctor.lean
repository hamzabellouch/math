import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompleteCohomologyFiniteResolution
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SubgroupInductionDimension

namespace OAI

/-! # Finite-dimensional resolutions after an exact coefficient functor

Only the images of countable free covers must have vanishing completion.
The terminal projective is handled by its actual retract of a free cover.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G Q : Type} [Group G] [Group Q]

instance normalizedFreeRepresentation_countable [Countable Q]
    (A : Rep.{0} ℤ Q) [Countable A] : Countable (normalizedFreeRepresentation A) := by
  change Countable ({a : A // a ≠ 0} →₀ ℤ[Q])
  infer_instance

instance normalizedSyzygy_countable [Countable Q]
    (A : Rep.{0} ℤ Q) [Countable A] : Countable (normalizedSyzygy A) :=
  Function.Injective.countable (f := (kernel.ι (normalizedFreeAugmentation A)).hom)
    ((Rep.mono_iff_injective _).mp inferInstance)

theorem shiftedCompleteCohomology_subsingleton_of_retract
    (p : ℕ) {A B : Rep.{0} ℤ G} (r : Retract A B)
    (hB : Subsingleton (ShiftedCompletedCohomology p B)) :
    Subsingleton (ShiftedCompletedCohomology p A) := by
  let F := shiftedCompletedCohomologyFunctor (G := G) p
  have hr : F.map r.i ≫ F.map r.r = 𝟙 (F.obj A) := by
    rw [← F.map_comp, r.retract, F.map_id]
  apply subsingleton_of_forall_eq (0 : ShiftedCompletedCohomology p A)
  intro x
  have hx := ConcreteCategory.congr_hom hr x
  change (F.map r.r) ((F.map r.i) x) = x at hx
  rw [hB.elim ((F.map r.i) x) 0] at hx
  exact hx.symm.trans (map_zero (F.map r.r).hom)

variable (F : Rep.{0} ℤ Q ⥤ Rep.{0} ℤ G) [F.Additive]
variable [F.PreservesHomology] [F.PreservesMonomorphisms] [F.PreservesEpimorphisms]

/-- A finite projective-dimensional coefficient can be used without choosing
finitely generated projectives, provided its countable free covers vanish. -/
theorem exactFunctor_complete_vanishing_of_finite_dimension [Countable Q]
    (hfree : ∀ (B : Rep.{0} ℤ Q) [Countable B] (p : ℕ),
      Subsingleton (ShiftedCompletedCohomology p (F.obj (normalizedFreeRepresentation B))))
    (A : Rep.{0} ℤ Q) [Countable A] (d : ℕ)
    (hd : HasProjectiveDimensionLE A d) (p : ℕ) :
    Subsingleton (ShiftedCompletedCohomology p (F.obj A)) := by
  induction d generalizing A p with
  | zero =>
    let : Projective A := (projective_iff_hasProjectiveDimensionLE_zero A).mpr hd
    let r : Retract A (normalizedFreeRepresentation A) :=
      ⟨Projective.factorThru (𝟙 A) (normalizedFreeAugmentation A),
        normalizedFreeAugmentation A, Projective.factorThru_comp _ _⟩
    apply shiftedCompleteCohomology_subsingleton_of_retract p (r.map F)
    exact hfree A p
  | succ d ih =>
    let S := normalizedSyzygySequence A
    have hS := normalizedSyzygySequence_shortExact A
    have hk : HasProjectiveDimensionLE (normalizedSyzygy A) d :=
      hS.hasProjectiveDimensionLT_X₁ (d + 1)
        (hasProjectiveDimensionLT_of_ge (normalizedFreeRepresentation A) 1 (d + 1) (by omega)) hd
    let : Mono S.f := hS.mono_f
    let : Epi S.g := hS.epi_g
    exact shiftedCompleteCohomology_vanishing_of_shortExact p (S.map F) (hS.map F)
      (ih (normalizedSyzygy A) hk (p + 1)) (hfree A p)

end PolycyclicRecognition

end

end OAI
