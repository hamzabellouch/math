import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalFiniteCoinvariants
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalCoefficientDimensionBound
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

namespace OAI

/-! # Rational dimension under a finite normal quotient -/
noncomputable section
namespace PolycyclicRecognition.RationalQuotient
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Representation.Coinvariants.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def normalCoinvariantsInflationCounit (B : Rep.{0} ℚ (G ⧸ N)) :
    (Rep.res (QuotientGroup.mk' N) B).quotientToCoinvariants N ⟶ B :=
  Rep.ofHom {
    toLinearMap := Representation.Coinvariants.lift _ LinearMap.id (fun n => by
      apply LinearMap.ext
      intro x
      change B.ρ (QuotientGroup.mk' N (n : G)) x = x
      have hn : QuotientGroup.mk' N (n : G) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr n.property
      rw [hn, map_one]
      rfl)
    isIntertwining' q := by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
      apply LinearMap.ext
      intro x
      induction x using Representation.Coinvariants.induction_on with
      | h x => rfl }

@[simp] theorem normalCoinvariantsInflationCounit_mk (B : Rep.{0} ℚ (G ⧸ N)) (x : B.V) :
    normalCoinvariantsInflationCounit N B
      (Representation.Coinvariants.mk ((Rep.res (QuotientGroup.mk' N) B).ρ.comp N.subtype) x) = x := rfl

def normalCoinvariantsInflationAdjunction :
    Rep.quotientToCoinvariantsFunctor.{0} ℚ N ⊣ Rep.resFunctor (QuotientGroup.mk' N) where
  unit := {
    app A := A.toCoinvariantsMkQ N
    naturality := by intros; ext; rfl }
  counit := {
    app B := normalCoinvariantsInflationCounit N B
    naturality := by
      intro A B f
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      induction x using Representation.Coinvariants.induction_on with
      | h x => rfl }
  left_triangle_components := by
    intro A
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    induction x using Representation.Coinvariants.induction_on with
    | h x => rfl
  right_triangle_components := by intros; ext; rfl

instance normalCoinvariants_preservesProjective :
    (Rep.quotientToCoinvariantsFunctor.{0} ℚ N).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (normalCoinvariantsInflationAdjunction N)


instance quotientCoinvariants_additive :
    (Rep.quotientToCoinvariantsFunctor.{0} ℚ N).Additive where
  map_add := by
    intro X Y f g
    ext x
    induction x using Representation.Coinvariants.induction_on with
    | h x => rfl

instance : (Rep.quotientToCoinvariantsFunctor.{0} ℚ N).IsLeftAdjoint :=
  (normalCoinvariantsInflationAdjunction N).isLeftAdjoint

instance [Finite N] :
    (Rep.quotientToCoinvariantsFunctor.{0} ℚ N).PreservesMonomorphisms where
  preserves f hf := by
    classical
    let : Fintype N := Fintype.ofFinite N
    apply (Rep.mono_iff_injective _).mpr
    exact finiteRationalCoinvariants_map_injective _ _
      ((Rep.resFunctor N.subtype).map f).hom ((Rep.mono_iff_injective f).mp hf)

instance [Finite N] : (Rep.quotientToCoinvariantsFunctor.{0} ℚ N).PreservesHomology := by
  let F := Rep.quotientToCoinvariantsFunctor.{0} ℚ N
  apply (Functor.exact_tfae F).out 1 3 |>.mp
  intro S hS
  have hm : Mono (F.map S.f) := by
    let : Mono S.f := hS.mono_f
    infer_instance
  have he := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi F).mp
    (inferInstance : PreservesFiniteColimits F) S hS
  exact { exact := he.1, mono_f := hm, epi_g := he.2 }

theorem exactFunctor_rational_dimension {K : Type} [Group K]
    (F : Rep.{0} ℚ G ⥤ Rep.{0} ℚ K)
    [F.Additive] [F.PreservesHomology] [F.PreservesMonomorphisms]
    [F.PreservesEpimorphisms] [F.PreservesProjectiveObjects]
    (A : Rep.{0} ℚ G) (d : ℕ) (hd : HasProjectiveDimensionLE A d) :
    HasProjectiveDimensionLE (F.obj A) d := by
  induction d generalizing A with
  | zero =>
    exact (projective_iff_hasProjectiveDimensionLE_zero _).mp
      (F.projective_obj_of_projective ((projective_iff_hasProjectiveDimensionLE_zero A).mpr hd))
  | succ d ih =>
    let p := Projective.π A
    let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel S (kernelIsKernel p) }
    have hk : HasProjectiveDimensionLE (kernel p) d :=
      hS.hasProjectiveDimensionLT_X₁ (d + 1)
        (hasProjectiveDimensionLT_of_ge (Projective.over A) 1 (d + 1) (by omega)) hd
    have hki := ih (kernel p) hk
    let : Mono S.f := hS.mono_f
    let : Epi S.g := hS.epi_g
    let : Projective (F.obj (Projective.over A)) :=
      F.projective_obj_of_projective (inferInstance : Projective (Projective.over A))
    exact (hS.map F).hasProjectiveDimensionLT_X₃ (d + 1) hki
      (hasProjectiveDimensionLT_of_ge (F.obj (Projective.over A)) 1 (d + 2) (by omega))

def trivialCoinvariantsIso :
    (Rep.trivial ℚ G ℚ).quotientToCoinvariants N ≅ Rep.trivial ℚ (G ⧸ N) ℚ := by
  let e : (Rep.trivial ℚ G ℚ).quotientToCoinvariants N ⟶
      Rep.trivial ℚ (G ⧸ N) ℚ :=
    normalCoinvariantsInflationCounit N (Rep.trivial ℚ (G ⧸ N) ℚ)
  let : Mono e := by
    apply (Rep.mono_iff_injective e).mpr
    intro x y hxy
    induction x using Representation.Coinvariants.induction_on with
    | h x =>
      induction y using Representation.Coinvariants.induction_on with
      | h y => exact congrArg (Representation.Coinvariants.mk _) hxy
  let : Epi e := by
    apply (Rep.epi_iff_surjective e).mpr
    intro q
    exact ⟨Representation.Coinvariants.mk _ q, rfl⟩
  let : IsIso e := isIso_of_mono_of_epi e
  exact asIso e

theorem rational_dimension_quotient [Finite N] (d : ℕ)
    (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d) :
    HasProjectiveDimensionLE (Rep.trivial ℚ (G ⧸ N) ℚ) d := by
  let : HasProjectiveDimensionLE ((Rep.trivial ℚ G ℚ).quotientToCoinvariants N) d :=
    exactFunctor_rational_dimension (Rep.quotientToCoinvariantsFunctor.{0} ℚ N)
    (Rep.trivial ℚ G ℚ) d hd
  exact hasProjectiveDimensionLT_of_iso (trivialCoinvariantsIso N) (d + 1)


theorem rational_dimension_subgroup (H : Subgroup G) (d : ℕ)
    (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d) :
    HasProjectiveDimensionLE (Rep.trivial ℚ H ℚ) d :=
  exactFunctor_rational_dimension (Rep.resFunctor H.subtype) (Rep.trivial ℚ G ℚ) d hd

end PolycyclicRecognition.RationalQuotient

end

end OAI
