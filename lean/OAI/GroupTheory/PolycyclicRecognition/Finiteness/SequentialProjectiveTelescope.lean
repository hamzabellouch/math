import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepresentationDirectSum
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequentialRepresentationDescent
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepCofiber

namespace OAI

/-! # A length-one projective resolution of a sequential projective colimit

The differential is identity minus the forward shift. Its injectivity uses
induction on coordinates, and the cokernel is the given concrete colimit.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule
variable {G : Type} [Group G]
namespace SequentialRepresentationDiagram
variable (D : SequentialRepresentationDiagram G)

abbrev telescopeSum := integralRepresentationSum D.obj

def telescopeShift : D.telescopeSum ⟶ D.telescopeSum :=
  integralRepresentationSumDesc D.obj D.telescopeSum
    (fun i => D.map i (i + 1) (Nat.le_succ i) ≫ integralRepresentationSumInclusion D.obj (i + 1))

def telescopeDifferential : D.telescopeSum ⟶ D.telescopeSum := 𝟙 _ - D.telescopeShift

@[simp]
theorem telescopeShift_inclusion (i : ℕ) (x : D.obj i) :
    D.telescopeShift.hom ((integralRepresentationSumInclusion D.obj i).hom x) =
      (integralRepresentationSumInclusion D.obj (i + 1)).hom
        ((D.map i (i + 1) (Nat.le_succ i)).hom x) := by
  exact ConcreteCategory.congr_hom (integralRepresentationSumInclusion_desc D.obj
    D.telescopeSum (fun i => D.map i (i + 1) (Nat.le_succ i) ≫
      integralRepresentationSumInclusion D.obj (i + 1)) i) x

@[simp]
theorem telescopeShift_zero (x : D.telescopeSum) : D.telescopeShift.hom x 0 = 0 := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add]
    change ((D.telescopeShift.hom x) 0 + (D.telescopeShift.hom y) 0) = 0
    rw [hx, hy, add_zero]
  | of i x =>
    rw [← integralRepresentationSumInclusion_apply D.obj i x]
    rw [telescopeShift_inclusion]
    exact integralRepresentationSumInclusion_ne D.obj (i + 1) 0 (by omega) _

@[simp]
theorem telescopeShift_succ (x : D.telescopeSum) (i : ℕ) :
    D.telescopeShift.hom x (i + 1) = (D.map i (i + 1) (Nat.le_succ i)).hom (x i) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add]
    change (D.telescopeShift.hom x) (i + 1) + (D.telescopeShift.hom y) (i + 1) =
      (D.map i (i + 1) (Nat.le_succ i)).hom (x i + y i)
    rw [hx, hy, map_add]
  | of j x =>
    rw [← integralRepresentationSumInclusion_apply D.obj j x]
    rw [telescopeShift_inclusion]
    by_cases h : j = i
    · subst j
      rw [integralRepresentationSumInclusion_same, integralRepresentationSumInclusion_same]
    · have h' : j + 1 ≠ i + 1 := by omega
      rw [integralRepresentationSumInclusion_ne D.obj (j + 1) (i + 1) h',
        integralRepresentationSumInclusion_ne D.obj j i h, map_zero]

theorem telescopeDifferential_injective : Function.Injective D.telescopeDifferential.hom := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  change DirectSum ℕ (fun i => (D.obj i).V) at x
  have hc (i : ℕ) : x i = 0 := by
    induction i with
    | zero =>
      have h := congrArg (fun y : D.telescopeSum => y 0) hx
      change x 0 - (D.telescopeShift.hom x) 0 = 0 at h
      rw [telescopeShift_zero D x, sub_zero] at h
      exact h
    | succ i hi =>
      have h := congrArg (fun y : D.telescopeSum => y (i + 1)) hx
      change x (i + 1) - (D.telescopeShift.hom x) (i + 1) = 0 at h
      rw [telescopeShift_succ D x i, hi, map_zero, sub_zero] at h
      exact h
  exact DFinsupp.ext hc

namespace ColimitCocone
variable {D} {A : Rep.{0} ℤ G} (c : D.ColimitCocone A)

def telescopeAugmentation : D.telescopeSum ⟶ A :=
  integralRepresentationSumDesc D.obj A c.ι

theorem telescopeDifferential_augmentation :
    D.telescopeDifferential ≫ c.telescopeAugmentation = 0 := by
  apply integralRepresentationSum_hom_ext
  intro i
  simp only [telescopeDifferential, Preadditive.comp_sub, Preadditive.sub_comp,
    Category.id_comp, Category.assoc, telescopeShift, telescopeAugmentation,
    integralRepresentationSumInclusion_desc_assoc, integralRepresentationSumInclusion_desc,
    c.comm, sub_self, comp_zero]

instance telescopeAugmentation_epi : Epi c.telescopeAugmentation := by
  apply (Rep.epi_iff_surjective _).mpr
  intro a
  obtain ⟨i, x, rfl⟩ := c.surj a
  exact ⟨(integralRepresentationSumInclusion D.obj i).hom x,
    ConcreteCategory.congr_hom (integralRepresentationSumInclusion_desc _ _ _ i) x⟩


def telescopeSequence : ShortComplex (Rep.{0} ℤ G) :=
  ShortComplex.mk D.telescopeDifferential c.telescopeAugmentation
    c.telescopeDifferential_augmentation

theorem telescopeCokernelCompatible (i j : ℕ) (h : i ≤ j) :
    D.map i j h ≫ integralRepresentationSumInclusion D.obj j ≫
        cokernel.π D.telescopeDifferential =
      integralRepresentationSumInclusion D.obj i ≫ cokernel.π D.telescopeDifferential := by
  induction h with
  | refl => rw [D.map_id, Category.id_comp]
  | @step j h ih =>
    have he : (integralRepresentationSumInclusion D.obj j -
        D.map j (j + 1) (Nat.le_succ j) ≫
          integralRepresentationSumInclusion D.obj (j + 1)) ≫
            cokernel.π D.telescopeDifferential = 0 := by
      have hz : (integralRepresentationSumInclusion D.obj j ≫ D.telescopeDifferential) ≫
          cokernel.π D.telescopeDifferential = 0 := by
        rw [Category.assoc, cokernel.condition, comp_zero]
      simpa only [← Category.assoc, telescopeDifferential, Preadditive.comp_sub,
        Category.comp_id, telescopeShift, integralRepresentationSumInclusion_desc,
        Preadditive.sub_comp] using hz
    have hj : D.map j (j + 1) (Nat.le_succ j) ≫
        integralRepresentationSumInclusion D.obj (j + 1) ≫
          cokernel.π D.telescopeDifferential =
        integralRepresentationSumInclusion D.obj j ≫ cokernel.π D.telescopeDifferential := by
      rw [Preadditive.sub_comp, sub_eq_zero] at he
      exact he.symm
    rw [← D.map_comp i j (j + 1) h (Nat.le_succ j), Category.assoc, hj]
    exact ih

def telescopeCokernelDescent : A ⟶ cokernel D.telescopeDifferential :=
  c.desc _ (fun i => integralRepresentationSumInclusion D.obj i ≫
    cokernel.π D.telescopeDifferential) (telescopeCokernelCompatible (D := D))

theorem telescopeAugmentation_cokernelDescent :
    c.telescopeAugmentation ≫ c.telescopeCokernelDescent =
      cokernel.π D.telescopeDifferential := by
  apply integralRepresentationSum_hom_ext
  intro i
  rw [← Category.assoc]
  change (integralRepresentationSumInclusion D.obj i ≫
    integralRepresentationSumDesc D.obj A c.ι) ≫ c.telescopeCokernelDescent = _
  rw [integralRepresentationSumInclusion_desc]
  exact c.ι_desc _ _ _ i

theorem telescopeSequence_shortExact : c.telescopeSequence.ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (rep_shortComplex_exact_iff _).mpr
    intro x hx
    change D.telescopeSum at x
    change c.telescopeAugmentation.hom x = 0 at hx
    have hz : (cokernel.π D.telescopeDifferential).hom x = 0 := by
      rw [← c.telescopeAugmentation_cokernelDescent]
      change c.telescopeCokernelDescent.hom (c.telescopeAugmentation.hom x) = 0
      rw [hx, map_zero]
    exact (rep_shortComplex_exact_iff _).mp
      (ShortComplex.exact_cokernel D.telescopeDifferential) x hz
  · exact (Rep.mono_iff_injective _).mpr D.telescopeDifferential_injective
  · exact inferInstanceAs (Epi c.telescopeAugmentation)

include c in
theorem projectiveDimension_le_one [∀ i, Projective (D.obj i)] :
    HasProjectiveDimensionLE A 1 :=
  (telescopeSequence_shortExact c).hasProjectiveDimensionLT_X₃ 1
    (inferInstance : HasProjectiveDimensionLT D.telescopeSum 1)
    (hasProjectiveDimensionLT_of_ge D.telescopeSum 1 2 (by omega))

end ColimitCocone
end SequentialRepresentationDiagram
end PolycyclicRecognition

end

end OAI
