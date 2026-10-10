import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Model

namespace OAI

section
section
noncomputable section
open CategoryTheory

namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]

section ProjectiveTransport
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughProjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [EnoughProjectives D]
open CategoryTheory.Limits

omit [EnoughProjectives D] in
lemma hasProjectiveDimensionLT_of_fullyFaithful
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Full] [F.Faithful] [F.PreservesProjectiveObjects]
    (X : C) (n : ℕ) [HasProjectiveDimensionLT (F.obj X) n] :
    HasProjectiveDimensionLT X n := by
  let := HasExt.standard C
  let := HasExt.standard D
  apply HasProjectiveDimensionLT.mk
  intro i hi Y e
  apply (F.mapExt_bijective_of_preservesProjectiveObjects X Y i).injective
  rw [map_zero]
  exact (F.mapExtAddHom X Y i e).eq_zero_of_hasProjectiveDimensionLT n hi

omit [EnoughProjectives D] in
lemma hasProjectiveDimensionLT_map
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesProjectiveObjects] (X : C) (n : ℕ) [HasProjectiveDimensionLT X n] :
    HasProjectiveDimensionLT (F.obj X) n := by
  induction n generalizing X with
  | zero =>
    exact (F.map_isZero (isZero_of_hasProjectiveDimensionLT_zero X)).hasProjectiveDimensionLT_zero
  | succ n ih =>
    cases n with
    | zero =>
      let : Projective X := projective_iff_hasProjectiveDimensionLT_one.mpr (by assumption)
      exact inferInstance
    | succ n =>
      let S := ShortComplex.mk (kernel.ι (Projective.π X)) (Projective.π X)
        (kernel.condition (Projective.π X))
      have hs : S.ShortExact := { exact := ShortComplex.exact_kernel (Projective.π X) }
      have hk : HasProjectiveDimensionLT S.X₁ (n + 1) :=
        (hs.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp inferInstance
      let := hk
      exact (hs.map_of_exact F).hasProjectiveDimensionLT_X₃ (n + 1)
        (ih S.X₁) (by
          change HasProjectiveDimensionLT (F.obj (Projective.over X)) (n + 1 + 1)
          exact hasProjectiveDimensionLT_of_ge _ 1 _ (by omega))

omit [EnoughProjectives D] in
lemma projectiveDimension_fullyFaithful
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesProjectiveObjects] [F.Full] [F.Faithful] (X : C) :
    projectiveDimension (F.obj X) = projectiveDimension X := by
  have h (n : ℕ) : HasProjectiveDimensionLT (F.obj X) n ↔ HasProjectiveDimensionLT X n :=
    ⟨fun h => @hasProjectiveDimensionLT_of_fullyFaithful _ _ _ _ _ _ _ F _ _ _ _ _ _ X n h,
      fun h => @hasProjectiveDimensionLT_map _ _ _ _ _ _ _ F _ _ _ _ X n h⟩
  simp only [projectiveDimension, h]

lemma hasProjectiveDimensionLT_equivalence_iff (e : C ≌ D) (X : C) (n : ℕ) :
    HasProjectiveDimensionLT (e.functor.obj X) n ↔ HasProjectiveDimensionLT X n := by
  let : e.functor.Additive := e.functor.additive_of_preserves_binary_products
  let : e.inverse.Additive := e.inverse.additive_of_preserves_binary_products
  constructor
  · intro h
    let : HasProjectiveDimensionLT (e.functor.obj X) n := h
    exact hasProjectiveDimensionLT_of_fullyFaithful e.functor X n
  · intro h
    let : HasProjectiveDimensionLT X n := h
    let : HasProjectiveDimensionLT (e.inverse.obj (e.functor.obj X)) n :=
      hasProjectiveDimensionLT_of_iso (show X ≅ e.inverse.obj (e.functor.obj X) from
        e.unitIso.app X) n
    exact hasProjectiveDimensionLT_of_fullyFaithful e.inverse (e.functor.obj X) n

lemma projectiveDimension_equivalence (e : C ≌ D) (X : C) :
    projectiveDimension (e.functor.obj X) = projectiveDimension X := by
  simp only [projectiveDimension, hasProjectiveDimensionLT_equivalence_iff e X]

end ProjectiveTransport

end LittleFinitistic
end
end
end

end OAI
