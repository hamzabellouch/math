import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.Frames

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}}

lemma coefficient_add {M : X.Modules} (e : M ≅ O X) (s t : O X ⟶ M) :
    coefficient e (s + t) = coefficient e s + coefficient e t := by
  simp [coefficient, endValue, Preadditive.add_comp]
  rfl

lemma coefficient_zero {M : X.Modules} (e : M ≅ O X) :
    coefficient e (0 : O X ⟶ M) = 0 := by
  simp [coefficient, endValue]
  rfl

lemma coefficient_sum {M : X.Modules} (e : M ≅ O X) {ι : Type*}
    (s : ι → (O X ⟶ M)) (T : Finset ι) :
    coefficient e (∑ i ∈ T, s i) = ∑ i ∈ T, coefficient e (s i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [coefficient_zero]
  | @insert i T hi ih => simp [Finset.sum_insert, hi, coefficient_add, ih]

lemma restrictSection_add (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    (s t : O X ⟶ M) : restrictSection φ (s + t) = restrictSection φ s + restrictSection φ t := by
  ext U a
  rfl

lemma restrictSection_zero (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules} :
    restrictSection φ (0 : O X ⟶ M) = 0 := by
  ext U value
  rfl

lemma restrictSection_sum (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    {ι : Type*} (s : ι → (O X ⟶ M)) (T : Finset ι) :
    restrictSection φ (∑ i ∈ T, s i) = ∑ i ∈ T, restrictSection φ (s i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [restrictSection_zero]
  | @insert i T hi ih => simp [Finset.sum_insert, hi, restrictSection_add, ih]

lemma coefficient_scalar_comp {M : X.Modules} (e : M ≅ O X)
    (a : Γ(X, ⊤)) (s : O X ⟶ M) :
    coefficient e (scalarEnd a ≫ s) = a * coefficient e s := by
  rw [coefficient, Category.assoc, endValue_comp, endValue_scalarEnd]
  rfl

lemma coefficient_restrict_scalar_comp (φ : Y ⟶ X) [IsOpenImmersion φ]
    {M : X.Modules} (e : M.restrict φ ≅ O Y) (a : Γ(X, ⊤)) (s : O X ⟶ M) :
    coefficient e (restrictSection φ (scalarEnd a ≫ s)) =
      φ.appTop a * coefficient e (restrictSection φ s) := by
  have h : restrictSection φ (scalarEnd a ≫ s) =
      (restrictSection φ (scalarEnd a) ≫ (Scheme.Modules.restrictUnitIso φ).hom) ≫
        restrictSection φ s := by
    let restriction : X.Modules ⥤ Y.Modules := Scheme.Modules.restrictFunctor φ
    let unitIso : restriction.obj (O X) ≅ O Y := Scheme.Modules.restrictUnitIso φ
    change unitIso.inv ≫ restriction.map (scalarEnd a ≫ s) =
      (unitIso.inv ≫ restriction.map (scalarEnd a) ≫ unitIso.hom) ≫
        unitIso.inv ≫ restriction.map s
    simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [h]
  calc
    _ = endValue ((restrictSection φ (scalarEnd a) ≫
        (Scheme.Modules.restrictUnitIso φ).hom) ≫ (restrictSection φ s ≫ e.hom)) :=
      congrArg endValue (Category.assoc _ _ _)
    _ = endValue (restrictSection φ (scalarEnd a) ≫
        (Scheme.Modules.restrictUnitIso φ).hom) * coefficient e (restrictSection φ s) :=
      endValue_comp _ _
    _ = _ := by rw [endValue_restrict, endValue_scalarEnd]

end
end MaximalSeshadri.Frames
end


end
end

end OAI
