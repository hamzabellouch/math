import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorFrames

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
open MaximalSeshadri.Frames
variable {X : Scheme}

def mixedPowMap {M N : X.Modules} :
    ∀ n, (Fin n → (M ⟶ N)) → (modulePow X M n ⟶ modulePow X N n)
  | 0, _ => 𝟙 _
  | n + 1, f => moduleTensorMap (f 0) (mixedPowMap n (fun i => f i.succ))

lemma mixedPowMap_const {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    mixedPowMap n (fun _ => f) = modulePowMap f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change moduleTensorMap f (mixedPowMap n (fun _ => f)) =
      moduleTensorMap f (modulePowMap f n)
    rw [ih]

lemma mixedPowMap_comp {M N P : X.Modules} (n : ℕ)
    (f : Fin n → (M ⟶ N)) (g : Fin n → (N ⟶ P)) :
    mixedPowMap n (fun i => f i ≫ g i) = mixedPowMap n f ≫ mixedPowMap n g := by
  induction n with
  | zero => exact (Category.id_comp _).symm
  | succ n ih =>
    change moduleTensorMap (f 0 ≫ g 0) (mixedPowMap n (fun i => f i.succ ≫ g i.succ)) =
      moduleTensorMap (f 0) (mixedPowMap n (fun i => f i.succ)) ≫
        moduleTensorMap (g 0) (mixedPowMap n (fun i => g i.succ))
    rw [ih, moduleTensorMap_comp]

lemma mixedPowMap_restrict (U : X.Opens) {M N : X.Modules} (n : ℕ)
    (f : Fin n → (M ⟶ N)) :
    (Scheme.Modules.restrictFunctor U.ι).map (mixedPowMap n f) ≫
      (modulePowRestrict U N n).hom =
    (modulePowRestrict U M n).hom ≫
      mixedPowMap n (fun i => (Scheme.Modules.restrictFunctor U.ι).map (f i)) := by
  induction n with
  | zero =>
    change (Scheme.Modules.restrictFunctor U.ι).map (𝟙 (structureSheaf X)) ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom =
      (Scheme.Modules.restrictUnitIso U.ι).hom ≫ 𝟙 (structureSheaf U.toScheme)
    exact (congrArg (fun morphism => morphism ≫ (Scheme.Modules.restrictUnitIso U.ι).hom)
      ((Scheme.Modules.restrictFunctor U.ι).map_id (structureSheaf X))).trans
        ((Category.id_comp _).trans (Category.comp_id _).symm)
  | succ n ih =>
    change (Scheme.Modules.restrictFunctor U.ι).map
        (moduleTensorMap (f 0) (mixedPowMap n (fun i => f i.succ))) ≫
      ((moduleTensorRestrict U N (modulePow X N n)).hom ≫
        (moduleTensorIso (Iso.refl _) (modulePowRestrict U N n)).hom) =
      ((moduleTensorRestrict U M (modulePow X M n)).hom ≫
        (moduleTensorIso (Iso.refl _) (modulePowRestrict U M n)).hom) ≫ _
    simp only [moduleTensorIso_hom, Iso.refl_hom]
    rw [← Category.assoc, moduleTensorRestrict_natural, Category.assoc,
      ← moduleTensorMap_comp, Category.comp_id, ih]
    simp only [mixedPowMap]
    rw [Category.assoc, ← moduleTensorMap_comp, Category.id_comp]

def mixedEnd : ∀ n, (Fin n → (structureSheaf X ⟶ structureSheaf X)) → (structureSheaf X ⟶ structureSheaf X)
  | 0, _ => 𝟙 _
  | n + 1, f => f 0 ≫ mixedEnd n (fun i => f i.succ)

lemma mixedEnd_value (n : ℕ) (f : Fin n → (structureSheaf X ⟶ structureSheaf X)) :
    endValue (mixedEnd n f) = ∏ i, endValue (f i) := by
  induction n with
  | zero => exact (endValue_id (X := X))
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    exact (endValue_comp (f 0) (mixedEnd n (fun i => f i.succ))).trans
      (congrArg (fun value => endValue (f 0) * value) (ih (fun i => f i.succ)))

lemma mixedPowMap_unitPower (n : ℕ) (f : Fin n → (structureSheaf X ⟶ structureSheaf X)) :
    mixedPowMap n f ≫ (unitPowerIso n).hom =
      (unitPowerIso n).hom ≫ mixedEnd n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change moduleTensorMap (f 0) (mixedPowMap n (fun i => f i.succ)) ≫
        ((moduleTensorUnit (modulePow X (structureSheaf X) n)).hom ≫ (unitPowerIso n).hom) =
      ((moduleTensorUnit (modulePow X (structureSheaf X) n)).hom ≫ (unitPowerIso n).hom) ≫
        (f 0 ≫ mixedEnd n (fun i => f i.succ))
    calc
      _ = moduleTensorMap (f 0) (mixedPowMap n (fun i => f i.succ)) ≫
          moduleTensorMap (𝟙 (structureSheaf X)) (unitPowerIso n).hom ≫
            (moduleTensorUnit (structureSheaf X)).hom := by
        rw [moduleTensorUnit_natural]
      _ = moduleTensorMap (f 0) ((unitPowerIso n).hom ≫ mixedEnd n (fun i => f i.succ)) ≫
            (moduleTensorUnit (structureSheaf X)).hom := by
        rw [← Category.assoc, ← moduleTensorMap_comp, Category.comp_id, ih]
      _ = moduleTensorMap (𝟙 (structureSheaf X)) (unitPowerIso n).hom ≫
          moduleTensorMap (f 0) (mixedEnd n (fun i => f i.succ)) ≫
            (moduleTensorUnit (structureSheaf X)).hom := by
        rw [← Category.assoc, ← moduleTensorMap_comp, Category.id_comp]
      _ = (moduleTensorUnit (modulePow X (structureSheaf X) n)).hom ≫
          (unitPowerIso n).hom ≫ (f 0 ≫ mixedEnd n (fun i => f i.succ)) := by
        rw [moduleTensorUnit_scalar, ← Category.assoc, moduleTensorUnit_natural,
          Category.assoc]
      _ = _ := by simp only [Category.assoc]

def mixedPowerSection {M : X.Modules} (n : ℕ) (s : Fin n → (structureSheaf X ⟶ M)) :
    structureSheaf X ⟶ modulePow X M n := (unitPowerIso n).inv ≫ mixedPowMap n s

lemma mixedPowerSection_const {M : X.Modules} (n : ℕ) (s : structureSheaf X ⟶ M) :
    mixedPowerSection n (fun _ => s) = powerSection s n := by
  simp only [mixedPowerSection, powerSection, mixedPowMap_const]

lemma mixedPowerSection_coefficient {M : X.Modules} (e : M ≅ structureSheaf X)
    (n : ℕ) (s : Fin n → (structureSheaf X ⟶ M)) :
    coefficient (globalPowerFrame e n) (mixedPowerSection n s) =
      ∏ i, coefficient e (s i) := by
  have section_power : mixedPowerSection n s ≫ (globalPowerFrame e n).hom =
      mixedEnd n (fun i => s i ≫ e.hom) := by
    change ((unitPowerIso n).inv ≫ mixedPowMap n s) ≫
      (modulePowMap e.hom n ≫ (unitPowerIso n).hom) = _
    rw [Category.assoc, ← mixedPowMap_const, ← Category.assoc (mixedPowMap n s),
      ← mixedPowMap_comp, mixedPowMap_unitPower, Iso.inv_hom_id_assoc]
  exact (congrArg (fun morphism : structureSheaf X ⟶ structureSheaf X =>
    endValue morphism) section_power).trans (mixedEnd_value n (fun i => s i ≫ e.hom))

lemma restrictMixedPowerSection_factor (U : X.Opens) {M : X.Modules}
    (n : ℕ) (s : Fin n → (structureSheaf X ⟶ M)) :
    restrictSection U.ι (mixedPowerSection n s) ≫ (modulePowRestrict U M n).hom =
      (powerRestrictionUnit U n).hom ≫
        mixedPowerSection n (fun i => restrictSection U.ι (s i)) := by
  let restriction : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let unitIso : restriction.obj (structureSheaf X) ≅ structureSheaf U.toScheme :=
    Scheme.Modules.restrictUnitIso U.ι
  change (unitIso.inv ≫ restriction.map ((unitPowerIso n).inv ≫ mixedPowMap n s)) ≫
      (modulePowRestrict U M n).hom =
    (unitIso.inv ≫ restriction.map (unitPowerIso n).inv ≫
      (modulePowRestrict U (structureSheaf X) n).hom ≫
      modulePowMap unitIso.hom n ≫ (unitPowerIso n).hom) ≫
        ((unitPowerIso n).inv ≫
          mixedPowMap n (fun i => unitIso.inv ≫ restriction.map (s i)))
  rw [restriction.map_comp]
  simp only [Category.assoc]
  rw [mixedPowMap_restrict, Iso.hom_inv_id_assoc, ← mixedPowMap_const,
    ← mixedPowMap_comp]
  simp only [Iso.hom_inv_id_assoc]
  rfl

lemma local_mixedPowerSection_coefficient (U : X.Opens) {M : X.Modules}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (n : ℕ) (s : Fin n → (structureSheaf X ⟶ M)) :
    coefficient (localPowerFrame U e n) (restrictSection U.ι (mixedPowerSection n s)) =
      endValue (powerRestrictionUnit U n).hom *
        ∏ i, coefficient e (restrictSection U.ι (s i)) := by
  change coefficient (globalPowerFrame e n)
    (restrictSection U.ι (mixedPowerSection n s) ≫ (modulePowRestrict U M n).hom) = _
  rw [restrictMixedPowerSection_factor]
  exact (coefficient_precompose (globalPowerFrame e n) (powerRestrictionUnit U n).hom
    (mixedPowerSection n (fun i => restrictSection U.ι (s i)))).trans
      (congrArg (fun value => endValue (powerRestrictionUnit U n).hom * value)
        (mixedPowerSection_coefficient e n (fun i => restrictSection U.ι (s i))))

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
