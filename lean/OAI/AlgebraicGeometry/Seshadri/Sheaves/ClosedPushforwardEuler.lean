import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.LocalSectionDegree
import OAI.AlgebraicGeometry.Seshadri.Cohomology.ClosedPushforwardCohomology

namespace OAI


                                                
section

namespace MaximalSeshadri.ClosedPushforward
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.FlasqueCohomology MaximalSeshadri.Frames

variable {X Y : Scheme.{0}} (f : X ⟶ Y)
local instance : HasExt.{1} X.Modules := schemeHasExt
local instance : HasExt.{1} Y.Modules := schemeHasExt

lemma scalar_naturality (p : Y ⟶ Spec (CommRingCat.of ℂ)) (U : Y.Opens) (r : ℂ) :
    restrictScalar X (f ⁻¹ᵁ U) (baseScalars (f ≫ p) r) =
      f.app U (restrictScalar Y U (baseScalars p r)) := by
  rw [baseScalars_comp_actual]
  change X.presheaf.map (homOfLE le_top).op (f.appTop (baseScalars p r)) = _
  exact (CategoryTheory.congr_fun (f.naturality (homOfLE le_top).op) (baseScalars p r)).symm

theorem complexLinearPushforward (p : Y ⟶ Spec (CommRingCat.of ℂ)) :
    letI := sheafComplexLinear (f ≫ p)
    letI := sheafComplexLinear p
    (Scheme.Modules.pushforward f).Linear ℂ := by
  let := sheafComplexLinear (f ≫ p)
  let := sheafComplexLinear p
  constructor
  intro M N g r
  ext U m
  change Γ(M, f ⁻¹ᵁ U) at m
  change restrictScalar X (f ⁻¹ᵁ U) (baseScalars (f ≫ p) r) • g.app (f ⁻¹ᵁ U) m =
    f.app U (restrictScalar Y U (baseScalars p r)) • g.app (f ⁻¹ᵁ U) m
  rw [scalar_naturality]

variable [IsClosedImmersion f]

lemma cohomologyMap_base_smul (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ)
    (r : ℂ) (x : Ext.{1} (O X) M n) :
    cohomologyMap f M n ((baseScalars (f ≫ p) r) • x) =
      (baseScalars p r) • cohomologyMap f M n x := by
  rw [Ext.smul_eq_comp_mk₀, cohomologyMap_comp, Ext.smul_eq_comp_mk₀,
    Ext.mapExactFunctor_mk₀]
  congr 2
  ext U m
  change Γ(M, f ⁻¹ᵁ U) at m
  change restrictScalar X (f ⁻¹ᵁ U) (baseScalars (f ≫ p) r) • m =
    f.app U (restrictScalar Y U (baseScalars p r)) • m
  rw [scalar_naturality]

def cohomologyLinearMap (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    letI := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
    cohomology M n →ₗ[ℂ] cohomology ((Scheme.Modules.pushforward f).obj M) n := by
  letI := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
  letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
  exact { toFun := cohomologyMap f M n
          map_add' := (cohomologyMap f M n).map_add
          map_smul' := by
            intro r x
            exact cohomologyMap_base_smul f p M n r x }

lemma cohomologyLinearMap_eq (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    ⇑(cohomologyLinearMap f p M n) = cohomologyMap f M n := rfl

def cohomologyEquiv (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    letI := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
    cohomology M n ≃ₗ[ℂ] cohomology ((Scheme.Modules.pushforward f).obj M) n := by
  exact LinearEquiv.ofBijective (cohomologyLinearMap f p M n)
    (by rw [cohomologyLinearMap_eq]; exact cohomologyMap_bijective f M n)

theorem euler_pushforward (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (d : ℕ) :
    eulerCharacteristic p d ((Scheme.Modules.pushforward f).obj M) =
      eulerCharacteristic (f ≫ p) d M := by
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  let := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
  exact (cohomologyEquiv f p M n).finrank_eq.symm

end
end MaximalSeshadri.ClosedPushforward

end

end OAI
