import OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer
import OAI.NumberTheory.PiExponent.Cohomology.EulerExact

namespace OAI

namespace PiExponent.ClosedImmersionSerreTransfer

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite PiExponentSeshadri.Geometry

variable {X Y : Scheme.{0}} (f : X ⟶ Y)
local instance closedPushforwardLinearSourceHasExt : HasExt.{1} X.Modules := schemeHasExt
local instance closedPushforwardLinearTargetHasExt : HasExt.{1} Y.Modules := schemeHasExt

lemma baseScalars_comp_actual (p : Y ⟶ Spec (CommRingCat.of ℂ)) :
    baseScalars (f ≫ p) = f.appTop.hom.comp (baseScalars p) := by
  ext c
  simp only [baseScalars, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]

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
  let y : Γ(N, f ⁻¹ᵁ U) := g.val.app (op (f ⁻¹ᵁ U)) m
  change restrictScalar X (f ⁻¹ᵁ U) (baseScalars (f ≫ p) r) • y =
    f.app U (restrictScalar Y U (baseScalars p r)) • y
  rw [scalar_naturality]

variable [IsClosedImmersion f]

lemma cohomologyMap_comp {M N : X.Modules} {n m k : ℕ}
    (x : cohomology M n) (y : Ext.{1} M N m) (h : n + m = k) :
    cohomologyMap f N k (x.comp y h) =
      (cohomologyMap f M n x).comp (y.mapExactFunctor (Scheme.Modules.pushforward f)) h :=
  PiExponentSeshadri.ExtSectionComparison.mapFrom_comp
    (Scheme.Modules.pushforward f) (structureMap f) x y h

def typedCohomologyMap (M : X.Modules) (n : ℕ) :
    cohomology M n →+ cohomology ((Scheme.Modules.pushforward f).obj M) n :=
  cohomologyMap f M n

lemma typedCohomologyMap_comp {M N : X.Modules} {n m k : ℕ}
    (x : cohomology M n) (y : Ext.{1} M N m) (h : n + m = k) :
    typedCohomologyMap f N k (x.comp y h) =
      (typedCohomologyMap f M n x).comp
        (y.mapExactFunctor (Scheme.Modules.pushforward f)) h :=
  cohomologyMap_comp f x y h

lemma typedCohomologyMap_bijective (M : X.Modules) (n : ℕ) :
    Function.Bijective (typedCohomologyMap f M n) :=
  cohomologyMap_bijective f M n

def cohomologyLinearMap (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    letI := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
    cohomology M n →ₗ[ℂ] cohomology ((Scheme.Modules.pushforward f).obj M) n := by
  letI := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
  letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
  exact { toFun := typedCohomologyMap f M n
          map_add' := (typedCohomologyMap f M n).map_add
          map_smul' := by
            intro r x
            change typedCohomologyMap f M n ((baseScalars (f ≫ p) r) • x) =
              (baseScalars p r) • (typedCohomologyMap f M n x)
            rw [Ext.smul_eq_comp_mk₀, typedCohomologyMap_comp, Ext.smul_eq_comp_mk₀,
              Ext.mapExactFunctor_mk₀]
            congr 2
            ext U m
            change Γ(M, f ⁻¹ᵁ U) at m
            change restrictScalar X (f ⁻¹ᵁ U) (baseScalars (f ≫ p) r) • m =
              f.app U (restrictScalar Y U (baseScalars p r)) • m
            rw [scalar_naturality] }

lemma cohomologyLinearMap_eq (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    ⇑(cohomologyLinearMap f p M n) = typedCohomologyMap f M n := rfl

def cohomologyLinearEquiv (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    letI := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
    cohomology M n ≃ₗ[ℂ] cohomology ((Scheme.Modules.pushforward f).obj M) n := by
  exact LinearEquiv.ofBijective (cohomologyLinearMap f p M n)
    (by rw [cohomologyLinearMap_eq]; exact typedCohomologyMap_bijective f M n)

theorem finiteDimensional_of_pushforward
    (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ)
    (hfinite : letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
      FiniteDimensional ℂ (cohomology ((Scheme.Modules.pushforward f).obj M) n)) :
    letI := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
    FiniteDimensional ℂ (cohomology M n) := by
  let := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
  have := hfinite
  exact FiniteDimensional.of_injective (cohomologyLinearEquiv f p M n).toLinearMap
    (cohomologyLinearEquiv f p M n).injective

lemma cohomologyDimension_pushforward
    (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    cohomologyDimension p ((Scheme.Modules.pushforward f).obj M) n =
      cohomologyDimension (f ≫ p) M n := by
  let := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
  exact (cohomologyLinearEquiv f p M n).finrank_eq.symm

theorem euler_pushforward (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (d : ℕ) :
    eulerCharacteristic p d ((Scheme.Modules.pushforward f).obj M) =
      eulerCharacteristic (f ≫ p) d M := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [cohomologyDimension_pushforward]

end
end PiExponent.ClosedImmersionSerreTransfer

end OAI
