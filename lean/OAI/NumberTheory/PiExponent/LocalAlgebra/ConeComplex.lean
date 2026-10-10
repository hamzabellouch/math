import Mathlib.Algebra.Homology.HomologicalComplex
import OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution

namespace OAI

namespace PiExponentSiegelAux.W30
open CategoryTheory

universe u
variable {R : Type u} [CommRing R]

lemma coneBottom_comp {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup Z] [Module R X] [Module R Y] [Module R Z]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R) (hgf : g.comp f = 0) :
    (coneBottom g r).comp (coneDifferential f g r) = 0 := by
  apply LinearMap.ext
  intro xy
  have hz : g (f xy.1) = 0 := LinearMap.congr_fun hgf xy.1
  change g (f xy.1 + r • xy.2) + r • (-g xy.2) = 0
  simp [map_add, map_smul, hz]

def scalarConeObject (C : ChainComplex (ModuleCat.{u} R) ℕ) : ℕ → ModuleCat.{u} R
  | 0 => C.X 0
  | n + 1 => ModuleCat.of R (C.X (n + 1) × C.X n)

def scalarConeMap (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) :
    ∀ n, scalarConeObject C (n + 1) ⟶ scalarConeObject C n
  | 0 => ModuleCat.ofHom (coneBottom (C.d 1 0).hom r)
  | n + 1 => ModuleCat.ofHom
      (coneDifferential (C.d (n + 2) (n + 1)).hom (C.d (n + 1) n).hom r)

lemma chain_linear_comp_zero (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (C.d (n + 1) n).hom.comp (C.d (n + 2) (n + 1)).hom = 0 := by
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero] using
    congrArg (fun f => f.hom) (C.d_comp_d (n + 2) (n + 1) n)

theorem scalarConeMap_comp (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (n : ℕ) :
    scalarConeMap C r (n + 1) ≫ scalarConeMap C r n = 0 := by
  cases n with
  | zero =>
    apply ModuleCat.hom_ext
    exact coneBottom_comp _ _ r (chain_linear_comp_zero C 0)
  | succ n =>
    apply ModuleCat.hom_ext
    exact coneDifferential_comp _ _ _ r
      (chain_linear_comp_zero C (n + 1)) (chain_linear_comp_zero C n)

def scalarConeComplex (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (scalarConeObject C) (scalarConeMap C r) (scalarConeMap_comp C r)

theorem scalarCone_interior_exact (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (n : ℕ)
    (hnext : LinearMap.range (C.d (n + 3) (n + 2)).hom =
      LinearMap.ker (C.d (n + 2) (n + 1)).hom)
    (hprev : LinearMap.range (C.d (n + 2) (n + 1)).hom =
      LinearMap.ker (C.d (n + 1) n).hom) :
    LinearMap.range (scalarConeMap C r (n + 2)).hom =
      LinearMap.ker (scalarConeMap C r (n + 1)).hom :=
  coneDifferential_exact _ _ _ r hnext hprev

end PiExponentSiegelAux.W30

end OAI
