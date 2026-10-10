import OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite
import OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite

namespace OAI

namespace PiExponent.GeometrySupport.ActualLaurentExtFinite
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} {ι K : Type} [Fintype ι] [Field K]
variable {U : ι → X.Opens} {M : X.Modules} {d : ℤ}
variable (ρ : K →+* Γ(X,⊤)) (P : ProjectiveTwistCech.LaurentCechPresentation (K := K) U M d)
private abbrev schemeFreeOpen (V : X.Opens) : X.Modules :=
  PiExponentSeshadri.ModuleFlasque.freeOpen X.ringCatSheaf V

@[instance_reducible] private def freeOpenHomAddCommGroup (V : X.Opens) (N : X.Modules) :
    AddCommGroup (PiExponentSeshadri.ModuleFlasque.freeOpen X.ringCatSheaf V ⟶ N) :=
  inferInstanceAs (AddCommGroup (schemeFreeOpen V ⟶ N))

attribute [local instance] freeOpenHomAddCommGroup

local instance (V : X.Opens) (N : X.Modules) :
    Module Γ(X,⊤) (PiExponentSeshadri.ModuleFlasque.freeOpen X.ringCatSheaf V ⟶ N) :=
  sheafHomModule X _ N
variable (hlinear : ∀ q t (r : K) b,
  P.coefficient q t ((ρ r) • b) = r • P.coefficient q t b)
include P hlinear

theorem actualExt_zero_finite (hcover : ⊤ ≤ ⨆ i, U i) :
    Module.Finite K (CechExtFinite.ActualExt ρ (structureSheaf X) M 0) := by
  let := LaurentCechFinite.degreeZero_finite ρ P hlinear
  let F := CechExtFinite.zeroComparison U ρ M ⊤ (fun _ => le_top) hcover
  let e := CechExtFinite.sourceIso (X := X) ρ
    (A := schemeFreeOpen ⊤) (B := structureSheaf X)
    (PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf) M 0
  exact Module.Finite.of_surjective (e.toLinearMap.comp F)
    (e.surjective.comp (CechExtFinite.zeroComparison_surjective U ρ M ⊤
      (fun _ => le_top) hcover))

theorem actualExt_succ_finite [IsNoetherian X] [M.IsQuasicoherent]
    (hcover : ⊤ ≤ ⨆ i, U i)
    (haffine : ∀ (q : ℕ) (t : Fin (q+1) → ι),
      IsAffineOpen (CechHigher.intersection U t)) (q : ℕ) :
    Module.Finite K (CechExtFinite.ActualExt ρ (structureSheaf X) M (q+1)) := by
  obtain ⟨F, hF, hboundary⟩ :=
    CechExtFinite.affine_exists_comparison U ρ hcover M haffine q
  exact LaurentCechFinite.finite_of_comparison ρ P hlinear q F hboundary hF

theorem actualExt_finite [IsNoetherian X] [M.IsQuasicoherent]
    (hcover : ⊤ ≤ ⨆ i, U i)
    (haffine : ∀ (q : ℕ) (t : Fin (q+1) → ι),
      IsAffineOpen (CechHigher.intersection U t)) (q : ℕ) :
    Module.Finite K (CechExtFinite.ActualExt ρ (structureSheaf X) M q) := by
  cases q with
  | zero => exact actualExt_zero_finite ρ P hlinear hcover
  | succ q => exact actualExt_succ_finite ρ P hlinear hcover haffine q

theorem cohomology_finite [IsNoetherian X] [M.IsQuasicoherent]
    (hcover : ⊤ ≤ ⨆ i, U i)
    (haffine : ∀ (q : ℕ) (t : Fin (q+1) → ι),
      IsAffineOpen (CechHigher.intersection U t)) (q : ℕ) :
    letI := Module.compHom (cohomology M q) ρ
    Module.Finite K (cohomology M q) := by
  exact actualExt_finite ρ P hlinear hcover haffine q

end
end PiExponent.GeometrySupport.ActualLaurentExtFinite

end OAI
