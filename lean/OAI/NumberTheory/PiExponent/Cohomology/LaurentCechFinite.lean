import OAI.NumberTheory.PiExponent.Cohomology.CechLinear
import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology
import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech

namespace OAI

namespace PiExponent.GeometrySupport.LaurentCechFinite
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open ProjectiveTwistCech

variable {X : Scheme.{0}} {ι K : Type} [Fintype ι] [Field K]
  {U : ι → X.Opens} {M : X.Modules} {d : ℤ}

private abbrev schemeFreeOpen (V : X.Opens) : X.Modules :=
  PiExponentSeshadri.ModuleFlasque.freeOpen X.ringCatSheaf V

@[instance_reducible] private def freeOpenHomAddCommGroup (V : X.Opens) (N : X.Modules) :
    AddCommGroup (PiExponentSeshadri.ModuleFlasque.freeOpen X.ringCatSheaf V ⟶ N) :=
  inferInstanceAs (AddCommGroup (schemeFreeOpen V ⟶ N))

attribute [local instance] freeOpenHomAddCommGroup

local instance (V : X.Opens) (N : X.Modules) :
    Module Γ(X, ⊤) (PiExponentSeshadri.ModuleFlasque.freeOpen X.ringCatSheaf V ⟶ N) :=
  sheafHomModule X _ N

variable (ρ : K →+* Γ(X, ⊤)) (P : LaurentCechPresentation (K := K) U M d)
  (hlinear : ∀ q t (r : K) b,
    P.coefficient q t ((ρ r) • b) = r • P.coefficient q t b)

def cochainMap (q : ℕ) :
    CechLinear.Cochain U ρ M q →ₗ[K] ProjectiveMonomialCohomology.regularCochains (ι := ι) (K := K) d q where
  toFun c := ⟨P.toLaurent c, fun t => P.regular q t (c t)⟩
  map_add' c e := by
    apply Subtype.ext
    funext t
    exact map_add (P.coefficient q t) (c t) (e t)
  map_smul' r c := by
    apply Subtype.ext
    funext t
    exact hlinear q t r (c t)

theorem cochainMap_injective (q : ℕ) :
    Function.Injective (cochainMap ρ P hlinear q) := by
  intro c e h
  funext t
  apply P.injective q t
  exact congrFun (congrArg Subtype.val h) t

theorem cochainMap_surjective (q : ℕ) :
    Function.Surjective (cochainMap ρ P hlinear q) := by
  intro c
  choose b hb using fun t => P.surjective q t (c.val t) (c.property t)
  exact ⟨b, Subtype.ext (funext hb)⟩

def cochainEquiv (q : ℕ) :
    CechLinear.Cochain U ρ M q ≃ₗ[K] ProjectiveMonomialCohomology.regularCochains (ι := ι) (K := K) d q :=
  LinearEquiv.ofBijective (cochainMap ρ P hlinear q)
    ⟨cochainMap_injective ρ P hlinear q, cochainMap_surjective ρ P hlinear q⟩

def cyclesMap (q : ℕ) :
    CechLinear.cycles U ρ M q →ₗ[K] ProjectiveMonomialCohomology.cycles (ι := ι) (K := K) d q where
  toFun c := ⟨P.toLaurent c.val, fun t => P.regular q t _, by
    change ProjectiveMonomialCechHigher.differential (P.toLaurent c.val) = 0
    have hc : CechLinear.differentialLinear U ρ M q c.val = 0 := c.property
    refine (P.toLaurent_differential c.val).symm.trans
      ((congrArg (fun c : CechLinear.Cochain U ρ M (q + 1) => P.toLaurent c) hc).trans ?_)
    funext t
    exact map_zero _⟩
  map_add' c e := by
    apply Subtype.ext
    funext t
    exact map_add (P.coefficient q t) (c.val t) (e.val t)
  map_smul' r c := by
    apply Subtype.ext
    funext t
    exact hlinear q t r (c.val t)

theorem cyclesMap_injective (q : ℕ) :
    Function.Injective (cyclesMap ρ P hlinear q) := by
  intro c e h
  apply Subtype.ext
  funext t
  apply P.injective q t
  exact congrFun (congrArg Subtype.val h) t

theorem cyclesMap_surjective (q : ℕ) :
    Function.Surjective (cyclesMap ρ P hlinear q) := by
  intro c
  choose b hb using fun t => P.surjective q t (c.val t) (c.property.1 t)
  have he : P.toLaurent b = c.val := funext hb
  have hc : CechLinear.differentialLinear U ρ M q b = 0 := by
    funext t
    apply P.injective (q + 1) t
    have h := P.toLaurent_differential b
    have hc : ProjectiveMonomialCechHigher.differential c.val = 0 := c.property.2
    rw [he, hc] at h
    exact (congrFun h t).trans (map_zero (P.coefficient (q + 1) t)).symm
  exact ⟨⟨b, hc⟩, Subtype.ext he⟩

def cyclesEquiv (q : ℕ) :
    CechLinear.cycles U ρ M q ≃ₗ[K] ProjectiveMonomialCohomology.cycles (ι := ι) (K := K) d q :=
  LinearEquiv.ofBijective (cyclesMap ρ P hlinear q)
    ⟨cyclesMap_injective ρ P hlinear q, cyclesMap_surjective ρ P hlinear q⟩

theorem cyclesEquiv_boundary (q : ℕ) (c : CechLinear.Cochain U ρ M q) :
    cyclesEquiv ρ P hlinear (q + 1) (CechLinear.boundaryToCycles U ρ M q c) =
      ProjectiveMonomialCohomology.boundaryMap d q (cochainEquiv ρ P hlinear q c) := by
  apply Subtype.ext
  exact P.toLaurent_differential c

theorem cyclesEquiv_symm_boundary (q : ℕ) (b : ProjectiveMonomialCohomology.regularCochains (ι := ι) (K := K) d q) :
    (cyclesEquiv ρ P hlinear (q + 1)).symm (ProjectiveMonomialCohomology.boundaryMap d q b) =
      CechLinear.boundaryToCycles U ρ M q ((cochainEquiv ρ P hlinear q).symm b) := by
  apply (cyclesEquiv ρ P hlinear (q + 1)).injective
  rw [LinearEquiv.apply_symm_apply, cyclesEquiv_boundary, LinearEquiv.apply_symm_apply]

include P hlinear in

theorem degreeZero_finite : Module.Finite K (CechLinear.cycles U ρ M 0) := by
  let : Module.Finite K (ProjectiveMonomialCohomology.cycles (ι := ι) (K := K) d 0) :=
    ProjectiveMonomialCohomology.degreeZero_finite d
  exact Module.Finite.of_surjective (cyclesEquiv ρ P hlinear 0).symm.toLinearMap
    (cyclesEquiv ρ P hlinear 0).symm.surjective

include P hlinear in

theorem finite_of_comparison (q : ℕ) {V : Type*} [AddCommGroup V] [Module K V]
    (f : CechLinear.cycles U ρ M (q + 1) →ₗ[K] V)
    (hboundary : ∀ b, f (CechLinear.boundaryToCycles U ρ M q b) = 0)
    (hsurj : Function.Surjective f) : Module.Finite K V := by
  let g := f.comp (cyclesEquiv ρ P hlinear (q + 1)).symm.toLinearMap
  apply ProjectiveMonomialCohomology.finite_of_boundary_annihilating_surjective d q g
  · intro b
    change f ((cyclesEquiv ρ P hlinear (q + 1)).symm
      (ProjectiveMonomialCohomology.boundaryMap d q b)) = 0
    rw [cyclesEquiv_symm_boundary]
    exact hboundary _
  · exact hsurj.comp (cyclesEquiv ρ P hlinear (q + 1)).symm.surjective

end
end PiExponent.GeometrySupport.LaurentCechFinite

end OAI
