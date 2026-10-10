import OAI.NumberTheory.PiExponent.Approximation.SerreAssembly
import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistAcyclicity
import OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateOverlapNaturality
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Geometry PiExponentSeshadri.ModuleFlasque
open ProjectiveTupleCharts
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (structureSheaf X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,PiExponentSeshadri.SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
attribute [local irreducible] coordinatePowerOverlap modulePow

private abbrev schemeUnit : X.Modules := SheafOfModules.unit X.ringCatSheaf

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

theorem coordinateTupleCoefficient_restrict (n q r : ℕ) (t : Fin (q + 1) → σ)
    (g : Fin (r + 1) → Fin (q + 1))
    (b : freeOpen X.ringCatSheaf
      (CechHigher.intersection (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) (t ∘ g)) ⟶
        modulePow X M n) :
    coordinateTupleCoefficient M s k hc f hf n q t
      (CechOne.restrictHom X.ringCatSheaf
        (CechHigher.intersectionLE (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) t g) b) =
      coordinateTupleCoefficient M s k hc f hf n r (t ∘ g) b := by
  change coordinatePowerOverlap M s k hc f hf n (t 0) (tupleVariables t 0)
    (freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)
      (freeOpenMap X.ringCatSheaf (homOfLE
        (CechHigher.intersectionLE (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) t g)) ≫ b)) =
    coordinatePowerOverlap M s k hc f hf n ((t ∘ g) 0) (tupleVariables (t ∘ g) 0)
      (freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s (t ∘ g) 0) b)
  erw [freeOpenHomCongr_restrict]
  exact coordinatePowerOverlap_restrict M s k hc f hf n ((t ∘ g) 0) (t 0)
    (tupleVariables (t ∘ g) 0) (tupleVariables t 0) _ _

def coordinateLaurentCechPresentation (n : ℕ) :
    ProjectiveTwistCech.LaurentCechPresentation (K := K)
      (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) (modulePow X M n) n where
  coefficient := coordinateTupleCoefficient M s k hc f hf n
  injective := coordinateTupleCoefficient_injective M s k hc f hf n
  regular := coordinateTupleCoefficient_regular M s k hc f hf n
  surjective := coordinateTupleCoefficient_surjective_regular M s k hc f hf n
  restriction q t j b :=
    coordinateTupleCoefficient_restrict M s k hc f hf n (q + 1) q t j.succAbove b

def coordinateLineBundle : LineBundle X where
  sheaf := M
  locallyRankOne x := by
    have hx : x ∈ (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) := by
      rw [hc]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact ⟨PiExponentSeshadri.SectionOpens.isoOpen (s i), hi, ⟨sectionFrame (s i)⟩⟩

include hc in
omit [Fintype σ] in

theorem coordinatePower_isQuasicoherent (n : ℕ) :
    (modulePow X M n).IsQuasicoherent :=
  LineBundleCoherent.modulePow_isQuasicoherent (coordinateLineBundle M s hc) n

include hf in

theorem coordinatePower_ext_succ_eq_zero [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (n q : ℕ)
    (x : Ext.{1} (C := X.Modules) (schemeUnit (X := X)) (modulePow X M n) (q + 1)) : x = 0 := by
  let : (modulePow X M n).IsQuasicoherent := coordinatePower_isQuasicoherent M s hc n
  exact ProjectiveTwistAcyclicity.ext_succ_eq_zero_of_laurent_cech_charts
    (coordinateOpen_isAffine M s k hc f hf) hc (modulePow X M n) n (Int.natCast_nonneg n)
    (coordinateLaurentCechPresentation M s k hc f hf n) q x

include hf in
theorem coordinatePower_ext_eq_zero [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (n q : ℕ) (hq : 0 < q)
    (x : Ext.{1} (C := X.Modules) (schemeUnit (X := X)) (modulePow X M n) q) : x = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  exact coordinatePower_ext_succ_eq_zero M s k hc f hf n r x

theorem coordinateBundle_serre [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (L : LineBundle X) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf X ⟶ L.sheaf)) (k : K →+* Γ(X,⊤))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade K (Fin l))) (hf : sectionsMorphism k s hc = f.hom)
    (A : X.Modules) [A.IsFinitePresentation] :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (C := X.Modules) (schemeUnit (X := X))
        ((moduleTwistFunctor L n).obj A) q, x = 0 := by
  apply SerreAssembly.eventual_twist_ext_zero_of_section_cover L l hl s hc
    (coordinateOpen_isAffine L.sheaf s k hc f hf) _ A
  intro n q hq x
  exact coordinatePower_ext_eq_zero L.sheaf s k hc f hf n q hq x

end
end PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity

end OAI
