import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.ToricCoordinates
import OAI.AlgebraicGeometry.Seshadri.Cohomology.ToricSpan
import OAI.AlgebraicGeometry.Seshadri.Geometry.NestedChart
import OAI.AlgebraicGeometry.Seshadri.Cohomology.PlanePairs

namespace OAI


                                     
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections MaximalSeshadri.Frames
open MaximalSeshadri.LaurentPlane MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

abbrev planeVertex (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) (i : Fin 3) :=
  (chartRes k L.sheaf (planeTriple_le s i)).range

lemma planeVertex_stable (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    letI := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
      (L.sheaf.restrict (planeTriple s).ι)
    ∀ i z, z ∈ vertexCone i → ∀ x ∈ planeVertex k s L i, T (K := K) z • x ∈ planeVertex k s L i := by
  let := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
    (L.sheaf.restrict (planeTriple s).ι)
  intro i z hz
  apply chartMap_monomial_mem _ _ _ _ _ _ (planeX s) (planeY s) z
  exact plane_vertex_lift k s i z hz

lemma planeVertex_cross_clearing (k : K →+* Γ(X,⊤))
    (s : Fin 3 → (O X ⟶ M)) (haff : ∀ i, IsAffineOpen (SectionOpens.isoOpen (s i)))
    (L : LineBundle X) :
    letI := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
      (L.sheaf.restrict (planeTriple s).ι)
    ∀ i j x, x ∈ planeVertex k s L j →
      ∃ d : ℕ, T (K := K) (d • (weight j-weight i)) • x ∈ planeVertex k s L i := by
  let := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
    (L.sheaf.restrict (planeTriple s).ι)
  intro i j x hx
  let U := SectionOpens.isoOpen (s i)
  let V := SectionOpens.isoOpen (s j)
  let : IsAffine U.toScheme := haff i
  have hbasic : (X.homOfLE (show U ⊓ V ≤ U from inf_le_left)).opensRange =
      U.toScheme.basicOpen (ratioOn s i j U le_rfl) :=
    pairRestriction_basic s i j U (U ⊓ V) le_rfl inf_le_left rfl
  obtain ⟨d,hd⟩ := chartRes_cross_clearing k L.sheaf U V (planeTriple s)
    (planeTriple_le s i) (planeTriple_le s j) (ratioOn s i j U le_rfl) hbasic x hx
  refine ⟨d,?_⟩
  rw [plane_ratio_weight_restrict k s i j U le_rfl (planeTriple_le s i),← map_pow,← T_nsmul] at hd
  exact hd

lemma planeVertex_finite_generators (k : K →+* Γ(X,⊤))
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) (i : Fin 3) :
    letI := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
      (L.sheaf.restrict (planeTriple s).ι)
    ∃ d : ℕ, ∃ g : Fin d → Sections ((planeTriple s).ι.appTop.hom.comp k)
      (L.sheaf.restrict (planeTriple s).ι) ⊤,
      (∀ a, g a ∈ planeVertex k s L i) ∧
      planeVertex k s L i = monomialSpan (K := K) (vertexCone i) g := by
  let U := SectionOpens.isoOpen (s i)
  let W := planeTriple s
  let kU := U.ι.appTop.hom.comp k
  let := laurentModule (W.ι.appTop.hom.comp k) (planeX s) (planeY s) (L.sheaf.restrict W.ι)
  let := laurentTower (W.ι.appTop.hom.comp k) (planeX s) (planeY s) (L.sheaf.restrict W.ι)
  let P := MvPolynomial (ChartVariables i) K
  let p : P →+* Γ(U.toScheme,⊤) := MvPolynomial.eval₂Hom kU (fun j => ratioOn s i j U le_rfl)
  let : IsAffine U.toScheme := (finite_sectionsMorphism_chart k s hs i).1
  let : Algebra P Γ(U.toScheme,⊤) := p.toAlgebra
  let : Module.Finite P Γ(U.toScheme,⊤) := finite_plane_chart k s hs i
  let : Module P (Sections kU (L.sheaf.restrict U.ι) ⊤) := Module.compHom _ p
  let : Module.Finite Γ(U.toScheme,⊤) (Sections kU (L.sheaf.restrict U.ι) ⊤) :=
    (L.restrict U.ι).affine_openSections_finite
  let : IsScalarTower P Γ(U.toScheme,⊤) (Sections kU (L.sheaf.restrict U.ι) ⊤) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  let : Module.Finite P (Sections kU (L.sheaf.restrict U.ι) ⊤) := Module.Finite.trans Γ(U.toScheme,⊤) _
  let : IsScalarTower K P (Sections kU (L.sheaf.restrict U.ι) ⊤) := by
    apply IsScalarTower.of_algebraMap_smul
    intro r m
    change p (algebraMap K P r) • (m : OpenSections (L.sheaf.restrict U.ι) ⊤) = kU r • m
    change p (MvPolynomial.C r) • (m : OpenSections (L.sheaf.restrict U.ι) ⊤) = kU r • m
    rw [show p (MvPolynomial.C r) = kU r from MvPolynomial.eval₂Hom_C _ _ _]
  apply finite_monomial_generators i (fun j : ChartVariables i => j.val)
    (chartRes k L.sheaf (planeTriple_le s i)) (planeVertex_stable k s L i)
  intro j n
  change chartRes k L.sheaf (planeTriple_le s i) (p (MvPolynomial.X j) • n) = _
  rw [chartMap_smul]
  rw [show p (MvPolynomial.X j) = ratioOn s i j U le_rfl from MvPolynomial.eval₂Hom_X' _ _ _,
    plane_ratio_weight_restrict k s i j U le_rfl (planeTriple_le s i)]
  rfl

end
end MaximalSeshadri.Projective

end

end OAI
