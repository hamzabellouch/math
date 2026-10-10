import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.SurfaceBaseCech
import OAI.AlgebraicGeometry.Seshadri.Sheaves.PlaneProjectionModule
import OAI.AlgebraicGeometry.Seshadri.Cohomology.PlaneCechFinite

namespace OAI


                                    
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

lemma pairRestriction_basic (s : Fin 3 → (O X ⟶ M)) (i j : Fin 3)
    (U W : X.Opens) (hi : U ≤ SectionOpens.isoOpen (s i)) (h : W ≤ U)
    (he : W = U ⊓ SectionOpens.isoOpen (s j)) :
    (X.homOfLE h).opensRange = U.toScheme.basicOpen (ratioOn s i j U hi) := by
  rw [Scheme.opensRange_homOfLE,he,Scheme.Hom.preimage_inf,
    Scheme.Opens.ι_preimage_self,top_inf_eq]
  exact ratioOn_basicOpen s i j U hi

lemma planeThird_unit (s : Fin 3 → (O X ⟶ M)) :
    ratioUnitOn s 2 1 (planeTriple s) (planeTriple_le s 2) (planeTriple_le s 1) =
      planeX s * (planeY s)⁻¹ := by
  have h := ratioUnitOn_cocycle s 0 2 1 (planeTriple s)
    (planeTriple_le s 0) (planeTriple_le s 2) (planeTriple_le s 1)
  change planeX s = planeY s * _ at h
  calc
    _ = (planeY s)⁻¹ * planeX s := by rw [h, ← mul_assoc, inv_mul_cancel, one_mul]
    _ = _ := mul_comm _ _

theorem finite_plane_cokernel [X.IsSeparated] (k : K →+* Γ(X,⊤))
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    Module.Finite K (Sections k L.sheaf (planeTriple s) ⧸
      tripleBaseImage k L.sheaf (SectionOpens.isoOpen (s 1))
        (SectionOpens.isoOpen (s 2)) (SectionOpens.isoOpen (s 0))) := by
  let U := SectionOpens.isoOpen (s 1)
  let V := SectionOpens.isoOpen (s 2)
  let Z := SectionOpens.isoOpen (s 0)
  let A := U ⊓ Z
  let B := V ⊓ Z
  let C := U ⊓ V
  let W := planeTriple s
  have hU : IsAffineOpen U := (finite_sectionsMorphism_chart k s hs 1).1
  have hV : IsAffineOpen V := (finite_sectionsMorphism_chart k s hs 2).1
  have hZ : IsAffineOpen Z := (finite_sectionsMorphism_chart k s hs 0).1
  let : IsAffine A.toScheme := hU.inf hZ
  let : IsAffine B.toScheme := hV.inf hZ
  let : IsAffine C.toScheme := hU.inf hV
  have hA : W ≤ A := inf_le_left
  have hB : W ≤ B := inf_le_right
  have hC : W ≤ C := inf_le_inf inf_le_left inf_le_left
  let a := X.homOfLE hA
  let b := X.homOfLE hB
  let c := X.homOfLE hC
  let kA := A.ι.appTop.hom.comp k
  let kB := B.ι.appTop.hom.comp k
  let kC := C.ι.appTop.hom.comp k
  let kW := W.ι.appTop.hom.comp k
  let ea := nestedRestriction L.sheaf hA
  let eb := nestedRestriction L.sheaf hB
  let ec := nestedRestriction L.sheaf hC
  let F := chartMap kA kW a (nestedBase k hA) (L.restrict A.ι).sheaf ea
  let G := chartMap kB kW b (nestedBase k hB) (L.restrict B.ι).sheaf eb
  let H := chartMap kC kW c (nestedBase k hC) (L.restrict C.ι).sheaf ec
  let ax := ratioUnitOn s 0 1 A inf_le_right inf_le_left
  let ay := ratioOn s 0 2 A inf_le_right
  let bx := ratioOn s 0 1 B inf_le_right
  let by' := ratioUnitOn s 0 2 B inf_le_right inf_le_left
  let cx := ratioUnitOn s 2 1 C inf_le_right inf_le_left
  let cy := ratioOn s 2 0 C inf_le_right
  have ha : a.opensRange = A.toScheme.basicOpen ay := by
    apply pairRestriction_basic s 0 2 A W inf_le_right hA
    dsimp only [W,planeTriple,tripleOpen,A,U,V,Z]
    simp only [inf_assoc,inf_left_comm,inf_comm,inf_left_idem]
  have hb : b.opensRange = B.toScheme.basicOpen bx := by
    apply pairRestriction_basic s 0 1 B W inf_le_right hB
    dsimp only [W,planeTriple,tripleOpen,B,U,V,Z]
    simp only [inf_assoc,inf_left_comm,inf_comm,inf_left_idem]
  have hc : c.opensRange = C.toScheme.basicOpen cy := by
    apply pairRestriction_basic s 2 0 C W inf_le_right hC
    dsimp only [W,planeTriple,tripleOpen,C,U,V,Z]
    simp only [inf_assoc,inf_left_comm,inf_comm,inf_left_idem]
  have hax : Units.map a.appTop.hom ax = planeX s :=
    ratioUnitOn_restrict s 0 1 inf_le_right inf_le_left hA
  have hay : a.appTop ay = (planeY s : Γ(W.toScheme,⊤)) := by
    rw [planeY,ratioUnitOn_val]
    exact ratioOn_restrict s 0 2 inf_le_right hA
  have hbx : b.appTop bx = (planeX s : Γ(W.toScheme,⊤)) := by
    rw [planeX,ratioUnitOn_val]
    exact ratioOn_restrict s 0 1 inf_le_right hB
  have hby : Units.map b.appTop.hom by' = planeY s :=
    ratioUnitOn_restrict s 0 2 inf_le_right inf_le_left hB
  have hcx : Units.map c.appTop.hom cx = planeX s * (planeY s)⁻¹ := by
    rw [show Units.map c.appTop.hom cx = ratioUnitOn s 2 1 W
      (planeTriple_le s 2) (planeTriple_le s 1) from
      ratioUnitOn_restrict s 2 1 inf_le_right inf_le_left hC]
    exact planeThird_unit s
  have hcy : c.appTop cy = (↑((planeY s)⁻¹) : Γ(W.toScheme,⊤)) := by
    rw [show c.appTop cy = ratioOn s 2 0 W (planeTriple_le s 2) from
      ratioOn_restrict s 2 0 inf_le_right hC]
    rw [← ratioUnitOn_val s 2 0 W (planeTriple_le s 2) (planeTriple_le s 0),
      ratioUnitOn_symm]
    rfl
  let : Module.Finite K (Sections kW (L.sheaf.restrict W.ι) ⊤ ⧸
      ((F.range ⊔ G.range) ⊔ H.range)) :=
    three_chart_quotient_finite kA kB kC kW a b c (nestedBase k hA)
      (nestedBase k hB) (nestedBase k hC) (L.restrict A.ι) (L.restrict B.ι)
      (L.restrict C.ι) (L.sheaf.restrict W.ι) ea eb ec (planeX s) (planeY s)
      ax ay bx by' cx cy hax hay hbx hby hcx hcy ha hb hc (finite_plane_laurent k s hs L)
  let E := chartTop k L.sheaf W
  have he : ((F.range ⊔ G.range) ⊔ H.range).map E.toLinearMap =
      tripleBaseImage k L.sheaf U V Z := by
    rw [Submodule.map_sup,Submodule.map_sup]
    exact congrArg₂ (· ⊔ ·) (congrArg₂ (· ⊔ ·)
      (chartMap_range_coherent k L.sheaf hA) (chartMap_range_coherent k L.sheaf hB))
      (chartMap_range_coherent k L.sheaf hC)
  let q := Submodule.Quotient.equiv ((F.range ⊔ G.range) ⊔ H.range)
    (tripleBaseImage k L.sheaf U V Z) E he
  exact Module.Finite.of_surjective q.toLinearMap q.surjective

end
end MaximalSeshadri.Projective

end

end OAI
