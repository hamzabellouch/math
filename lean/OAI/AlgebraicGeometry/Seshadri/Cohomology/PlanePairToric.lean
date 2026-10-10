import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.PlaneVertex

namespace OAI


                                        
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections MaximalSeshadri.Frames
open MaximalSeshadri.LaurentPlane MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

abbrev planePair (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) (i j : Fin 3) :=
  (chartRes k L.sheaf (le_inf (planeTriple_le s i) (planeTriple_le s j))).range

lemma planeVertex_le_pair (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) (i j : Fin 3) :
    planeVertex k s L i ≤ planePair k s L i j :=
  chartRes_range_le k L.sheaf (le_inf (planeTriple_le s i) (planeTriple_le s j)) inf_le_left

lemma planeVertex_le_pair_right (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) (i j : Fin 3) :
    planeVertex k s L j ≤ planePair k s L i j :=
  chartRes_range_le k L.sheaf (le_inf (planeTriple_le s i) (planeTriple_le s j)) inf_le_right

lemma planePair_clearing (k : K →+* Γ(X,⊤))
    (s : Fin 3 → (O X ⟶ M)) (haff : ∀ i, IsAffineOpen (SectionOpens.isoOpen (s i)))
    (L : LineBundle X) :
    letI := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
      (L.sheaf.restrict (planeTriple s).ι)
    ∀ i j x, x ∈ planePair k s L i j →
      ∃ d : ℕ, T (K := K) (d • (weight j-weight i)) • x ∈ planeVertex k s L i := by
  let := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
    (L.sheaf.restrict (planeTriple s).ι)
  intro i j x hx
  let U := SectionOpens.isoOpen (s i)
  let V := U ⊓ SectionOpens.isoOpen (s j)
  let : IsAffine U.toScheme := haff i
  have hbasic : (X.homOfLE (show U ⊓ V ≤ U from inf_le_left)).opensRange =
      U.toScheme.basicOpen (ratioOn s i j U le_rfl) := by
    apply pairRestriction_basic s i j U (U ⊓ V) le_rfl inf_le_left
    simp only [V,← inf_assoc,inf_idem]
  obtain ⟨d,hd⟩ := chartRes_cross_clearing k L.sheaf U V (planeTriple s)
    (planeTriple_le s i) (le_inf (planeTriple_le s i) (planeTriple_le s j))
    (ratioOn s i j U le_rfl) hbasic x hx
  refine ⟨d,?_⟩
  rw [plane_ratio_weight_restrict k s i j U le_rfl (planeTriple_le s i),← map_pow,← T_nsmul] at hd
  exact hd

lemma planePair_stable01 (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    letI := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
      (L.sheaf.restrict (planeTriple s).ι)
    ∀ z ∈ coneA, ∀ x ∈ planePair k s L 0 1, T (K := K) z • x ∈ planePair k s L 0 1 := by
  let := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
    (L.sheaf.restrict (planeTriple s).ι)
  intro z hz
  apply chartMap_monomial_mem _ _ _ _ _ _ (planeX s) (planeY s) z
  let U := SectionOpens.isoOpen (s 0) ⊓ SectionOpens.isoOpen (s 1)
  let h := le_inf (planeTriple_le s 0) (planeTriple_le s 1)
  let f := X.homOfLE h
  let u := ratioUnitOn s 0 1 U inf_le_left inf_le_right
  let v := ratioOn s 0 2 U inf_le_left
  refine ⟨↑(u ^ z.1) * v ^ z.2.toNat,?_⟩
  apply lift_cone_left _ (planeX s) (planeY s) f.appTop.hom u v _ _ z hz
  · exact ratioUnitOn_restrict s 0 1 inf_le_left inf_le_right h
  · rw [show f.appTop v = ratioOn s 0 2 (planeTriple s) (planeTriple_le s 0) from
      ratioOn_restrict s 0 2 inf_le_left h]
    exact (ratioUnitOn_val s 0 2 _ _ _).symm

lemma planePair_stable02 (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    letI := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
      (L.sheaf.restrict (planeTriple s).ι)
    ∀ z ∈ coneB, ∀ x ∈ planePair k s L 0 2, T (K := K) z • x ∈ planePair k s L 0 2 := by
  let := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
    (L.sheaf.restrict (planeTriple s).ι)
  intro z hz
  apply chartMap_monomial_mem _ _ _ _ _ _ (planeX s) (planeY s) z
  let U := SectionOpens.isoOpen (s 0) ⊓ SectionOpens.isoOpen (s 2)
  let h := le_inf (planeTriple_le s 0) (planeTriple_le s 2)
  let f := X.homOfLE h
  let u := ratioOn s 0 1 U inf_le_left
  let v := ratioUnitOn s 0 2 U inf_le_left inf_le_right
  refine ⟨u ^ z.1.toNat * ↑(v ^ z.2),?_⟩
  apply lift_cone_right _ (planeX s) (planeY s) f.appTop.hom u v _ _ z hz
  · rw [show f.appTop u = ratioOn s 0 1 (planeTriple s) (planeTriple_le s 0) from
      ratioOn_restrict s 0 1 inf_le_left h]
    exact (ratioUnitOn_val s 0 1 _ _ _).symm
  · exact ratioUnitOn_restrict s 0 2 inf_le_left inf_le_right h

lemma planePair_stable12 (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    letI := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
      (L.sheaf.restrict (planeTriple s).ι)
    ∀ z ∈ coneC 0, ∀ x ∈ planePair k s L 1 2, T (K := K) z • x ∈ planePair k s L 1 2 := by
  let := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
    (L.sheaf.restrict (planeTriple s).ι)
  intro z hz
  apply chartMap_monomial_mem _ _ _ _ _ _ (planeX s) (planeY s) z
  let U := SectionOpens.isoOpen (s 1) ⊓ SectionOpens.isoOpen (s 2)
  let h := le_inf (planeTriple_le s 1) (planeTriple_le s 2)
  let f := X.homOfLE h
  let u := ratioUnitOn s 2 1 U inf_le_right inf_le_left
  let v := ratioOn s 2 0 U inf_le_right
  refine ⟨↑(u ^ z.1) * v ^ (-(z.1 + z.2)).toNat,?_⟩
  apply lift_cone_top _ (planeX s) (planeY s) f.appTop.hom u v _ _ z hz
  · rw [show Units.map f.appTop.hom u = ratioUnitOn s 2 1 (planeTriple s)
      (planeTriple_le s 2) (planeTriple_le s 1) from ratioUnitOn_restrict s 2 1 inf_le_right inf_le_left h]
    exact planeThird_unit s
  · rw [show f.appTop v = ratioOn s 2 0 (planeTriple s) (planeTriple_le s 2) from
      ratioOn_restrict s 2 0 inf_le_right h]
    rw [← ratioUnitOn_val s 2 0 (planeTriple s) (planeTriple_le s 2) (planeTriple_le s 0),ratioUnitOn_symm]
    rfl

end
end MaximalSeshadri.Projective

end


end OAI
