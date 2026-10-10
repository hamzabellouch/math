import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.PencilCharts
import OAI.AlgebraicGeometry.Seshadri.Geometry.ChartCoherence
import OAI.AlgebraicGeometry.Seshadri.Sheaves.PlaneModules
import OAI.AlgebraicGeometry.Seshadri.Geometry.PlaneCoordinates
import OAI.AlgebraicGeometry.Seshadri.Cohomology.SurfaceCech

namespace OAI


                                               
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.LaurentPlane MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

abbrev planeTriple (s : Fin 3 → (O X ⟶ M)) : X.Opens :=
  tripleOpen (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2))
    (SectionOpens.isoOpen (s 0))

lemma planeTriple_le (s : Fin 3 → (O X ⟶ M)) (i : Fin 3) :
    planeTriple s ≤ SectionOpens.isoOpen (s i) := by
  fin_cases i
  · exact inf_le_left.trans inf_le_right
  · exact inf_le_left.trans inf_le_left
  · exact inf_le_right.trans inf_le_left

def planeX (s : Fin 3 → (O X ⟶ M)) : Γ((planeTriple s).toScheme,⊤)ˣ :=
  ratioUnitOn s 0 1 (planeTriple s) (planeTriple_le s 0) (planeTriple_le s 1)

def planeY (s : Fin 3 → (O X ⟶ M)) : Γ((planeTriple s).toScheme,⊤)ˣ :=
  ratioUnitOn s 0 2 (planeTriple s) (planeTriple_le s 0) (planeTriple_le s 2)

lemma finite_plane_chart (k : K →+* Γ(X,⊤))
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (i : Fin 3) :
    (MvPolynomial.eval₂Hom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (fun j : ChartVariables i => ratioOn s i j (SectionOpens.isoOpen (s i)) le_rfl)).Finite := by
  have he : (fun j : ChartVariables i => ratioOn s i j (SectionOpens.isoOpen (s i)) le_rfl) =
      (fun j : ChartVariables i => coefficient (sectionFrame (s i))
      (restrictSection (SectionOpens.isoOpen (s i)).ι (s j))) := by
    funext j
    exact ratioOn_full s i j
  rw [he]
  exact (finite_sectionsMorphism_chart k s hs i).2

theorem finite_plane_laurent (k : K →+* Γ(X,⊤))
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    let W := planeTriple s
    letI := laurentModule (W.ι.appTop.hom.comp k) (planeX s) (planeY s) (L.sheaf.restrict W.ι)
    Module.Finite (LaurentPlane.Ring K)
      (Sections (W.ι.appTop.hom.comp k) (L.sheaf.restrict W.ι) ⊤) := by
  let U := SectionOpens.isoOpen (s 0)
  let W := planeTriple s
  let kU := U.ι.appTop.hom.comp k
  let kW := W.ι.appTop.hom.comp k
  let a := ratioOn s 0 1 U le_rfl
  let b := ratioOn s 0 2 U le_rfl
  let f := X.homOfLE (planeTriple_le s 0)
  let p : MvPolynomial (ChartVariables (0 : Fin 3)) K →+* Γ(U.toScheme,⊤) :=
    MvPolynomial.eval₂Hom kU (fun j => ratioOn s 0 j U le_rfl)
  obtain ⟨hU,hp⟩ := finite_sectionsMorphism_chart k s hs (0 : Fin 3)
  have : IsAffine U.toScheme := hU
  have hp' : p.Finite := finite_plane_chart k s hs 0
  have ho : f.opensRange = U.toScheme.basicOpen (a*b) := by
    rw [Scheme.opensRange_homOfLE]
    change U.ι ⁻¹ᵁ ((SectionOpens.isoOpen (s 1) ⊓ U) ⊓
      (SectionOpens.isoOpen (s 2) ⊓ U)) = _
    simp only [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, inf_top_eq]
    rw [ratioOn_basicOpen s 0 1 U le_rfl, ratioOn_basicOpen s 0 2 U le_rfl]
    exact (Scheme.basicOpen_mul _ _ _).symm
  have ha : f.appTop a = (planeX s : Γ(W.toScheme,⊤)) := by
    rw [planeX, ratioUnitOn_val]
    exact ratioOn_restrict s 0 1 le_rfl (planeTriple_le s 0)
  have hb : f.appTop b = (planeY s : Γ(W.toScheme,⊤)) := by
    rw [planeY, ratioUnitOn_val]
    exact ratioOn_restrict s 0 2 le_rfl (planeTriple_le s 0)
  let e : MvPolynomial (ChartVariables (0 : Fin 3)) K →+* LaurentPlane.Ring K :=
    MvPolynomial.eval₂Hom (algebraMap K _) (fun j => T (if j.val = 1 then (1,0) else (0,1)))
  apply laurent_finite_of_affine kU kW f (nestedBase k (planeTriple_le s 0))
    (L.restrict U.ι) (nestedRestriction L.sheaf (planeTriple_le s 0)) a b ho
    (planeX s) (planeY s) ha hb p hp' e
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, p, e, MvPolynomial.eval₂Hom_C, eval_algebraMap]
    exact RingHom.congr_fun (nestedBase k (planeTriple_le s 0)) r
  · intro j
    simp only [RingHom.comp_apply, p, e, MvPolynomial.eval₂Hom_X']
    have hj : j.val = 1 ∨ j.val = 2 := by
      have h := j.property
      have h' := j.val.isLt
      omega
    rcases hj with hj | hj
    · simp only [hj, ↓reduceIte, eval_T, zpow_one, zpow_zero, mul_one]
      exact ha
    · simp only [hj, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte, eval_T,
        zpow_zero, zpow_one, one_mul]
      exact hb

end
end MaximalSeshadri.Projective

end


end OAI
