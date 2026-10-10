import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.CurveProjection
import OAI.AlgebraicGeometry.Seshadri.Cohomology.FiniteCover

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Abelian
open MaximalSeshadri.Projective MaximalSeshadri.ModuleFlasque
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} [IsNoetherian X]

local instance : HasExt.{1} X.Modules := schemeHasExt

lemma two_affine_ext_zero (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : IsAffineOpen (U ⊓ V)) (hcover : U ⊔ V = ⊤)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (x : cohomology M (n+2)) : x = 0 := by
  let e : FiniteCoverCohomology.freeOpenModule (X := X) ⊤ ≅
      structureSheaf X := FreeOpenUnit.freeTopIso X.ringCatSheaf
  have hz : ∀ z : Ext.{1} (C := X.Modules)
      (FiniteCoverCohomology.freeOpenModule ⊤) M (n+2), z = 0 := by
    rw [← hcover]
    exact ModuleMayerVietoris.union_ext_zero X.ringCatSheaf U V M (n+1)
      (FiniteCoverCohomology.affine_open_ext_zero U hU M (n+1))
      (FiniteCoverCohomology.affine_open_ext_zero V hV M (n+1))
      (FiniteCoverCohomology.affine_open_ext_zero (U ⊓ V) hUV M n)
  have h := congrArg (fun y => (Ext.mk₀ e.inv).comp y (zero_add (n+2)))
    (hz ((Ext.mk₀ e.hom).comp x (zero_add _)))
  simpa only [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp, Ext.comp_zero] using h

theorem finite_over_line_ext_zero {K : Type} [Field K]
    (f : X ⟶ Proj (PolyGrade K Bool)) [IsFinite f]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (x : cohomology M (n+2)) : x = 0 := by
  let U (b : Bool) := f ⁻¹ᵁ Proj.basicOpen (PolyGrade K Bool) (MvPolynomial.X b)
  have hA (b : Bool) : IsAffineOpen (U b) :=
    (Proj.isAffineOpen_basicOpen _ _ (poly_X_mem b) (by decide)).preimage f
  have hUV : IsAffineOpen (U false ⊓ U true) := by
    have h := (Proj.isAffineOpen_basicOpen (PolyGrade K Bool) _
      (SetLike.mul_mem_graded (poly_X_mem false) (poly_X_mem true)) (by decide)).preimage f
    simpa only [Proj.basicOpen_mul, Scheme.Hom.preimage_inf] using h
  have hc : U false ⊔ U true = ⊤ := by
    apply top_unique
    intro z hz
    have hf : f z ∈ ⨆ b : Bool, Proj.basicOpen (PolyGrade K Bool) (MvPolynomial.X b) := by
      rw [projective_coordinate_cover]
      trivial
    obtain ⟨b,hb⟩ := Opens.mem_iSup.mp hf
    cases b with
    | false => exact Or.inl hb
    | true => exact Or.inr hb
  exact two_affine_ext_zero (U false) (U true) (hA false) (hA true) hUV hc M n x

theorem projective_curve_ext_zero {K σ : Type} [Field K] [Infinite K] [Fintype σ]
    [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {N : X.Modules}
    (s : σ → (MaximalSeshadri.Frames.O X ⟶ N))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (x : cohomology M (n+2)) : x = 0 := by
  obtain ⟨t,ht,hf⟩ := projective_curve_finite_pencil p hd s hs
  let f := sectionsMorphism
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht
  let : IsFinite f := hf
  exact finite_over_line_ext_zero f M n x

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
