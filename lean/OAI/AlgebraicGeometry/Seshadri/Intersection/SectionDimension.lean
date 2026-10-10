import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.FiniteAtlas
import OAI.AlgebraicGeometry.Seshadri.Geometry.CurveFinite
import OAI.AlgebraicGeometry.Seshadri.Divisors.PrincipalSectionIdeal
import OAI.AlgebraicGeometry.Seshadri.Divisors.CartierSection
import OAI.AlgebraicGeometry.Seshadri.Geometry.EtaleDimension
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.LocalDimension

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Frames

attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ τ : Type} [Field K] [Fintype σ] {X : Scheme}

lemma EtaleProjectiveChart.dimension_le [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) (h : X ⟶ Proj (PolyGrade K τ))
    (C : EtaleProjectiveChart g h) : ringKrullDim Γ(X,C.U.1) ≤ 2 := by
  let := C.finite
  let φ := MvPolynomial.eval₂Hom (openScalars g C.U.1)
    (fun k => -C.φ (chartCoordinate C.coord (C.a k).1))
  let : Algebra (MvPolynomial C.κ K) Γ(X,C.U.1) := φ.toAlgebra
  let : Algebra.Etale (MvPolynomial C.κ K) Γ(X,C.U.1) := C.etale
  have H := MaximalSeshadri.EtaleDimension.etale_polynomial_dimension_le K Γ(X,C.U.1) C.κ
  simpa only [C.card, Nat.cast_ofNat] using H

theorem sectionIdeal_dimension_le_one [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K τ)) [IsClosedImmersion h]
    (hbase : h ≫ projectiveToSpec = g)
    (L : LineBundle X) (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ L.sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → K)
    (hv : sectionCombination k s v ≠ 0) :
    topologicalKrullDim (sectionIdeal k s hs v).subscheme ≤ 1 := by
  apply subscheme_dimension_le_of_affine_neighborhoods
  intro x
  let y := (sectionIdeal k s hs v).subschemeι x
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (hs.ge (show y ∈ (⊤ : X.Opens) from trivial))
  obtain ⟨C,hy,hU⟩ := exists_etale_projective_neighborhood g h hbase
    (SectionOpens.isoOpen (s i)) y hi
  let := C.nonempty
  let e := sectionFrameOn (s i) C.U.1 hU
  let f := C.U.1.topIso.hom (coefficient e
    (restrictSection C.U.1.ι (sectionCombination k s v)))
  have hf : f ≠ 0 := (isRegular_iff_ne_zero).mp (L.section_coefficient_regular _ hv C.U e)
  refine ⟨C.U,hy,?_⟩
  rw [sectionIdeal_on_any_frame k s hs v C.U e]
  apply ENat.WithBot.add_le_add_one_right_iff.mp
  have H := (ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_iff_ne_zero.mpr hf)).trans (EtaleProjectiveChart.dimension_le g h C)
  exact H

theorem sectionIdeal_proper_closed_finite [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K τ)) [IsClosedImmersion h]
    (hbase : h ≫ projectiveToSpec = g)
    (L : LineBundle X) (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ L.sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → K)
    (hv : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    [IsNoetherian (sectionIdeal k s hs v).subscheme]
    {Z : Set (sectionIdeal k s hs v).subscheme} (hZ : IsClosed Z) (hp : Z ≠ Set.univ) :
    Z.Finite :=
  proper_closed_finite_of_dimension_one
    (sectionIdeal_dimension_le_one g h hbase L k s hs v hv) hZ hp

end
end MaximalSeshadri.Projective
end


end
end

end OAI
