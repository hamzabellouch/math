import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Configurations.RationalPoint
import OAI.AlgebraicGeometry.Seshadri.Nodal.BranchDimension
import OAI.AlgebraicGeometry.Seshadri.Intersection.SectionDimension
import OAI.AlgebraicGeometry.Seshadri.Divisors.IntegralSectionIdeal
import OAI.AlgebraicGeometry.Seshadri.Geometry.EtaleLowerDimension

namespace OAI


                                                  
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Frames

attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ τ : Type} [Field K] [IsAlgClosed K] [Fintype σ] {X : Scheme}

theorem sectionIdeal_dimension_eq_one [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K τ)) [IsClosedImmersion h]
    (hbase : h ≫ projectiveToSpec = g)
    (L : LineBundle X) (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ L.sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → K)
    (hv : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme] :
    topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1 := by
  apply le_antisymm (sectionIdeal_dimension_le_one g h hbase L k s hs v hv)
  let I := sectionIdeal k s hs v
  obtain ⟨z⟩ : Nonempty I.subscheme := inferInstance
  let y := I.subschemeι z
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (hs.ge (show y ∈ (⊤ : X.Opens) from trivial))
  obtain ⟨C,hy,hU⟩ := exists_etale_projective_neighborhood g h hbase
    (SectionOpens.isoOpen (s i)) y hi
  let := C.nonempty
  let := C.finite
  let : Fintype C.κ := Fintype.ofFinite _
  let : Algebra K Γ(X,C.U.1) := (openScalars g C.U.1).toAlgebra
  let : Algebra (MvPolynomial C.κ K) Γ(X,C.U.1) :=
    (MvPolynomial.eval₂Hom (openScalars g C.U.1)
      (fun j => -C.φ (chartCoordinate C.coord (C.a j).1))).toAlgebra
  let : IsScalarTower K (MvPolynomial C.κ K) Γ(X,C.U.1) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext k
    exact (MvPolynomial.eval₂Hom_C _ _ k).symm
  let : Algebra.Etale (MvPolynomial C.κ K) Γ(X,C.U.1) := C.etale
  let : Algebra.FiniteType K Γ(X,C.U.1) :=
    Algebra.FiniteType.trans (R := K) (S := MvPolynomial C.κ K)
      (A := Γ(X,C.U.1)) inferInstance inferInstance
  let e := sectionFrameOn (s i) C.U.1 hU
  let r := C.U.1.topIso.hom (coefficient e
    (restrictSection C.U.1.ι (sectionCombination k s v)))
  have hI : I.ideal C.U = Ideal.span {r} := sectionIdeal_on_any_frame k s hs v C.U e
  have hp : (Ideal.span {r}).IsPrime := by
    rw [← hI]
    apply ideal_prime_of_integral_subscheme I C.U y hy
    change y ∈ (I.support : Set X)
    rw [← I.range_subschemeι]
    exact ⟨z,rfl⟩
  let := hp
  obtain ⟨f⟩ := exists_point_finite_type (K := K) (R := Γ(X,C.U.1) ⧸ Ideal.span {r})
  have H := MaximalSeshadri.EtaleDimension.etale_principal_dimension_lower K Γ(X,C.U.1) C.κ
    (f.comp (Ideal.Quotient.mkₐ K (Ideal.span {r}))) r (by
      change f (Ideal.Quotient.mk _ r) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton r)),map_zero])
  have hcard : Fintype.card C.κ = 2 := by rw [← Nat.card_eq_fintype_card]; exact C.card
  rw [hcard] at H
  have H' : (1 : WithBot ℕ∞) ≤ ringKrullDim (Γ(X,C.U.1) ⧸ Ideal.span {r}) := by
    apply ENat.WithBot.add_le_add_one_right_iff.mp
    simpa only [Nat.cast_ofNat,one_add_one_eq_two] using H
  have H'' := subscheme_dimension_ge_affine_chart I C.U
  rw [hI] at H''
  exact H'.trans H''

end
end MaximalSeshadri.Projective

end


end OAI
