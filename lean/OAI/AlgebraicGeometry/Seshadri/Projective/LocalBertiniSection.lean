import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.BertiniEquations
import OAI.AlgebraicGeometry.Seshadri.Configurations.RationalPoint
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionChart
import OAI.AlgebraicGeometry.Seshadri.Geometry.LocalCoordinateAtlas

namespace OAI

section
noncomputable section
                                             
section

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.BertiniIntegral MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_smooth_integral_cartier_section_of_local_coordinates
    {K : Type} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    {n : ℕ} (X : Scheme) [IsIntegral X] [CompactSpace X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (M : X.Modules) (k : K →+* Γ(X, ⊤))
    (s : Option (Fin n) → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (h : X ⟶ Proj (PolyGrade K (Option (Fin n))))
    (hh : h = sectionsMorphism k s hs)
    (hbase : h ≫ projectiveToSpec = g)
    (hlocal : ∀ x : X, ∃ i : Option (Fin n), ∃ V : X.affineOpens, x ∈ V.1 ∧
      ∃ φ : PolyChart (R := K) i →+* Γ(X, V.1), Function.Surjective φ ∧
        Spec.map (CommRingCat.ofHom φ) ≫
          Proj.awayι (PolyGrade K (Option (Fin n))) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
            V.2.fromSpec ≫ h)
    (q : MvPolynomial (Option (Fin n)) K) (hq : q ≠ 0) :
    ∃ t : Option (Fin n) → K, MvPolynomial.aeval t q ≠ 0 ∧
      IsIntegral (projectiveHyperplane h t).subscheme ∧
      Smooth ((projectiveHyperplane h t).subschemeι ≫ g) ∧
      ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ r : Γ(X, U.1),
        IsRegular r ∧ (projectiveHyperplane h t).ideal U = Ideal.span {r} ∧
        ∃ e : M.restrict U.1.ι ≅ O U.1.toScheme,
          U.1.topIso.hom (coefficient e (restrictSection U.1.ι
            (sectionCombination k s t))) = r := by
  classical
  let A := Classical.choice (finite_atlas_of_local_coordinates g h hbase hlocal)
  let C := A.chart
  let : Finite A.ι := A.finite
  let : ∀ j, Nonempty (C j).U.1 := fun j => (C j).nonempty
  let : ∀ j, IsDomain Γ(X, (C j).U.1) := fun j => inferInstance
  let : ∀ j, Algebra K Γ(X, (C j).U.1) :=
    fun j => (openScalars g (C j).U.1).toAlgebra
  let : ∀ j, Finite (C j).κ := fun j => (C j).finite
  let : ∀ j, Algebra (MvPolynomial (C j).κ K) Γ(X, (C j).U.1) :=
    fun j => (MvPolynomial.eval₂Hom (openScalars g (C j).U.1)
      (fun k => -(C j).φ (chartCoordinate (C j).coord ((C j).a k).1))).toAlgebra
  let : ∀ j, IsScalarTower K (MvPolynomial (C j).κ K) Γ(X, (C j).U.1) := by
    intro j
    apply IsScalarTower.of_algebraMap_eq'
    ext k
    exact (MvPolynomial.eval₂Hom_C _ _ k).symm
  let : ∀ j, Algebra.Etale (MvPolynomial (C j).κ K) Γ(X, (C j).U.1) :=
    fun j => (C j).etale
  let : ∀ j, Algebra.FiniteType K Γ(X, (C j).U.1) := fun j =>
    Algebra.FiniteType.trans (R := K) (S := MvPolynomial (C j).κ K)
      (A := Γ(X, (C j).U.1)) inferInstance inferInstance
  let : Fintype A.ι := Fintype.ofFinite _
  let ψ (j : A.ι) : Γ(X, (C j).U.1) →ₐ[K] K :=
    Classical.choice (exists_point_finite_type (K := K) (R := Γ(X, (C j).U.1)))
  let v (j : A.ι) (k : Option (Fin n)) : K :=
    ψ j ((C j).φ (chartCoordinate (C j).coord k))
  let P (j : A.ι) : MvPolynomial (Option (Fin n)) K := linearEquation (v j)
  have hP (j : A.ι) : P j ≠ 0 :=
    linearEquation_ne_zero (v j) (C j).coord (by
      simp [v, chartCoordinate_self])
  let Q := q * ∏ j, P j
  have hQ : Q ≠ 0 := mul_ne_zero hq (Finset.prod_ne_zero_iff.mpr (fun j _ => hP j))
  let δ (j : A.ι) : Fin n ≃ ChartVariables (C j).coord :=
    Equiv.optionSubtype (C j).coord ⟨Equiv.swap none (C j).coord, by simp⟩
  let e (j : A.ι) : Option (Fin n) ≃ Option (Fin n) :=
    ((Equiv.optionSubtype (C j).coord).symm (δ j)).1
  have hp (j : A.ι) : ∃ a b : (C j).κ, a ≠ b := by
    let : Fintype (C j).κ := Fintype.ofFinite _
    have hcard : Fintype.card (C j).κ = 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact (C j).card
    let : Nontrivial (C j).κ := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_pair_ne _
  choose a b hab using hp
  have hc : ∀ j, ∀ c, (C j).φ (chartConstants (C j).coord c) =
      openScalars g (C j).U.1 c := fun j =>
    projective_affine_constants h g hbase (C j).U (spec_openScalars g (C j).U)
      _ (C j).φ (C j).factor
  obtain ⟨t, ht, hI, hS, heq⟩ :=
    smooth_integral_hyperplane_of_etale_atlas_with_equations X g h hbase
    (fun j => (C j).U) A.cover (fun j => spec_openScalars g (C j).U)
    e (fun j => (C j).φ) (fun j => (C j).factor) (fun j => (C j).κ)
    (fun j => (δ j).symm ((C j).a (a j)))
    (fun j => (δ j).symm ((C j).a (b j))) a b hab
    (by
      intro j
      change -(C j).φ (chartCoordinate (C j).coord (δ j ((δ j).symm ((C j).a (a j)))).1) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.X (a j))
      rw [Equiv.apply_symm_apply, MvPolynomial.eval₂Hom_X'])
    (by
      intro j
      change -(C j).φ (chartCoordinate (C j).coord (δ j ((δ j).symm ((C j).a (b j)))).1) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.X (b j))
      rw [Equiv.apply_symm_apply, MvPolynomial.eval₂Hom_X'])
    A.base A.overlap A.left A.right Q hQ

  have htq : MvPolynomial.aeval t q ≠ 0 :=
    (mul_ne_zero_iff.mp (by simpa only [Q, map_mul] using ht)).1
  have htP (j : A.ι) : MvPolynomial.aeval t (P j) ≠ 0 := by
    have hh := (mul_ne_zero_iff.mp (by simpa only [Q, map_mul] using ht)).2
    rw [map_prod] at hh
    exact Finset.prod_ne_zero_iff.mp hh j (Finset.mem_univ j)
  refine ⟨t, htq, hI, hS, fun x => ?_⟩
  obtain ⟨j, hj⟩ := A.cover x
  let r : Γ(X, (C j).U.1) := ∑ k, (C j).φ (chartConstants (C j).coord (t k)) *
    (C j).φ (chartCoordinate (C j).coord k)
  have hψr : ψ j r = MvPolynomial.aeval t (P j) := by
    simp only [r, map_sum, map_mul, hc, P, linearEquation, MvPolynomial.aeval_C,
      MvPolynomial.aeval_X]
    apply Finset.sum_congr rfl
    intro k hk
    have hh : ψ j (openScalars g (C j).U.1 (t k)) = t k := (ψ j).commutes _
    rw [hh, mul_comm]
    rfl
  have hr : r ≠ 0 := by
    intro hz
    apply htP j
    rw [← hψr, hz, map_zero]
  obtain ⟨e, he⟩ := sectionsMorphism_affine_equation k s hs (C j).U
    (C j).coord (C j).φ (by simpa only [← hh] using (C j).factor)
  exact ⟨(C j).U, hj, r, isRegular_iff_ne_zero.mpr hr, heq j, e, he t⟩

end
end MaximalSeshadri.ProjectiveBertini

end


end
end

end OAI
