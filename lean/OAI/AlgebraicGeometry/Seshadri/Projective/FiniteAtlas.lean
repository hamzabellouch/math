import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.ProjectiveRefinement

namespace OAI

section
noncomputable section
                                              

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme} {σ : Type}

lemma projective_standard_cover :
    (⨆ i : σ, Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i)) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  change p ∈ idealOfVars σ K
  rw [← pow_one (idealOfVars σ K), mem_pow_idealOfVars_iff]
  intro d hd
  change 1 ≤ d.sum fun _ v => v
  rw [Finsupp.sum, ← hp.degree_eq_sum_deg_support hd]
  exact hn

 theorem exists_etale_projective_neighborhood [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K σ)) [IsClosedImmersion h]
    (hbase : h ≫ projectiveToSpec = g)
    (W : X.Opens) (x : X) (hxW : x ∈ W) :
    ∃ C : EtaleProjectiveChart g h, x ∈ C.U.1 ∧ C.U.1 ≤ W := by
  have hx : h x ∈ ⨆ i : σ, Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i) := by
    rw [projective_standard_cover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  obtain ⟨C, hxC, hCW, _⟩ := exists_etale_projective_chart g h hbase i W x hxW hi
  exact ⟨C, hxC, hCW⟩

structure OverlappingEtaleProjectiveAtlas
    (g : X ⟶ Spec (CommRingCat.of K)) (h : X ⟶ Proj (PolyGrade K σ)) where
  ι : Type
  finite : Finite ι
  chart : ι → EtaleProjectiveChart g h
  cover : ∀ x : X, ∃ j, x ∈ (chart j).U.1
  base : ι
  overlap : ι → ι
  left : ∀ j, (chart (overlap j)).U.1 ≤ (chart base).U.1
  right : ∀ j, (chart (overlap j)).U.1 ≤ (chart j).U.1

 theorem exists_finite_etale_projective_atlas [IsIntegral X] [CompactSpace X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K σ)) [IsClosedImmersion h]
    (hbase : h ≫ projectiveToSpec = g) :
    Nonempty (OverlappingEtaleProjectiveAtlas g h) := by
  classical
  choose C hC using (fun x : X => exists_etale_projective_neighborhood g h hbase ⊤ x
    (show x ∈ (⊤ : X.Opens) from trivial))
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X => ((C x).U.1 : Set X))
    (fun x => (C x).U.1.isOpen) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, (hC x).1⟩)
  have hcover : ∀ x : X, ∃ j : s, x ∈ (C j.1).U.1 := by
    intro x
    obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨⟨j, hj⟩, hx⟩
  let x₀ : X := Classical.arbitrary X
  obtain ⟨j₀, _⟩ := hcover x₀
  have hov (j : s) : ∃ D : EtaleProjectiveChart g h,
      D.U.1 ≤ (C j₀.1).U.1 ∧ D.U.1 ≤ (C j.1).U.1 := by
    have hne (k : s) : ((C k.1).U.1 : Set X).Nonempty :=
      Set.nonempty_coe_sort.mp (C k.1).nonempty
    obtain ⟨x, hx₀, hx⟩ := nonempty_preirreducible_inter
      (C j₀.1).U.1.isOpen (C j.1).U.1.isOpen (hne j₀) (hne j)
    obtain ⟨D, _, hD⟩ := exists_etale_projective_neighborhood g h hbase
      ((C j₀.1).U.1 ⊓ (C j.1).U.1) x ⟨hx₀, hx⟩
    exact ⟨D, hD.trans inf_le_left, hD.trans inf_le_right⟩
  choose D hD₀ hD using hov
  refine ⟨{ ι := s ⊕ s
            finite := inferInstance
            chart := Sum.elim (fun j => C j.1) D
            cover := ?_
            base := Sum.inl j₀
            overlap := fun j => Sum.inr (Sum.elim id id j)
            left := ?_
            right := ?_ }⟩
  · intro x
    obtain ⟨j, hj⟩ := hcover x
    exact ⟨Sum.inl j, hj⟩
  · intro j
    cases j with
    | inl j => exact hD₀ j
    | inr j => exact hD₀ j
  · intro j
    cases j with
    | inl j => exact hD j
    | inr j => exact le_rfl

end

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.BertiniIntegral
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_smooth_integral_projective_hyperplane
    {K : Type} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    {n : ℕ} (X : Scheme) [IsIntegral X] [CompactSpace X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K (Option (Fin n)))) [IsClosedImmersion h]
    (hbase : h ≫ projectiveToSpec = g)
    (q : MvPolynomial (Option (Fin n)) K) (hq : q ≠ 0) :
    ∃ t : Option (Fin n) → K, MvPolynomial.aeval t q ≠ 0 ∧
      IsIntegral (projectiveHyperplane h t).subscheme ∧
      Smooth ((projectiveHyperplane h t).subschemeι ≫ g) := by
  classical
  let A := Classical.choice (exists_finite_etale_projective_atlas g h hbase)
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
  apply smooth_integral_hyperplane_of_etale_atlas X g h hbase
    (fun j => (C j).U) A.cover (fun j => spec_openScalars g (C j).U)
    e (fun j => (C j).φ) (fun j => (C j).factor) (fun j => (C j).κ)
    (fun j => (δ j).symm ((C j).a (a j)))
    (fun j => (δ j).symm ((C j).a (b j))) a b hab ?_ ?_
    A.base A.overlap A.left A.right q hq
  · intro j
    change -(C j).φ (chartCoordinate (C j).coord (δ j ((δ j).symm ((C j).a (a j)))).1) =
      MvPolynomial.eval₂Hom _ _ (MvPolynomial.X (a j))
    rw [Equiv.apply_symm_apply, MvPolynomial.eval₂Hom_X']
  · intro j
    change -(C j).φ (chartCoordinate (C j).coord (δ j ((δ j).symm ((C j).a (b j)))).1) =
      MvPolynomial.eval₂Hom _ _ (MvPolynomial.X (b j))
    rw [Equiv.apply_symm_apply, MvPolynomial.eval₂Hom_X']

end
end MaximalSeshadri.ProjectiveBertini

noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

end
end
end

end OAI
