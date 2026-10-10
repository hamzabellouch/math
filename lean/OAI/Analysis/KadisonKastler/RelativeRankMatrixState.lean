import OAI.Analysis.KadisonKastler.PrescribedMatrixState
import OAI.Analysis.KadisonKastler.RelativeMatrixCentralExtension
import OAI.Analysis.KadisonKastler.RelativeUnitaryStateDefect

namespace OAI

/-! # Prescribed-rank positive states inside a matrix relative commutant

The comparison matrix stays in the relative algebra. Averaging over
its product with the initial matrix algebra produces a faithful positive
vector central for both algebras on the original Hilbert space.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

private theorem rank_projection_weight
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    {r s : ℕ} (F : MatrixUnitSystem (Fin (r+1) ⊕ Fin (s+1)) (Algebra M))
    (p : AlgebraProjection M) (hp : (∑ i, F.entry (Sum.inl i) (Sum.inl i))=p.val)
    (ζ : H) (hnorm : ‖ζ‖=1)
    (hcentral : ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra F) J) :
    (inner ℂ ζ (p.val.val ζ)).re=((r+1:ℕ):ℝ)/((r+s+2:ℕ):ℝ) := by
  have he : inner ℂ ζ (p.val.val ζ) =
      (Fintype.card (Fin (r+1) ⊕ Fin (s+1)) : ℂ)⁻¹*(r+1) := by
    rw [← hp]
    change inner ℂ ζ (M.toStarSubalgebra.subtype
      (∑ i, F.entry (Sum.inl i) (Sum.inl i)) ζ) = _
    rw [map_sum M.toStarSubalgebra.subtype]
    simp only [sum_apply,inner_sum]
    change (∑ i, inner ℂ ζ ((F.entry (Sum.inl i) (Sum.inl i)).val ζ)) = _
    simp only [matrixCentralVector_inner_entry F J hJ hright hcentral hnorm,
      ite_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    push_cast
    ring
  rw [he]
  have hcard : Fintype.card (Fin (r+1) ⊕ Fin (s+1))=r+s+2 := by simp; omega
  rw [hcard]
  have heq : ((r+s+2:ℕ):ℂ)⁻¹*(r+1)=
      (((((r+s+2:ℕ):ℝ)⁻¹*((r+1:ℕ):ℝ)):ℝ):ℂ) := by
    push_cast
    rfl
  rw [heq,Complex.ofReal_re]
  ring

local instance relativeRankRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem TypeIIIFactor.exists_relative_positive_matrix_state_near_weight
    [TopologicalSpace.SeparableSpace H] (hM : TypeIIIFactor M)
    (E : FiniteMatrixStage M)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hunit : ‖η‖=1) (hsep : Function.Injective (algebraVectorMap M η))
    (p : AlgebraProjection E.units.relativeVonNeumann) (hp0 : p.val≠0) (hp1 : p.val≠1)
    (t ε : ℝ) (ht : 0 < t) (ht1 : t < 1) (hε : 0 < ε) :
    ∃ (r s : ℕ)
      (F : MatrixUnitSystem (Fin (r+1) ⊕ Fin (s+1)) (Algebra E.units.relativeVonNeumann))
      (ζ : H), (∑ i, F.entry (Sum.inl i) (Sum.inl i))=p.val ∧
      ‖ζ‖=1 ∧ ζ ∈ modularPositiveCone (M := M) J ξ ∧
      Function.Injective (algebraVectorMap M ζ) ∧
      ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) J ∧
      ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra F) J ∧
      |(inner ℂ ζ (p.val.val ζ)).re-t| < ε := by
  classical
  obtain ⟨r,s,hrs⟩ := exists_positive_rank_ratio_near t ε ht ht1 hε
  obtain ⟨F,hF⟩ := (hM.relative_matrix E).exists_matrixUnits_prescribed_projection_rank
    p hp0 hp1 r s
  let e : Fin (Fintype.card (Fin (r+1) ⊕ Fin (s+1))) ≃
      (Fin (r+1) ⊕ Fin (s+1)) := (Fintype.equivFin _).symm
  let G : FiniteMatrixStage E.units.relativeVonNeumann :=
    ⟨Fintype.card _,Fintype.card_pos,F.reindex e⟩
  let K := relativeMatrixExtension E G
  let : Nonempty (Fin K.size) := ⟨⟨0,K.positive⟩⟩
  obtain ⟨ζ,hζn,hζcone,hζsep,_,hζK,_⟩ := exists_positive_matrix_central_unit_vector
    K.units J hJ hright hleft ξ hξ hpos hη hunit hsep
  have hleE : matrixUnitConcreteAlgebra E.units ≤ matrixUnitConcreteAlgebra K.units :=
    fun _ ha => relativeMatrixExtension_contains_left E G ha
  have hleG : matrixUnitConcreteAlgebra G.units ≤ matrixUnitConcreteAlgebra K.units :=
    fun _ ha => relativeMatrixExtension_contains_right E G ha
  have hζE := centralVectorSpace_antitone hleE J hζK
  have hζG := centralVectorSpace_antitone hleG J hζK
  have hζF : ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra F) J := by
    apply (mem_centralVectorSpace_matrix_iff F J ζ).mpr
    intro i j
    have h := (mem_centralVectorSpace_matrix_iff G.units J ζ).mp hζG (e.symm i) (e.symm j)
    change (F.entry (e (e.symm i)) (e (e.symm j))).val ζ =
      conjugationOperator J (star (F.entry (e (e.symm i)) (e (e.symm j)))).val ζ at h
    simpa only [Equiv.apply_symm_apply,StarMemClass.coe_star] using h
  refine ⟨r,s,F,ζ,hF,hζn,hζcone,hζsep,hζE,hζF,?_⟩
  rw [rank_projection_weight J hJ (relative_conjugation_mem_commutant E.units J hright)
    F p hF ζ hζn hζF]
  exact hrs

end

end KadisonKastler

end OAI
