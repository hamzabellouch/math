import OAI.Analysis.KadisonKastler.TypeIIIPrescribedRank
import OAI.Analysis.KadisonKastler.NormalizedMatrixAveraging
import OAI.Analysis.KadisonKastler.RelativeMatrixCone

namespace OAI

/-! # Faithful positive matrix states with a prescribed projection weight

Rational matrix ranks approximate any weight strictly between zero and
one. This constructs the comparison state used in the local homogeneity
step; proximity of the two whole states is a separate requirement.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

theorem exists_positive_rank_ratio_near (t ε : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hε : 0 < ε) :
    ∃ r s : ℕ, |((r+1 : ℕ) : ℝ) / ((r+s+2 : ℕ) : ℝ) - t| < ε := by
  have hl : max 0 (t-ε) < t := max_lt ht (by linarith)
  have hu : t < min 1 (t+ε) := lt_min ht1 (by linarith)
  obtain ⟨q,hqlo,hqhi⟩ := exists_rat_btwn (hl.trans hu)
  have hq0 : 0 < (q : ℝ) := (le_max_left _ _).trans_lt hqlo
  have hq1 : (q : ℝ) < 1 := hqhi.trans_le (min_le_left _ _)
  have hqn : 0 < q.num := Rat.num_pos.mpr (by exact_mod_cast hq0)
  let n := q.num.toNat
  let d := q.den
  have hn : (n : ℤ) = q.num := Int.toNat_of_nonneg hqn.le
  have hnpos : 0 < n := by exact_mod_cast (hn ▸ hqn)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast q.den_pos
  have hq : (q : ℝ) = (n : ℝ) / d := by
    rw [Rat.cast_def,← hn]
    simp only [Int.cast_natCast]
    rfl
  have hnd : n < d := by
    have h : (n : ℝ) < d := (div_lt_one hdpos).mp (hq ▸ hq1)
    exact_mod_cast h
  refine ⟨n-1,d-n-1,?_⟩
  have he₁ : n-1+1 = n := by omega
  have he₂ : n-1+(d-n-1)+2 = d := by omega
  rw [he₁,he₂,← hq]
  apply abs_lt.mpr
  constructor
  · have h := (le_max_right 0 (t-ε)).trans_lt hqlo
    linarith
  · have h := hqhi.trans_le (min_le_right 1 (t+ε))
    linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem matrixCentralVector_inner_entry (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    {ξ : H} (hξ : ξ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (hnorm : ‖ξ‖ = 1) (i j : ι) :
    inner ℂ ξ ((E.entry i j).val ξ) = if i = j then (Fintype.card ι : ℂ)⁻¹ else 0 := by
  let K := centralVectorSpace (matrixUnitConcreteAlgebra E) J
  have hf : K.starProjection ξ = ξ := Submodule.starProjection_eq_self_iff.mpr hξ
  calc
    inner ℂ ξ ((E.entry i j).val ξ) =
        inner ℂ (K.starProjection ξ) ((E.entry i j).val ξ) := by rw [hf]
    _ = inner ℂ ξ (K.starProjection ((E.entry i j).val ξ)) :=
      K.inner_starProjection_left_eq_right _ _
    _ = _ := by
      rw [centralProjection_matrix_entry E J hJ hright hξ]
      by_cases hij : i = j <;> simp [hij,inner_self_eq_norm_sq_to_K,hnorm]

local instance prescribedMatrixStateRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem TypeIIIFactor.exists_positive_matrix_state_near_projection_weight
    [TopologicalSpace.SeparableSpace H] (hM : TypeIIIFactor M)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ = ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hunit : ‖η‖ = 1) (hsep : Function.Injective (algebraVectorMap M η))
    (p : AlgebraProjection M) (hp0 : p.val ≠ 0) (hp1 : p.val ≠ 1)
    (t ε : ℝ) (ht : 0 < t) (ht1 : t < 1) (hε : 0 < ε) :
    ∃ (r s : ℕ) (E : MatrixUnitSystem (Fin (r+1) ⊕ Fin (s+1)) (Algebra M)) (ζ : H),
      (∑ i, E.entry (Sum.inl i) (Sum.inl i)) = p.val ∧
      ‖ζ‖ = 1 ∧ ζ ∈ modularPositiveCone (M := M) J ξ ∧
      Function.Injective (algebraVectorMap M ζ) ∧ DenseRange (algebraVectorMap M ζ) ∧
      ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J ∧
      |(inner ℂ ζ (p.val.val ζ)).re-t| < ε := by
  obtain ⟨r,s,hrs⟩ := exists_positive_rank_ratio_near t ε ht ht1 hε
  obtain ⟨E,hE⟩ := hM.exists_matrixUnits_prescribed_projection_rank p hp0 hp1 r s
  obtain ⟨ζ,hζn,hζcone,hζsep,hζcyc,hζcentral,_⟩ :=
    exists_positive_matrix_central_unit_vector E J hJ hright hleft ξ hξ hpos hη hunit hsep
  refine ⟨r,s,E,ζ,hE,hζn,hζcone,hζsep,hζcyc,hζcentral,?_⟩
  have he : inner ℂ ζ (p.val.val ζ) =
      (Fintype.card (Fin (r+1) ⊕ Fin (s+1)) : ℂ)⁻¹ * (r+1) := by
    rw [← hE]
    change inner ℂ ζ (M.toStarSubalgebra.subtype
      (∑ i, E.entry (Sum.inl i) (Sum.inl i)) ζ) = _
    rw [map_sum M.toStarSubalgebra.subtype]
    simp only [sum_apply,inner_sum]
    change (∑ i, inner ℂ ζ ((E.entry (Sum.inl i) (Sum.inl i)).val ζ)) = _
    simp only [matrixCentralVector_inner_entry E J hJ hright hζcentral hζn,
      ite_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    push_cast
    ring
  rw [he]
  have hr : ((Fintype.card (Fin (r+1) ⊕ Fin (s+1)) : ℂ)⁻¹ * (r+1)).re =
      ((r+1 : ℕ) : ℝ) / ((r+s+2 : ℕ) : ℝ) := by
    have hcard : Fintype.card (Fin (r+1) ⊕ Fin (s+1)) = r+s+2 := by simp; omega
    rw [hcard]
    have heq : ((r+s+2 : ℕ) : ℂ)⁻¹ * (r+1) =
        (((((r+s+2 : ℕ) : ℝ)⁻¹ * ((r+1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [heq,Complex.ofReal_re]
    ring
  rwa [hr]

end

end KadisonKastler

end OAI
