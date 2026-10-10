import OAI.Analysis.KadisonSimilarity.Representation.DiagonalFiberRepresentations
import OAI.Analysis.KadisonSimilarity.Representation.L2FiniteCopies
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialSymmetryExtraction

namespace OAI

/-! # Matrix norms of the reconstructed diagonal representations

Finite L² sums are identified isometrically with tuple-valued L². The
actual matrix action is pointwise under this identification, so its norm is
exactly the essential supremum of the fiber matrix norms.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A genuine pointwise operator automatically commutes with all measurable
localizations. -/
theorem pointwise_action_commutes_localization
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (R : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (s : Set Ω) (hs : MeasurableSet s) :
    T * l2Localization μ s hs = l2Localization μ s hs * T := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [hR (l2Localization μ s hs f), hR f,
    l2Localization_ae μ s hs f, l2Localization_ae μ s hs (T f)] with a hl ht hf hout
  change T (l2Localization μ s hs f) a = l2Localization μ s hs (T f) a
  rw [hl, hout, hf]
  by_cases ha : a ∈ s
  · simpa only [Set.indicator_of_mem ha] using ht.symm
  · simp only [Set.indicator_of_notMem ha, map_zero]

variable [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

omit [CompleteSpace H] in
/-- The field in any actual all-L² action has precisely the original
operator's scalar norm bounds. -/
theorem pointwise_field_norm_iff
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (R : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (C : ℝ) (hC : 0 ≤ C) :
    ‖T‖ ≤ C ↔ ∀ᵐ a ∂μ, ‖R a‖ ≤ C := by
  constructor
  · intro hTC
    have htest (x : H) : ∀ᵐ a ∂μ, ‖R a x‖ ≤ C * ‖x‖ := by
      have hb := diagonal_commutant_column_bound μ T
        (pointwise_action_commutes_localization μ T R hR) x
      filter_upwards [hb, pointwise_action_column μ T R hR x] with a ha he
      rw [he] at ha
      exact ha.trans (mul_le_mul_of_nonneg_right hTC (norm_nonneg x))
    have hall : ∀ᵐ a ∂μ, ∀ n : ℕ,
        ‖R a (TopologicalSpace.denseSeq H n)‖ ≤ C * ‖TopologicalSpace.denseSeq H n‖ :=
      eventually_countable_forall.mpr fun n => htest (TopologicalSpace.denseSeq H n)
    filter_upwards [hall] with a ha
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro x
    exact (TopologicalSpace.denseRange_denseSeq H).induction_on x
      (isClosed_le (by fun_prop) (by fun_prop)) ha
  · intro hb
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro f
    have hglobal : ∀ᵐ a ∂μ, ‖T f a‖ ≤ C * ‖f a‖ := by
      filter_upwards [hR f, hb] with a ha hn
      rw [ha]
      exact ((R a).le_opNorm _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    calc
      ‖T f‖ ≤ ‖(C : ℂ) • f‖ := by
        apply Lp.norm_le_norm_of_ae_le
        filter_upwards [hglobal, Lp.coeFn_smul (C : ℂ) f] with a ha he
        rw [he, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
        exact ha
      _ = C * ‖f‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]

omit [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
/-- The transported finite matrix acts pointwise by the corresponding
matrix of the actual scalar fields. -/
theorem l2_matrix_action {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (R : Ω → Matrix (Fin n) (Fin n) (H →L[ℂ] H))
    (hR : ∀ (i j : Fin n) (f : Lp H 2 μ),
      ∀ᵐ a ∂μ, X i j f a = R a i j (f a))
    (f : Lp (HilbertCopies H n) 2 μ) :
    ∀ᵐ a ∂μ, (l2FiniteCopiesEquiv (H := H) μ n).conjStarAlgEquiv (matrixOperator X) f a =
      matrixOperator (R a) (f a) := by
  let U := l2FiniteCopiesEquiv (H := H) μ n
  let x := U.symm f
  have hsums : ∀ᵐ a ∂μ, ∀ i : Fin n,
      (∑ j : Fin n, X i j (x j)) a = ∑ j : Fin n, X i j (x j) a :=
    eventually_countable_forall.mpr fun i =>
      (Lp.coeFn_finsetSum Finset.univ (fun j => X i j (x j))).mono fun a ha => by
        simpa only [Finset.sum_apply] using ha
  have hentries : ∀ᵐ a ∂μ, ∀ i j : Fin n, X i j (x j) a = R a i j (x j a) :=
    eventually_countable_forall.mpr fun i => eventually_countable_forall.mpr fun j => hR i j (x j)
  filter_upwards [l2FiniteCopiesEquiv_ae μ (matrixOperator X x),
    l2FiniteCopiesEquiv_ae μ x, hsums, hentries] with a hout hx hsum he
  ext i
  change U (matrixOperator X x) a i = _
  rw [hout i, matrixOperator_apply, hsum i, matrixOperator_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [he i j]
  have hj : f a j = x j a := by simpa only [x, U, LinearIsometryEquiv.apply_symm_apply] using hx j
  rw [hj]

/-- Matrix norms are preserved exactly by the actual pointwise fields. -/
theorem diagonal_matrix_norm_iff {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (R : Ω → Matrix (Fin n) (Fin n) (H →L[ℂ] H))
    (hR : ∀ (i j : Fin n) (f : Lp H 2 μ),
      ∀ᵐ a ∂μ, X i j f a = R a i j (f a)) (C : ℝ) (hC : 0 ≤ C) :
    ‖matrixOperator X‖ ≤ C ↔ ∀ᵐ a ∂μ, ‖matrixOperator (R a)‖ ≤ C := by
  have hnorm : ‖(l2FiniteCopiesEquiv (H := H) μ n).conjStarAlgEquiv (matrixOperator X)‖ =
      ‖matrixOperator X‖ :=
    NonUnitalStarAlgHom.norm_map (l2FiniteCopiesEquiv (H := H) μ n).conjStarAlgEquiv
      (l2FiniteCopiesEquiv (H := H) μ n).conjStarAlgEquiv.injective _
  rw [← hnorm]
  exact pointwise_field_norm_iff μ _ _ (l2_matrix_action μ X R hR) C hC

variable {A : Type*} [CStarAlgebra A]

/-- The matrix norm field on a conull base is the entrywise matrix of the
genuine fiber representations, with no additional matrix-norm input. -/
theorem conull_representation_matrix_norm_iff
    (σ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (s : Set Ω) (hsm : MeasurableSet s) (hsnull : μ sᶜ = 0)
    (ρ : ∀ _a : s, A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (haction : ∀ (b : A) (f : Lp H 2 μ),
      ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, σ b f a = ρ a b (f a))
    {n : ℕ} (X : CStarMatrix (Fin n) (Fin n) A) (C : ℝ) (hC : 0 ≤ C) :
    ‖representedMatrix σ X‖ ≤ C ↔
      ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, ‖representedMatrix (ρ a) X‖ ≤ C := by
  classical
  let R : Ω → Matrix (Fin n) (Fin n) (H →L[ℂ] H) :=
    fun a i j => if ha : a ∈ s then ρ ⟨a, ha⟩ (X i j) else 0
  have hs : ∀ᵐ a ∂μ, a ∈ s := mem_ae_iff.mpr hsnull
  have hR (i j : Fin n) (f : Lp H 2 μ) :
      ∀ᵐ a ∂μ, σ (X i j) f a = R a i j (f a) := by
    have hr : ∀ᵐ a ∂μ.restrict s, σ (X i j) f a = R a i j (f a) := by
      apply (ae_restrict_iff_subtype hsm).mpr
      filter_upwards [haction (X i j) f] with a ha
      simpa only [R, dite_eq_left a.property, representedMatrix] using ha
    filter_upwards [hs, (ae_restrict_iff' hsm).mp hr] with a ha h
    exact h ha
  have hnorm := diagonal_matrix_norm_iff μ (fun i j => σ (X i j)) R hR C hC
  change ‖matrixOperator (fun i j => σ (X i j))‖ ≤ C ↔ _
  rw [hnorm]
  constructor
  · intro h
    have hr := (ae_restrict_iff_subtype hsm).mp (ae_restrict_of_ae h)
    filter_upwards [hr] with a ha
    simpa only [R, dite_eq_left a.property, representedMatrix] using ha
  · intro h
    have hr : ∀ᵐ a ∂μ.restrict s, ‖matrixOperator (R a)‖ ≤ C := by
      apply (ae_restrict_iff_subtype hsm).mpr
      filter_upwards [h] with a ha
      simpa only [R, dite_eq_left a.property, representedMatrix] using ha
    filter_upwards [hs, (ae_restrict_iff' hsm).mp hr] with a ha h
    exact h ha

/-- The constructive diagonal decomposition supplies both scalar and all
finite matrix norm equivalences on the same conull family of representations. -/
theorem exists_conull_diagonal_representations_with_matrices
    [TopologicalSpace.SeparableSpace A]
    (σ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (hσ : ∀ (b : A) (r : Set Ω) (hr : MeasurableSet r),
      σ b * l2Localization μ r hr = l2Localization μ r hr * σ b) :
    ∃ s : Set Ω, MeasurableSet s ∧ μ sᶜ = 0 ∧
      ∃ ρ : ∀ _a : s, A →⋆ₐ[ℂ] (H →L[ℂ] H),
        (∀ (b : A) (f : Lp H 2 μ),
          ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ,
            σ b f a = ρ a b (f a)) ∧
        (∀ (b : A) (C : ℝ), 0 ≤ C →
          (‖σ b‖ ≤ C ↔ ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, ‖ρ a b‖ ≤ C)) ∧
        ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) (C : ℝ), 0 ≤ C →
          (‖representedMatrix σ X‖ ≤ C ↔
            ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, ‖representedMatrix (ρ a) X‖ ≤ C) := by
  obtain ⟨s, hsm, hsnull, ρ, haction, hscalar⟩ :=
    exists_conull_diagonal_star_representations μ σ hσ
  refine ⟨s, hsm, hsnull, ρ, haction, hscalar, ?_⟩
  intro n X C hC
  exact conull_representation_matrix_norm_iff μ σ s hsm hsnull ρ haction X C hC

end KadisonSimilarity

end

end OAI
