import OAI.Analysis.KadisonKastler.UniformInfinitesimalBound

namespace OAI

/-! # The unit-ball defect in the infinitesimal normalizer estimate -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def commutatorRangeError (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) : ℝ :=
  sSup ((fun x : Algebra M =>
    Metric.infDist (commutatorAlong M.toStarSubalgebra.subtype T x) (M : Set (H →L[ℂ] H))) ''
      {x | ‖x‖ ≤ 1})

theorem commutatorRangeError_bddAbove (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    BddAbove ((fun x : Algebra M =>
      Metric.infDist (commutatorAlong M.toStarSubalgebra.subtype T x) (M : Set (H →L[ℂ] H))) ''
        {x | ‖x‖ ≤ 1}) := by
  refine ⟨2 * ‖T‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  calc
    _ ≤ dist (commutatorAlong M.toStarSubalgebra.subtype T x) 0 :=
      Metric.infDist_le_dist_of_mem M.zero_mem
    _ = ‖T * x.val - x.val * T‖ := by rw [dist_zero_right, commutatorAlong_apply]; rfl
    _ ≤ ‖T‖ * ‖x‖ + ‖x‖ * ‖T‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ 2 * ‖T‖ := by
      have hx' : ‖x‖ ≤ 1 := hx
      nlinarith [norm_nonneg T, norm_nonneg x]

theorem commutatorRangeError_nonneg (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    0 ≤ commutatorRangeError M T := by
  exact Metric.infDist_nonneg.trans (le_csSup (commutatorRangeError_bddAbove M T)
    ⟨0, by simp, rfl⟩)

theorem commutatorRangeError_bounds_unitBall (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (x : Algebra M) (hx : ‖x‖ ≤ 1) :
    Metric.infDist (commutatorAlong M.toStarSubalgebra.subtype T x) (M : Set (H →L[ℂ] H)) ≤
      commutatorRangeError M T :=
  le_csSup (commutatorRangeError_bddAbove M T) ⟨x, hx, rfl⟩

theorem commutator_approximation_of_rangeError_lt (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) {δ : ℝ} (hδ : commutatorRangeError M T < δ) :
    ∀ x : Algebra M, ∃ y : Algebra M,
      ‖T * x.val - x.val * T - y.val‖ ≤ δ * ‖x‖ := by
  intro x
  by_cases hx : x = 0
  · subst x
    exact ⟨0, by simp⟩
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let u : Algebra M := (‖x‖⁻¹ : ℂ) • x
  have hu : ‖u‖ ≤ 1 := by
    dsimp [u]
    rw [norm_smul]
    change ‖((‖x‖ : ℂ)⁻¹)‖ * ‖x‖ ≤ 1
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hxpos, inv_mul_cancel₀ hxpos.ne']
  have hdist := (commutatorRangeError_bounds_unitBall M T u hu).trans_lt hδ
  obtain ⟨y, hy, hnear⟩ := (Metric.infDist_lt_iff (show (M : Set (H →L[ℂ] H)).Nonempty from
    ⟨0, M.zero_mem⟩)).mp hdist
  refine ⟨(‖x‖ : ℂ) • (⟨y, hy⟩ : Algebra M), ?_⟩
  let D := commutatorAlong M.toStarSubalgebra.subtype T
  have hxu : (‖x‖ : ℂ) • u = x := by
    change (‖x‖ : ℂ) • ((‖x‖ : ℂ)⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hxpos.ne'), one_smul]
  have he : D x - (‖x‖ : ℂ) • y = (‖x‖ : ℂ) • (D u - y) := by
    calc
      D x - (‖x‖ : ℂ) • y = D ((‖x‖ : ℂ) • u) - (‖x‖ : ℂ) • y := by rw [hxu]
      _ = (‖x‖ : ℂ) • (D u - y) := by rw [map_smul, smul_sub]
  change ‖D x - (‖x‖ : ℂ) • y‖ ≤ _
  rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
  have hnear' : ‖D u - y‖ < δ := by simpa only [dist_eq_norm] using hnear
  nlinarith

universe u

local instance rangeErrorSourceOrder (P : MatrixTypeIIIFactorModel.{u}) :
    PartialOrder (Algebra P.M) := CStarAlgebra.spectralOrder _
local instance rangeErrorSourceStarOrder (P : MatrixTypeIIIFactorModel.{u}) :
    StarOrderedRing (Algebra P.M) := CStarAlgebra.spectralOrderedRing _

theorem uniform_typeIII_selfAdjoint_infinitesimal_estimate
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ P : MatrixTypeIIIFactorModel.{u},
      PublishedBlockCommutantApproximation (Algebra P.M) P.H) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : MatrixTypeIIIFactorModel.{u},
      ∀ T : P.H →L[ℂ] P.H, IsSelfAdjoint T →
        Metric.infDist T (selfAdjointAlgebraCommutantSum P.M) ≤ C * commutatorRangeError P.M T := by
  obtain ⟨C, hC, hbound⟩ := uniform_typeIII_infinitesimal_bound hSpectral hCompare hSakai hDistance
  refine ⟨C, hC, fun P T hT => ?_⟩
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  have hδ : commutatorRangeError P.M T < r / C :=
    (lt_div_iff₀ hC).mpr (by nlinarith)
  have h := hbound P T hT (r / C) ((commutatorRangeError_nonneg P.M T).trans hδ.le)
    (commutator_approximation_of_rangeError_lt P.M T hδ)
  exact h.trans_eq (by field_simp)

theorem uniform_typeIII_infinitesimal_estimate
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ P : MatrixTypeIIIFactorModel.{u},
      PublishedBlockCommutantApproximation (Algebra P.M) P.H) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : MatrixTypeIIIFactorModel.{u},
      ∀ T : P.H →L[ℂ] P.H, IsSelfAdjoint T →
        Metric.infDist T (algebraCommutantSum P.M) ≤ C * commutatorRangeError P.M T := by
  obtain ⟨C, hC, hbound⟩ :=
    uniform_typeIII_selfAdjoint_infinitesimal_estimate hSpectral hCompare hSakai hDistance
  refine ⟨C, hC, fun P T hT => ?_⟩
  exact (Metric.infDist_le_infDist_of_subset (x := T)
    (selfAdjointAlgebraCommutantSum_subset P.M)
    ⟨0, selfAdjointAlgebraCommutantSum_zero P.M⟩).trans (hbound P T hT)

end

end KadisonKastler

end OAI
