import OAI.Analysis.KadisonSimilarity.Tracial.SourceCornerQuantization
import OAI.Analysis.KadisonSimilarity.Tracial.SourcePartialUnitaries

namespace OAI

/-! Incremental moment patches chosen inside a prescribed irreducible source. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open HochschildComparison HochschildPatching BoundedHochschild
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {R M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hRM : R ≤ M)
  (hfactor : ∀ c : R.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : R.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : R.toStarSubalgebra, coordinateInclusion hRM a * c =
      c * coordinateInclusion hRM a) → ∃ z : ℂ, c = z • 1)

include hfactor hdiff hirr in
/-- The mixed-word patch is an extension in the source algebra, even though
all coefficients and estimates belong to the larger ambient algebra. -/
theorem exists_source_incremental_patch {I : Type*} [Fintype I]
    (F : I → M.toStarSubalgebra)
    (hF : ∀ i, ‖F i‖ ≤ 1) (hFτ : ∀ i, υ.trace (F i) = 0)
    {K N : ℕ} (hK : 0 < K) {b : ℝ → ℝ} (v : PartialUnitary R.toStarSubalgebra)
    (hb : 0 ≤ b ((υ.trace (coordinateInclusion hRM v.support)).re))
    (hv : MomentBound F (vectorPositiveFunctional M υ.vector) (K := K) (N := N) b
      (SourcePartialUnitary.map (coordinateInclusion hRM) v))
    (hs : (υ.trace (coordinateInclusion hRM v.support)).re < 1)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ w : PartialUnitary R.toStarSubalgebra, ∃ h : v.support * w.support = 0,
      0 < (υ.trace (coordinateInclusion hRM w.support)).re ∧
      (υ.trace (coordinateInclusion hRM w.support)).re < η ∧
      ∀ a : BoundedWord I K N, admissibleTail a.2.val →
        ‖υ.trace (mixedEval F
          (SourcePartialUnitary.map (coordinateInclusion hRM) (v.orthogonalSum w h))
          a.1 a.2.val)‖ ≤ b ((υ.trace (coordinateInclusion hRM v.support)).re) +
          ((N : ℝ) * ε + (N : ℝ)^2 *
            (ε + 2 * b ((υ.trace (coordinateInclusion hRM v.support)).re) /
              (1 - (υ.trace (coordinateInclusion hRM v.support)).re))) *
            (υ.trace (coordinateInclusion hRM w.support)).re := by
  let φ := coordinateInclusion hRM
  let τ := vectorPositiveFunctional M υ.vector
  let V := SourcePartialUnitary.map φ v
  have hVs : V.support = φ v.support := SourcePartialUnitary.support_map φ v
  have hφp : φ (1 - v.support) = 1 - V.support := by rw [map_sub, map_one, hVs]
  have hpt : (τ (φ (1 - v.support))).re = 1 - (υ.trace (φ v.support)).re := by
    rw [map_sub, map_one]
    change (υ.trace (1 - φ v.support)).re = _
    rw [trace_sub, υ.trace_one, Complex.sub_re, Complex.one_re]
  have hp : 0 < (τ (1 - V.support)).re := by rw [← hφp, hpt]; linarith
  have hp0 : 1 - v.support ≠ 0 := by
    intro he
    have ht : 0 < (τ (φ (1 - v.support))).re := by rwa [hφp]
    rw [he, map_zero, map_zero, Complex.zero_re] at ht
    exact lt_irrefl _ ht
  obtain ⟨q, hq, hqv, hq0, hqt, hqsmall⟩ := exists_source_relative_small_corner
    υ hRM hfactor hdiff hirr (1 - v.support) v.support_proj.one_sub hp0
    (fun a : BoundedWord I K N => mixedEval F V a.1 a.2.val) (sq_pos_of_pos hε) hη
  obtain ⟨w, hw, hweak⟩ := exists_source_partial_unitary_weak_powers
    υ hRM hfactor hdiff q hq hq0 (linearCoeff F V (K := K) (N := N)) linearPower hε
  have horth : v.support * w.support = 0 := by
    rw [hw]
    have hh := (hq.le_iff_mul_eq_right v.support_proj.one_sub).mp hqv
    rw [sub_mul, one_mul, sub_eq_self] at hh
    exact hh
  let W := SourcePartialUnitary.map φ w
  have hWs : W.support = φ q := by rw [SourcePartialUnitary.support_map, hw]
  have horthM : V.support * W.support = 0 := by
    rw [hVs, SourcePartialUnitary.support_map, ← map_mul, horth, map_zero]
  have hwpos : 0 < (υ.trace (φ w.support)).re := by
    rw [hw]
    exact HochschildDiffuse.projection_trace_pos τ
      (fun a ha => υ.separating a (inner_self_eq_zero.mp ((baseVector_inner_trace υ a a).trans ha)))
      (hq.map φ) (fun h => hq0 (Subtype.ext (congrArg
        (fun a : M.toStarSubalgebra => (a : H →L[ℂ] H)) h)))
  refine ⟨w, horth, hwpos, by rwa [hw], fun a ha => ?_⟩
  have hsmall : ∀ z : BoundedWord I K N,
      ‖τ.toPreGNS (W.support * mixedEval F V z.1 z.2.val * W.support -
        residualScalar τ V (mixedEval F V z.1 z.2.val) • W.support)‖ ≤
        ε * ‖τ.toPreGNS W.support‖ := by
    intro z
    rw [hWs]
    apply le_of_sq_le_sq _ (mul_nonneg hε.le (norm_nonneg _))
    rw [mul_pow, projection_gns_sq τ (hq.map φ)]
    apply le_of_lt
    change ‖τ.toPreGNS (φ q * mixedEval F V z.1 z.2.val * φ q -
      residualScalar τ V (mixedEval F V z.1 z.2.val) • φ q)‖ ^ 2 < ε ^ 2 * (τ (φ q)).re
    rw [residualScalar, ← hφp]
    exact hqsmall z
  have hlin := linear_trace_bound F τ υ.trace_mul_comm V W a.1 a.2.val a.2.property
    (ε * (τ W.support).re) (fun j => by
      rw [hWs]
      rw [show W.power (linearPower j) = φ (w.power (linearPower j)) from
        SourcePartialUnitary.power_map φ w (linearPower j)]
      change ‖υ.trace (linearCoeff F V j * φ (w.power (linearPower j)))‖ ≤
        ε * (υ.trace (φ q)).re
      exact (hweak j).le)
  have hquad := quadratic_trace_bound F τ υ.trace_mul_comm V W horthM hK hF hFτ
    hb hv hp ε hsmall a.1 a.2.val a.2.property ha
  have hh := mixedEval_patch_bound F τ V W horthM a.1 a.2.val a.2.property
    (mul_nonneg hε.le hwpos.le)
    (mul_nonneg (add_nonneg hε.le (div_nonneg (mul_nonneg (by norm_num) hb) hp.le)) hwpos.le)
    hlin hquad
  have hpt' : (τ (1 - V.support)).re = 1 - (υ.trace (φ v.support)).re := by
    rw [← hφp, hpt]
  rw [hpt'] at hh
  rw [SourcePartialUnitary.map_orthogonalSum]
  change ‖τ (mixedEval F (V.orthogonalSum W horthM) a.1 a.2.val)‖ ≤ _
  calc
    _ ≤ ‖τ (mixedEval F V a.1 a.2.val)‖ + (N : ℝ) * (ε * (τ W.support).re) +
        (N : ℝ)^2 * ((ε + 2 * b ((υ.trace (φ v.support)).re) /
          (1 - (υ.trace (φ v.support)).re)) * (τ W.support).re) := hh
    _ ≤ b ((υ.trace (φ v.support)).re) + (N : ℝ) * (ε * (τ W.support).re) +
        (N : ℝ)^2 * ((ε + 2 * b ((υ.trace (φ v.support)).re) /
          (1 - (υ.trace (φ v.support)).re)) * (τ W.support).re) :=
      add_le_add (add_le_add (hv a ha) le_rfl) le_rfl
    _ = _ := by
      rw [SourcePartialUnitary.support_map]
      change b ((υ.trace (φ v.support)).re) + (N : ℝ) * (ε * (υ.trace (φ w.support)).re) +
        (N : ℝ)^2 * ((ε + 2 * b ((υ.trace (φ v.support)).re) /
          (1 - (υ.trace (φ v.support)).re)) * (υ.trace (φ w.support)).re) = _
      ring

end KadisonSimilarity

end

end OAI
