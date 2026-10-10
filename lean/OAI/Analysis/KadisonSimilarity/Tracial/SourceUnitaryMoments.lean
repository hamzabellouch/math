import OAI.Analysis.KadisonSimilarity.Tracial.SourceMomentConstruction

namespace OAI

/-! Completing the source partial unitary controls every prescribed finite
family of ambient mixed moments. -/

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
/-- A unitary in the source makes any finite family of centered ambient
mixed moments arbitrarily small. -/
theorem exists_source_unitary_small_moments {I : Type*} [Fintype I]
    (F : I → M.toStarSubalgebra)
    (hF : ∀ i, ‖F i‖ ≤ 1) (hFτ : ∀ i, υ.trace (F i) = 0)
    {K N : ℕ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : unitary R.toStarSubalgebra, ∀ a : BoundedWord I K N,
      admissibleTail a.2.val →
        ‖υ.trace (mixedEval F (SourcePartialUnitary.map (coordinateInclusion hRM)
          (asPartialUnitary u)) a.1 a.2.val)‖ < ε := by
  let φ := coordinateInclusion hRM
  let τ := vectorPositiveFunctional M υ.vector
  let t : ℝ := min (1 / 2) (ε / (4 * ((N : ℝ) + 1)))
  have ht0 : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have htε : t ≤ ε / (4 * ((N : ℝ) + 1)) := min_le_right _ _
  let T : ℝ := 1 - t
  have hT0 : 0 ≤ T := by dsimp only [T]; linarith
  have hT : T < 1 := by dsimp only [T]; linarith
  let C := patchRate (N : ℝ) T
  let δ := ε / (4 * Real.exp (C * T))
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) (Real.exp_pos _))
  obtain ⟨v, hvs, hvm⟩ := exists_source_partial_unitary_moments υ hRM hfactor hdiff hirr
    F hF hFτ hK (N := N) hδ hT0 hT
  let w := ofCornerUnitary (1 - v.support) v.support_proj.one_sub 1
  have hw : w.support = 1 - v.support := ofCornerUnitary_support ..
  have horth : v.support * w.support = 0 := by
    rw [hw, mul_sub, mul_one, v.support_proj.isIdempotentElem.eq, sub_self]
  let V := SourcePartialUnitary.map φ v
  let W := SourcePartialUnitary.map φ w
  have horthM : V.support * W.support = 0 := by
    rw [SourcePartialUnitary.support_map, SourcePartialUnitary.support_map,
      ← map_mul, horth, map_zero]
  have hwt : (τ W.support).re = t := by
    rw [SourcePartialUnitary.support_map, hw, map_sub, map_one]
    change (υ.trace (1 - φ v.support)).re = t
    rw [trace_sub, υ.trace_one, Complex.sub_re, Complex.one_re, hvs]
    dsimp only [T]
    ring
  have he : asPartialUnitary (unitaryCompletion v) = v.orthogonalSum w horth := by
    apply HochschildComparison.PartialUnitary.ext
    rfl
  refine ⟨unitaryCompletion v, fun a ha => ?_⟩
  rw [he, SourcePartialUnitary.map_orthogonalSum]
  change ‖τ (mixedEval F (V.orthogonalSum W horthM) a.1 a.2.val)‖ < ε
  have herr := trace_mixedEval_patch τ υ.trace_mul_comm F V W horthM hF a.1 a.2.val
  rw [hwt] at herr
  have hvb := hvm a ha
  change ‖τ (mixedEval F V a.1 a.2.val)‖ ≤
    expBudget δ (patchRate N T) (υ.trace (φ v.support)).re at hvb
  rw [hvs] at hvb
  have hb : expBudget δ (patchRate N T) T ≤ ε / 4 := by
    change δ * (Real.exp (C * T) - 1) ≤ ε / 4
    have heq : δ * Real.exp (C * T) = ε / 4 := by dsimp only [δ]; field_simp
    nlinarith
  have hn : (a.2.val.length : ℝ) * t ≤ ε / 4 := by
    have hnN : (a.2.val.length : ℝ) ≤ (N : ℝ) + 1 := by
      exact_mod_cast (a.2.property.trans (Nat.le_succ N))
    have hnt := mul_le_mul_of_nonneg_right hnN ht0.le
    have hpos : 0 < 4 * ((N : ℝ) + 1) := by positivity
    have hbound := (le_div_iff₀ hpos).mp htε
    nlinarith
  have htotal : ‖τ (mixedEval F (V.orthogonalSum W horthM) a.1 a.2.val)‖ ≤ ε / 2 := by
    calc
      _ ≤ ‖τ (mixedEval F (V.orthogonalSum W horthM) a.1 a.2.val) -
          τ (mixedEval F V a.1 a.2.val)‖ + ‖τ (mixedEval F V a.1 a.2.val)‖ := by
        simpa only [sub_add_cancel] using norm_add_le
          (τ (mixedEval F (V.orthogonalSum W horthM) a.1 a.2.val) - τ (mixedEval F V a.1 a.2.val))
          (τ (mixedEval F V a.1 a.2.val))
      _ ≤ ε / 4 + ε / 4 := add_le_add (herr.trans hn) (hvb.trans hb)
      _ = _ := by ring
  exact htotal.trans_lt (by linarith)

end KadisonSimilarity

end

end OAI
