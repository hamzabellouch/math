import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFacetSupportedAgreement
import OAI.GroupTheory.PolycyclicRecognition.Analysis.GoodSheetProfileAgreement

namespace OAI

/-! # Contact-facet equality for the diagonal's nonempty good sheets -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology NNReal

variable {EG G W A I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)

include T in
/-- At a facet, even good sets of vanishing relative mass force equality of
the two limiting affine values. Their nonemptiness suffices for this step. -/
theorem good_word_profiles_agree_on_facet
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (X : I → H) (words : Finset (FreeMagma I)) (β : WordBasisSelections X words)
    (z : Fin (finrank ℝ H) → ℝ) (i : Fin M.letterCount)
    (scale R η t : ℕ → ℝ)
    (hscale : Tendsto scale atTop atTop) (hscale1 : ∀ n, 1 ≤ scale n)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R)
    (hη : Tendsto η atTop (𝓝 0))
    (ht : ∀ n, |t n| ≤ R n * Real.exp
      ((M.weight i ((WordBasisSelections.basis X words β).equivFun.symm z) + η n) * scale n))
    {K : ℝ≥0} (J : ℕ → G → W) (hJ : ∀ n, LipschitzWith K (J n))
    (x : ℕ → G) (k : ℕ → A → G)
    (Good : ℕ → Set A) (hne : ∀ n, (Good n).Nonempty)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (f g : W)
    (happrox : ∀ᶠ n in atTop, ∀ a ∈ Good n,
      ‖rescaledMapProfile (J n) (x n) (k n a) (Real.log (scale n))
        (fun v => Exp (wordChartPivot X words β (scale n) v : H)) z - f‖ ≤ ε n ∧
      ‖rescaledMapProfile (J n) (x n)
        (k n a * Exp (t n • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (Real.log (scale n)) (fun v => Exp (wordChartPivot X words β (scale n) v : H)) z - g‖ ≤ ε n) :
    f = g := by
  obtain ⟨B, d, hB, hpos⟩ := wordChartPivot_polynomial_bound X words β (finBasis ℝ H) z
  let RH := fun n => (B + 1) * (1 + scale n) ^ d
  have hRH0 : ∀ n, 0 ≤ RH n := fun n =>
    mul_nonneg (by linarith) (pow_nonneg (by linarith [hscale1 n]) _)
  have hRH : HasSubexponentialUpperBoundSeq scale RH :=
    (subexponential_upper_polynomial (by linarith : 0 < B + 1) d).along_sequence hscale
  have hq n : ‖(finBasis ℝ H).equivFun (wordChartPivot X words β (scale n) z)‖ ≤ RH n :=
    (hpos _ (hscale1 n)).trans (by
      dsimp only [RH]
      exact mul_le_mul_of_nonneg_right (by linarith)
        (pow_nonneg (by linarith [hscale1 n]) _))
  let χ : H →ₗ[ℝ] ℝ := (cartanHeightWeight T H (M.weight i)).comp
    ((heightProjection T.character).comp H.subtype)
  have hχ (h : H) : χ h = M.weight i h := cartanHeightWeight_projection T H (M.weight i) h
  have hbr (h k : H) : χ ⁅h, k⁆ = 0 := by
    change cartanHeightWeight T H (M.weight i)
      (heightProjection T.character (⁅h, k⁆ : H)) = 0
    rw [LieSubalgebra.coe_bracket, T.height_lie, map_zero]
  have hfacet n : M.weight i (wordChartPivot X words β (scale n) z) =
      M.weight i ((WordBasisSelections.basis X words β).equivFun.symm z) * scale n := by
    simpa only [hχ, smul_eq_mul, mul_comm] using
      wordChartPivot_height X words β χ hbr (hscale1 n) z
  apply good_sheet_profile_values_eq J hJ scale
    (fun n => lt_of_lt_of_le zero_lt_one (hscale1 n)) x k
    (fun n a => k n a * Exp (t n • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (fun n v => Exp (wordChartPivot X words β (scale n) v : H)) z Good hne ε hε f g happrox
  intro τ hτ
  filter_upwards [facet_root_switch_sublinear T H (M.weight i) (M.weight_nonzero i)
    Exp hExp realize ⟨M.letter i, M.letter_root i⟩ scale RH R η
    (M.weight i ((WordBasisSelections.basis X words β).equivFun.symm z))
    hscale (fun n => le_trans zero_le_one (hscale1 n)) hRH0 hR0 hRH hR hη τ hτ] with n hn
  intro a _
  simpa only [mul_assoc] using hn (x n * k n a)
    (wordChartPivot X words β (scale n) z) (t n) (hq n) (hfacet n) (ht n)

end PolycyclicRecognition.CartanWordModel

end

end OAI
