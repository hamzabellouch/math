import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSheetAgreement
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FacetPivotBridgeRate
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordChartPivot

namespace OAI

/-! # Contact-facet equality in the support of the actual joint law -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology NNReal

variable {EG G W Z A : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace Z] [LocallyCompactSpace Z] [MeasurableSpace A]

theorem supported_profiles_agree_on_contact_facet
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (v : rootSpace H χ) (scale RH R η t : ℕ → ℝ) (s : ℝ)
    (hs : Tendsto scale atTop atTop) (hscale : ∀ n, 0 < scale n)
    (hRH0 : ∀ n, 0 ≤ RH n) (hR0 : ∀ n, 0 ≤ R n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hR : HasSubexponentialUpperBoundSeq scale R) (hη : Tendsto η atTop (𝓝 0))
    (ht : ∀ n, |t n| ≤ R n * Real.exp ((s + η n) * scale n))
    (chart : ℕ → Z → G) (z : Z) (q : ℕ → H)
    (hchart : ∀ n, chart n z = Exp (q n))
    (hq : ∀ n, ‖(finBasis ℝ H).equivFun (q n)‖ ≤ RH n)
    (hfacet : ∀ n, χ (q n) = s * scale n)
    {K : ℝ≥0} (J : ℕ → G → W) (hJ : ∀ n, LipschitzWith K (J n))
    (x : ℕ → G) (k : ℕ → A → G)
    (S : Set C(Z, W)) [MeasurableSpace (S × S)] [BorelSpace (S × S)]
    [HasOuterApproxClosed (S × S)]
    (samples : ℕ → ProbabilityMeasure A) (pair : ℕ → A → S × S)
    (hp : ∀ n, Measurable (pair n)) (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (pair n)) atTop (𝓝 ν))
    (hfirst : ∀ n, ∀ᵐ a ∂(samples n : Measure A), (pair n a).1.val z =
      rescaledMapProfile (J n) (x n) (k n a) (Real.log (scale n)) (chart n) z)
    (hsecond : ∀ n, ∀ᵐ a ∂(samples n : Measure A), (pair n a).2.val z =
      rescaledMapProfile (J n) (x n)
        (k n a * Exp (t n • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (Real.log (scale n)) (chart n) z)
    {f : S × S} (hf : f ∈ (ν : Measure (S × S)).support) :
    f.1.val z = f.2.val z := by
  let left := fun n => Exp (q n)
  let right := fun n => Exp (t n • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * Exp (q n)
  have hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      dist (left n) (right n) ≤ ε * scale n := by
    intro ε hε
    filter_upwards [facet_root_switch_sublinear T H χ hχ Exp hExp realize v
      scale RH R η s hs (fun n => (hscale n).le) hRH0 hR0 hRH hR hη ε hε] with n hn
    simpa only [left, right, one_mul] using hn 1 (q n) (t n) (hq n) (hfacet n) (ht n)
  let δ := fun n => dist (left n) (right n) / scale n
  have hδ : Tendsto δ atTop (𝓝 0) := distance_rate_tendsto_zero scale hscale left right hnear
  have hbound : ∀ n, ∀ᵐ a ∂(samples n : Measure A), dist ((pair n a).1.val z) ((pair n a).2.val z) ≤ K * δ n := by
    intro n
    filter_upwards [hfirst n, hsecond n] with a ha hb
    rw [ha, hb]
    have hd := rescaledMapProfile_suffix_dist_le (hJ n) (x n) (k n a)
      (k n a * Exp (t n • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
      (Real.log (scale n)) (chart n) z
    simpa only [Real.exp_log (hscale n), hchart, mul_assoc, dist_mul_left, δ, left, right]
      using hd
  have herr : Tendsto (fun n => (K : ℝ) * δ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hδ
  exact dist_eq_zero.mp (supported_profile_pair_eq_of_ae_discrepancy S samples pair hp ν hν
    z (fun n => K * δ n) herr (Eventually.of_forall hbound) hf)

end PolycyclicRecognition

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology NNReal

variable {EG G W A I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace A]
  [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)

include T in
/-- Exact facet agreement for the actual polynomial Cartan chart. The
polynomial position bound and the chart's exact height are proved here. -/
theorem supported_word_profiles_agree_on_facet
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
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace (S × S)] [BorelSpace (S × S)] [HasOuterApproxClosed (S × S)]
    (samples : ℕ → ProbabilityMeasure A) (pair : ℕ → A → S × S)
    (hp : ∀ n, Measurable (pair n)) (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (pair n)) atTop (𝓝 ν))
    (hfirst : ∀ n, ∀ᵐ a ∂(samples n : Measure A), (pair n a).1.val z =
      rescaledMapProfile (J n) (x n) (k n a) (Real.log (scale n))
        (fun v => Exp (wordChartPivot X words β (scale n) v : H)) z)
    (hsecond : ∀ n, ∀ᵐ a ∂(samples n : Measure A), (pair n a).2.val z =
      rescaledMapProfile (J n) (x n)
        (k n a * Exp (t n • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (Real.log (scale n))
        (fun v => Exp (wordChartPivot X words β (scale n) v : H)) z)
    {f : S × S} (hf : f ∈ (ν : Measure (S × S)).support) :
    f.1.val z = f.2.val z := by
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
  exact supported_profiles_agree_on_contact_facet T H (M.weight i) (M.weight_nonzero i)
    Exp hExp realize ⟨M.letter i, M.letter_root i⟩ scale RH R η t _ hscale
    (fun n => lt_of_lt_of_le zero_lt_one (hscale1 n)) hRH0 hR0 hRH hR hη ht
    (fun n v => Exp (wordChartPivot X words β (scale n) v : H)) z
    (fun n => wordChartPivot X words β (scale n) z) (fun _ => rfl) hq hfacet
    J hJ x k S samples pair hp ν hν hfirst hsecond hf

end PolycyclicRecognition.CartanWordModel

end

end OAI
