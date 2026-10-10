import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootSupportSwitch
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordModel
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordChartPivot
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialEnvelopes

namespace OAI

/-! # Interior root switches disappear in rescaled profiles -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Fintype I] [DecidableEq I]

include T in
/-- Above a generator's support height, every switch with the prescribed
subexponential amplitude has vanishing normalized distance. The chart
position and its polynomial bound are constructed from the word basis. -/
theorem exists_word_pivot_interior_switch_bound
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (z : Fin (finrank ℝ H) → ℝ) (i : Fin M.letterCount)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (t : ℕ → ℝ) {B s : ℝ} (hB : 0 ≤ B)
    (ht : ∀ᶠ n in atTop, |t n| ≤ B * Real.exp (scale n * (s + ε n)))
    (hslack : s < M.weight i ((WordBasisSelections.basis X S β).equivFun.symm z)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ x : G,
      dist (x * Exp (wordChartPivot X S β (scale n) z : H))
        (x * Exp (t n • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) *
          Exp (wordChartPivot X S β (scale n) z : H)) ≤ K * Real.log (2 + scale n) := by
  let χ : H →ₗ[ℝ] ℝ := (cartanHeightWeight T H (M.weight i)).comp
    ((heightProjection T.character).comp H.subtype)
  have hχ (h : H) : χ h = M.weight i h := cartanHeightWeight_projection T H (M.weight i) h
  have hbr (h k : H) : χ ⁅h, k⁆ = 0 := by
    change cartanHeightWeight T H (M.weight i)
      (heightProjection T.character (⁅h, k⁆ : H)) = 0
    rw [LieSubalgebra.coe_bracket, T.height_lie, map_zero]
  have hheight (r : ℝ) (hr : 1 ≤ r) :
      M.weight i (wordChartPivot X S β r z) =
        r * M.weight i ((WordBasisSelections.basis X S β).equivFun.symm z) := by
    simpa only [hχ, smul_eq_mul] using wordChartPivot_height X S β χ hbr hr z
  obtain ⟨A, p, hA, hpos⟩ := wordChartPivot_polynomial_bound X S β (finBasis ℝ H) z
  let v : rootSpace H (M.weight i) := ⟨M.letter i, M.letter_root i⟩
  obtain ⟨K, hK, hswitch⟩ := logarithmic_root_support_switch_polynomial_position
    T H (M.weight i) (M.weight_nonzero i) Exp hExp realize v hA hB p
  have hr : ∀ᶠ n in atTop, 1 ≤ scale n := hscale.eventually (eventually_ge_atTop 1)
  have he : ∀ᶠ n in atTop,
      ε n < M.weight i ((WordBasisSelections.basis X S β).equivFun.symm z) - s :=
    hε.eventually (gt_mem_nhds (sub_pos.mpr hslack))
  have hb : ∀ᶠ n in atTop,
      |t n| * Real.exp (-(M.weight i (wordChartPivot X S β (scale n) z))) ≤ B := by
    filter_upwards [hr, he, ht] with n hrn hen htn
    rw [hheight _ hrn]
    have ha : |t n| ≤ B * Real.exp
        (scale n * M.weight i ((WordBasisSelections.basis X S β).equivFun.symm z)) := by
      apply htn.trans
      apply mul_le_mul_of_nonneg_left _ hB
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hmul := mul_le_mul_of_nonneg_right ha
      (Real.exp_pos (-(scale n * M.weight i
        ((WordBasisSelections.basis X S β).equivFun.symm z)))).le
    simpa only [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] using hmul
  refine ⟨K, hK, ?_⟩
  filter_upwards [hr, hb] with n hn hbn x
  exact hswitch (scale n) (by linarith) x
    (wordChartPivot X S β (scale n) z) (t n) (hpos _ hn) hbn

include T in
/-- The preceding uniform switch bound vanishes after dividing by the
physical scale, for arbitrary translated sheets. -/
theorem word_pivot_interior_switch_sublinear
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (z : Fin (finrank ℝ H) → ℝ) (i : Fin M.letterCount)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (t : ℕ → ℝ) (x : ℕ → G) {B s : ℝ} (hB : 0 ≤ B)
    (ht : ∀ᶠ n in atTop, |t n| ≤ B * Real.exp (scale n * (s + ε n)))
    (hslack : s < M.weight i ((WordBasisSelections.basis X S β).equivFun.symm z)) :
    Tendsto (fun n =>
      dist (x n * Exp (wordChartPivot X S β (scale n) z : H))
        (x n * Exp (t n • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) *
          Exp (wordChartPivot X S β (scale n) z : H)) / scale n) atTop (𝓝 0) := by
  obtain ⟨K, _, hb⟩ := M.exists_word_pivot_interior_switch_bound T Exp hExp realize
    X S β z i scale hscale ε hε t hB ht hslack
  have hlog : Tendsto (fun n => K * (Real.log (2 + scale n) / scale n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using (log_shift_div_tendsto_zero.comp hscale).const_mul K
  have hr := hscale.eventually (eventually_gt_atTop (0 : ℝ))
  apply squeeze_zero' _ _ hlog
  · filter_upwards [hr] with n hn
    exact div_nonneg dist_nonneg hn.le
  · filter_upwards [hr, hb] with n hn hbn
    exact (div_le_div_of_nonneg_right (hbn (x n)) hn.le).trans_eq (mul_div_assoc _ _ _)

end PolycyclicRecognition.CartanWordModel

end

end OAI
