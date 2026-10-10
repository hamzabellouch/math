import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanInteriorSwitch
import OAI.GroupTheory.PolycyclicRecognition.Analysis.AffineSheetAgreement
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledProfiles

namespace OAI

/-! # Supported Cartan sheets agree above an interior generator switch -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter Set MeasureTheory
open scoped Manifold Topology NNReal

/-- At a fixed chart point, changing the suffix changes the profile by at
most the normalized distance between the two right-positioned sheets. -/
theorem rescaledMapProfile_suffix_dist_le
    {G W V : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {L : ℝ≥0} {J : G → W} (hJ : LipschitzWith L J)
    (x k l : G) (r : ℝ) (φ : V → G) (z : V) :
    dist (rescaledMapProfile J x k r φ z) (rescaledMapProfile J x l r φ z) ≤
      (L : ℝ) * (dist (k * φ z) (l * φ z) / Real.exp r) := by
  have h := hJ.dist_le_mul (x * k * φ z) (x * l * φ z)
  rw [mul_assoc x k, mul_assoc x l, dist_mul_left] at h
  have he : dist (rescaledMapProfile J x k r φ z) (rescaledMapProfile J x l r φ z) =
      dist (J (x * k * φ z)) (J (x * l * φ z)) / Real.exp r := by
    simp only [rescaledMapProfile, dist_eq_norm, ← smul_sub,
      sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos (Real.exp_pos r), div_eq_mul_inv, mul_comm]
  rw [he]
  simpa only [mul_assoc] using
    (div_le_div_of_nonneg_right h (Real.exp_pos r).le).trans_eq (mul_div_assoc _ _ _)

namespace CartanWordModel

variable {EG G I W A : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Fintype I] [DecidableEq I]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace A]

include T in
/-- Every supported joint limit of two actual sheets separated by a
strictly interior root switch agrees at the given chart point. -/
theorem supported_switch_profiles_agree
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (X : I → H) (words : Finset (FreeMagma I)) (β : WordBasisSelections X words)
    (z : Fin (finrank ℝ H) → ℝ) (i : Fin M.letterCount)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (t : ℕ → ℝ) {B s : ℝ} (hB : 0 ≤ B)
    (ht : ∀ᶠ n in atTop, |t n| ≤ B * Real.exp (scale n * (s + ε n)))
    (hslack : s < M.weight i ((WordBasisSelections.basis X words β).equivFun.symm z))
    {L : ℝ≥0} (J : ℕ → G → W) (hJ : ∀ n, LipschitzWith L (J n))
    (x : ℕ → G) (k : ℕ → A → G)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace (S × S)] [BorelSpace (S × S)] [HasOuterApproxClosed (S × S)]
    (samples : ℕ → ProbabilityMeasure A) (pair : ℕ → A → S × S)
    (hp : ∀ n, Measurable (pair n)) (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (pair n)) atTop (𝓝 ν))
    (hfirst : ∀ n a w, (pair n a).1.val w =
      rescaledMapProfile (J n) (x n) (k n a) (max (Real.log (scale n)) 0)
        (fun v => Exp (wordChartPivot X words β (scale n) v : H)) w)
    (hsecond : ∀ n a w, (pair n a).2.val w =
      rescaledMapProfile (J n) (x n)
        (k n a * Exp (t n • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (max (Real.log (scale n)) 0)
        (fun v => Exp (wordChartPivot X words β (scale n) v : H)) w)
    {f : S × S} (hf : f ∈ (ν : Measure (S × S)).support) :
    f.1.val z = f.2.val z := by
  obtain ⟨C, _, hC⟩ := M.exists_word_pivot_interior_switch_bound T Exp hExp realize
    X words β z i scale hscale ε hε t hB ht hslack
  let err := fun n => (L : ℝ) * C * (Real.log (2 + scale n) / scale n)
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa only [err, Function.comp_def, mul_zero] using
      (log_shift_div_tendsto_zero.comp hscale).const_mul ((L : ℝ) * C)
  have hbound : ∀ᶠ n in atTop, ∀ a,
      dist ((pair n a).1.val z) ((pair n a).2.val z) ≤ err n := by
    filter_upwards [hC, hscale.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hr a
    rw [hfirst, hsecond, max_eq_left (Real.log_nonneg hr)]
    have hd := rescaledMapProfile_suffix_dist_le (hJ n) (x n) (k n a)
      (k n a * Exp (t n • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
      (max (Real.log (scale n)) 0)
      (fun v => Exp (wordChartPivot X words β (scale n) v : H)) z
    rw [max_eq_left (Real.log_nonneg hr), Real.exp_log (by linarith)] at hd
    apply hd.trans
    have hb := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (hn (k n a)) (show 0 ≤ scale n by linarith)) L.coe_nonneg
    exact hb.trans_eq (by dsimp [err]; ring)
  exact dist_eq_zero.mp (supported_profile_pair_eq_of_uniform_discrepancy S samples pair hp ν hν
    z err herr hbound hf)

end CartanWordModel
end PolycyclicRecognition

end

end OAI
