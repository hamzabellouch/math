import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicContractionModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicCartanHeightAssembly
import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntrinsicTraceFromHaar
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PublishedRecognitionInputs
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoarsePairHeight
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePairMetricChange
import OAI.GroupTheory.PolycyclicRecognition.Geometry.HeightChangeOfCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SelfQuasiIsometry
import Mathlib.Algebra.Lie.CartanExists

namespace OAI

/-! # Uniform bounded height in a fixed metric and an arbitrary norm

The auxiliary Riemannian metric is used only to construct smoothing. The
identity comparison transfers every uniformly controlled family from the
specified proper chain metric. A bounded linear change of coordinates then
returns the estimate to the specified norm on the canonical height space.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra MeasureTheory
open scoped Manifold NNReal

attribute [local instance] stationaryL2Action zeroMeanL2Action

/-- Unimodularity of the actual Lie model, using its canonical Borel Haar measure. -/
def ModelIsUnimodular (R : SimplyConnectedSolvableLieModel) : Prop :=
  letI : IsTopologicalGroup R.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, R.modelSpace)) ⊤
  letI : LocallyCompactSpace R.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, R.modelSpace))
  letI : MeasurableSpace R.carrier := borel _
  letI : BorelSpace R.carrier := ⟨rfl⟩
  (Measure.haar : Measure R.carrier).IsMulRightInvariant

/-- The standalone uniform bounded-height theorem. In particular the
fixed metric can be any left-invariant proper Riemannian metric. The finite
group is chosen before the quasi-isometry constants, and the bound is
uniform over all self quasi-isometries with those constants. -/
theorem uniform_bounded_height
    (R : SimplyConnectedSolvableLieModel) (d : ProperChainMetric R.carrier)
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier) a)
    (huni : ModelIsUnimodular R)
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier → R.carrier)
    (hExp : IsGroupExponential Exp) (π : R.carrier →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) :
    letI := d.compatibleMetric
    ∃ A : Subgroup (W ≃ₗ[ℝ] W), Set.Finite (A : Set (W ≃ₗ[ℝ] W)) ∧
      ∀ K C : ℝ, 1 ≤ K → 0 ≤ C → ∃ B : ℝ, 0 ≤ B ∧
        ∀ F : SelfQuasiIsometry R.carrier K C, ∃ AF : A, ∀ g,
          ‖(π (F.toFun g)).toAdd - ((π (F.toFun 1)).toAdd + AF.val (π g).toAdd)‖ ≤ B := by
  classical
  let : IsTopologicalGroup R.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, R.modelSpace)) ⊤
  let : LocallyCompactSpace R.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, R.modelSpace))
  let : MeasurableSpace R.carrier := borel _
  let : BorelSpace R.carrier := ⟨rfl⟩
  let m : Measure R.carrier := Measure.haar
  let : m.IsMulRightInvariant := huni
  obtain ⟨d₀, hcompat⟩ := lieRiemannianMetricInput R
  let := d₀.toProperChainMetric.compatibleMetric
  let := d₀.toProperChainMetric.proper_compatibleMetric
  let := d₀.toProperChainMetric.isometric_compatibleMetric
  let V := EuclideanSpace ℝ (Fin (finrank ℝ (HeightSpace T.character)))
  let q₀ : HeightSpace T.character ≃ₗ[ℝ] V :=
    LinearEquiv.ofFinrankEq _ _ (by simp [V])
  obtain ⟨π₀, hπ₀Exp, _, _, L, hL, hπ₀Lip⟩ :=
    exists_lipschitz_intrinsic_canonical_height T q₀ d₀.toProperChainMetric.chains_compatibleMetric hExp
  let e : V ≃ₗ[ℝ] W := q₀.symm.trans q
  have hπe (g : R.carrier) : (π g).toAdd = e (π₀ g).toAdd := by
    apply height_eq_of_exponential_linear hExp π π₀ e.toLinearMap
    intro x
    rw [hπExp, hπ₀Exp]
    simp [e]
  have hπ₀ : LipschitzWith (⟨L, hL⟩ : ℝ≥0) (fun g => (π₀ g).toAdd) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm]
    exact hπ₀Lip x y
  obtain ⟨n, φ, hφ0, hf, hb⟩ :=
    exists_intrinsic_smooth_coordinates T q₀ Exp hExp π₀ hπ₀.continuous hπ₀Exp
  obtain ⟨hfLip, hbLip⟩ := hcompat n φ hf hb
  let c := ControlledContraction.ofChart φ hφ0 hfLip hbLip
  have hunimod (x : GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier) :
      LinearMap.trace ℝ _ (ad ℝ _ x) = 0 :=
    trace_ad_eq_zero_of_intrinsic_kernel_haar T q₀ Exp hExp π₀ hπ₀.continuous hπ₀Exp m x
  obtain ⟨x, hx⟩ := LieAlgebra.exists_isCartanSubalgebra_engel ℝ
    (GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier)
  let H := LieSubalgebra.engel ℝ x
  let : H.IsCartanSubalgebra := hx
  obtain ⟨M⟩ := nonempty_cartanWordModel H T
  let D := M.supportIn T hunimod q₀
  have hheight := M.exists_uniform_height_intrinsic T hunimod q₀ Exp hExp
    m π₀ hπ₀Exp hπ₀
    d₀.minimizing_compatibleMetric remezPolynomialInput geodesicMetricExistenceInput
  let A := (templateSymmetryGroup D).map (heightConjugation e)
  refine ⟨A, finite_heightConjugation e (templateSymmetryGroup D), ?_⟩
  intro K C hK hC
  let Q := @SelfQuasiIsometry R.carrier d.compatibleMetric.toPseudoMetricSpace K C
  let f : Q → R.carrier → R.carrier := by
    let := d.compatibleMetric
    exact fun F => F.toFun
  let g : Q → R.carrier → R.carrier := by
    let := d.compatibleMetric
    exact fun F => F.inverse
  have hK₀ : 0 ≤ K := le_trans zero_le_one hK
  have hf : letI := d.compatibleMetric
      ∀ F x y, dist (f F x) (f F y) ≤ K * dist x y + (C + 3 * K * C) := by
    let := d.compatibleMetric
    intro F x y
    exact (F.upper x y).trans (by nlinarith)
  have hg : letI := d.compatibleMetric
      ∀ F x y, dist (g F x) (g F y) ≤ K * dist x y + (C + 3 * K * C) := by
    let := d.compatibleMetric
    intro F x y
    exact (F.inverse_upper hK₀ x y).trans (by linarith)
  have hgf : letI := d.compatibleMetric
      ∀ F x, dist (g F (f F x)) x ≤ C + 2 * K * C := by
    let := d.compatibleMetric
    intro F x
    exact (F.left_inverse_close hK₀ x).trans (by linarith)
  have hfg : letI := d.compatibleMetric
      ∀ F x, dist (f F (g F x)) x ≤ C + 2 * K * C := by
    let := d.compatibleMetric
    intro F x
    exact ((dist_comm _ _).trans_le (F.inverse_close x)).trans (by nlinarith)
  obtain ⟨κ, ξ, ε, hκ, hξ, _, hf', hg', hgf', hfg'⟩ :=
    coarse_pair_metric_change d d₀.toProperChainMetric hK₀
      (by positivity : 0 ≤ C + 3 * K * C) (by positivity : 0 ≤ C + 2 * K * C)
      f g hf hg hgf hfg
  obtain ⟨label, B, hB, hbound⟩ := uniform_affine_height_of_coarse_inverse_pairs
    c d₀.minimizing_compatibleMetric D π₀ hL hπ₀Lip hheight
    hκ hξ f g hf' hg' hgf' hfg'
  refine ⟨‖e.toContinuousLinearEquiv.toContinuousLinearMap‖ * B,
    mul_nonneg (norm_nonneg _) hB, ?_⟩
  intro F
  refine ⟨⟨heightConjugation e (label F).val, ?_⟩, fun y => ?_⟩
  · exact ⟨(label F).val, (label F).property, rfl⟩
  · simp only [hπe]
    exact norm_height_difference_le e _ _ _ (label F).val (hbound F y)

/-- Compatibility form of the height theorem; its published-input argument
is no longer needed. -/
theorem uniform_bounded_height_of_published_inputs
    (_inputs : PublishedRecognitionInputs)
    (R : SimplyConnectedSolvableLieModel) (d : ProperChainMetric R.carrier)
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier) a)
    (huni : ModelIsUnimodular R)
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier → R.carrier)
    (hExp : IsGroupExponential Exp) (π : R.carrier →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) :
    letI := d.compatibleMetric
    ∃ A : Subgroup (W ≃ₗ[ℝ] W), Set.Finite (A : Set (W ≃ₗ[ℝ] W)) ∧
      ∀ K C : ℝ, 1 ≤ K → 0 ≤ C → ∃ B : ℝ, 0 ≤ B ∧
        ∀ F : SelfQuasiIsometry R.carrier K C, ∃ AF : A, ∀ g,
          ‖(π (F.toFun g)).toAdd - ((π (F.toFun 1)).toAdd + AF.val (π g).toAdd)‖ ≤ B := by
  exact uniform_bounded_height R d T huni q Exp hExp π hπExp

end PolycyclicRecognition

end

end OAI
