import Mathlib
import OAI.Geometry.CAT0Fillings.Slicing.CoordinateCoarea

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
universe u
attribute [local instance] Classical.propDecidable
namespace BorelCoefficients
variable {X : Type u} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
variable {k : ℕ} {T : Functional X k}
noncomputable def coefficientLinear (hT : IsMetricCurrent T) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    lipAlgebra (X := X) →ₗ[ℝ] ℝ where
  toFun f := T f.val π
  map_add' f g := by
    change T (fun x => f.val x + g.val x) π = _
    simpa using hT.linearFirst f.val g.val π 1 1 f.property g.property hπ
  map_smul' r f := by
    change T (fun x => r * f.val x) π = _
    simpa using hT.linearFirst f.val f.val π r 0 f.property f.property hπ

lemma coefficientLinear_bound (hT : IsMetricCurrent T) (hμ : Controls T μ)
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ i, LipschitzWith (K i) (π i)) (f : lipAlgebra (X := X)) :
    ‖coefficientLinear hT π (fun i => ⟨K i, hK i⟩) f‖ ≤
      (∏ i, (K i : ℝ)) * ‖lipToL1 μ f‖ := by
  rw [norm_lipToL1]
  exact hT.mass_bound hμ f.property K hK

noncomputable def l1Action (hT : IsMetricCurrent T) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) : Lp ℝ 1 μ →L[ℝ] ℝ :=
  (coefficientLinear hT π hπ).extendOfNorm (lipToL1 μ)

lemma l1Action_eq (hT : IsMetricCurrent T) (hμ : Controls T μ)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (f : lipAlgebra (X := X)) : l1Action μ hT π hπ (lipToL1 μ f) = T f.val π := by
  have hπcopy := hπ
  choose K hK using hπcopy
  exact LinearMap.extendOfNorm_eq (lipToL1_dense μ)
    ⟨∏ i, (K i : ℝ), coefficientLinear_bound μ hT hμ π K hK⟩ f

lemma l1Action_bound (hT : IsMetricCurrent T) (hμ : Controls T μ)
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ i, LipschitzWith (K i) (π i)) (b : Lp ℝ 1 μ) :
    |l1Action μ hT π (fun i => ⟨K i, hK i⟩) b| ≤ (∏ i, (K i : ℝ)) * ‖b‖ :=
  LinearMap.norm_extendOfNorm_apply_le (lipToL1_dense μ) _
    (coefficientLinear_bound μ hT hμ π K hK) b

noncomputable def borelAction (hT : IsMetricCurrent T) : Functional X k :=
  fun b π => if hb : Integrable b μ then
    if hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i) then
      l1Action μ hT π hπ (hb.toL1 b) else 0 else 0

lemma borelAction_of_integrable (hT : IsMetricCurrent T) {b : X → ℝ}
    (hb : Integrable b μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction μ hT b π = l1Action μ hT π hπ (hb.toL1 b) := by
  simp only [borelAction, dite_eq_left hb, dite_eq_left hπ]

lemma borelAction_eq (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hadm : Admissible b π) :
    borelAction μ hT b π = T b π := by
  let f : lipAlgebra (X := X) := ⟨⟨b, hadm.1.continuous⟩, hadm.1⟩
  have hbeq : (integrable_boundedLip μ hadm.1).toL1 b = lipToL1 μ f := by
    apply Lp.ext
    exact (Integrable.coeFn_toL1 _).trans
      (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ f.val).symm
  rw [borelAction_of_integrable μ hT (integrable_boundedLip μ hadm.1) π hadm.2, hbeq]
  exact l1Action_eq μ hT hμ π hadm.2 f

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure μ] in
lemma norm_toL1_integral_abs {b : X → ℝ} (hb : Integrable b μ) :
    ‖hb.toL1 b‖ = ∫ x, |b x| ∂μ := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [hb.coeFn_toL1] with x hx
  rw [hx, Real.norm_eq_abs]

lemma borelAction_bound (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b : X → ℝ} (hb : Integrable b μ) (π : Fin k → X → ℝ)
    (K : Fin k → ℝ≥0) (hK : ∀ i, LipschitzWith (K i) (π i)) :
    |borelAction μ hT b π| ≤ (∏ i, (K i : ℝ)) * ∫ x, |b x| ∂μ := by
  rw [borelAction_of_integrable μ hT hb π (fun i => ⟨K i, hK i⟩)]
  simpa only [norm_toL1_integral_abs] using l1Action_bound μ hT hμ π K hK (hb.toL1 b)

lemma borelAction_add (hT : IsMetricCurrent T) {b c : X → ℝ}
    (hb : Integrable b μ) (hc : Integrable c μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction μ hT (b + c) π = borelAction μ hT b π + borelAction μ hT c π := by
  simp only [borelAction_of_integrable μ hT (hb.add hc) π hπ,
    borelAction_of_integrable μ hT hb π hπ, borelAction_of_integrable μ hT hc π hπ,
    ]
  change l1Action μ hT π hπ (hb.toL1 b + hc.toL1 c) = _
  exact map_add _ _ _

lemma borelAction_smul (hT : IsMetricCurrent T) {b : X → ℝ}
    (hb : Integrable b μ) (π : Fin k → X → ℝ) (r : ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction μ hT (r • b) π = r * borelAction μ hT b π := by
  simp only [borelAction_of_integrable μ hT (hb.smul r) π hπ,
    borelAction_of_integrable μ hT hb π hπ]
  change l1Action μ hT π hπ (r • hb.toL1 b) = _
  exact map_smul _ _ _

lemma borelAction_congr_ae (hT : IsMetricCurrent T) {b c : X → ℝ}
    (hbc : b =ᵐ[μ] c) (π : Fin k → X → ℝ) :
    borelAction μ hT b π = borelAction μ hT c π := by
  by_cases hb : Integrable b μ
  · have hc := hb.congr hbc
    by_cases hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)
    · rw [borelAction_of_integrable μ hT hb π hπ, borelAction_of_integrable μ hT hc π hπ,
        (Integrable.toL1_eq_toL1_iff b c hb hc).mpr hbc]
    · simp only [borelAction, dite_eq_left hb, dite_eq_left hc, dite_eq_right hπ]
  · have hc : ¬Integrable c μ := fun hc => hb (hc.congr hbc.symm)
    simp only [borelAction, dite_eq_right hb, dite_eq_right hc]

lemma l1Action_lipschitz (hT : IsMetricCurrent T) (hμ : Controls T μ)
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ i, LipschitzWith (K i) (π i)) :
    LipschitzWith (∏ i, K i) (l1Action μ hT π (fun i => ⟨K i, hK i⟩)) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro b c
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  simpa only [Real.norm_eq_abs, NNReal.coe_prod] using l1Action_bound μ hT hμ π K hK (b-c)

lemma borelAction_sequentialContinuity (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b : X → ℝ} (hb : Integrable b μ) (π : Fin k → X → ℝ)
    (πs : ℕ → Fin k → X → ℝ)
    (hLip : ∀ i, ∃ K : ℝ≥0, ∀ j, LipschitzWith K (πs j i))
    (hpt : ∀ i x, Tendsto (fun j => πs j i x) atTop (𝓝 (π i x))) :
    Tendsto (fun j => borelAction μ hT b (πs j)) atTop (𝓝 (borelAction μ hT b π)) := by
  choose K hK using hLip
  have hKlim (i) : LipschitzWith (K i) (π i) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    exact le_of_tendsto ((hpt i x).dist (hpt i y))
      (Eventually.of_forall fun j => (hK i j).dist_le_mul x y)
  have hlim := tendsto_of_lipschitz_dense (l := atTop)
    (fun j => l1Action_lipschitz μ hT hμ (πs j) K (fun i => hK i j))
    (l1Action_lipschitz μ hT hμ π K hKlim) (lipToL1_dense μ)
    (fun f => ?_) (hb.toL1 b)
  · simp only [borelAction_of_integrable μ hT hb _ (fun i => ⟨K i, hK i _⟩),
      borelAction_of_integrable μ hT hb π (fun i => ⟨K i, hKlim i⟩)]
    exact hlim
  · simp only [l1Action_eq μ hT hμ]
    exact hT.sequentialContinuity f.val π πs f.property (fun i => ⟨K i, hK i⟩) hpt

end BorelCoefficients
end CAT0Fillings
end

end OAI
