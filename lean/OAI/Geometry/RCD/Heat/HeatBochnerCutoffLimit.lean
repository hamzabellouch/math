import OAI.Geometry.RCD.Sobolev.CutoffBochnerConvergence
import OAI.Geometry.RCD.Heat.HeatLocalSourceConvergence
import OAI.Geometry.RCD.Coordinates.BoundedRegularBochnerMass
import OAI.Geometry.RCD.Heat.BoundedHeatSobolevData

namespace OAI

/-! # Full local heat Bochner measures and their exact cutoff limit -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X)
  [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem heat_bochner_cutoff_limit (hK : K ≤ 0)
    (u : SobolevSpace (hausdorff n X) hX.quadratic) (d : Lp ℝ 2 (hausdorff n X))
    (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d)
    (U : X → ℝ) (L A : ℝ≥0) (hU : LipschitzWith L U) (hUc : HasCompactSupport U)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] U)
    (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic u x| ≤ A)
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (2*R) C)
    (t : ℕ → ℝ) (ht : ∀ k, 0 < t k) (ht1 : ∀ k, t k ≤ 1)
    (ht0 : Tendsto t atTop (𝓝 0)) :
    let m := hausdorff n X
    let q := hX.quadratic
    let f := SobolevSpace.toLp m q u
    let w k := heatSobolev m q (t k) (ht k) f
    let D k := heatSobolevMap m q (t k/2) (half_pos (ht k))
      (-heatGeneratorAt m q (t k-t k/2) f)
    ∃ (G : ℕ → SobolevSpace m q) (σ : ℕ → Measure X),
      (∀ k, IsFiniteMeasure (σ k)) ∧
      (∀ k, SobolevSpace.toLp m q (G k) =ᵐ[m] localGamma m q (w k) (w k)) ∧
      (∀ k, ∀ (ψ : SobolevSpace m q) (v : X → ℝ),
        Continuous v → HasCompactSupport v → tsupport v ⊆ ball p (6*R) →
        SobolevSpace.toLp m q ψ =ᵐ[m] v →
        (∫ x, v x ∂σ k)=-(1/2:ℝ)*energyForm m q (G k) ψ-
          weightedGamma m q (SobolevSpace.toLp m q ψ) (w k) (D k)-
          K*weightedGamma m q v (w k) (w k)) ∧
      (∀ k, (σ k).real (closedBall p R) ≤ ∫ x, χ.weight x ∂σ k) ∧
      Tendsto (fun k => ∫ x, χ.weight x ∂σ k) atTop
        (𝓝 ((1/2:ℝ)*weightedGamma m q χ.laplacian u u+
          (∫ x, χ.weight x*(d x)^2 ∂m)+weightedGamma m q d u χ.sobolev-
          K*weightedGamma m q χ.weight u u)) := by
  intro m q f w D
  have hw (k : ℕ) := heatTail_weak_laplacian m q (t k) (ht k) f
  let L' : ℝ≥0 := ⟨(L:ℝ)*Real.exp |K|,mul_nonneg L.coe_nonneg (Real.exp_pos _).le⟩
  have hLL : (L:ℝ) ≤ L' := by
    change (L:ℝ) ≤ (L:ℝ)*Real.exp |K|
    exact le_mul_of_one_le_right L.coe_nonneg (Real.one_le_exp (abs_nonneg K))
  have hgrad (k : ℕ) : ∀ᵐ x ∂m, SobolevSpace.minimalSlope m q (w k) x ≤ L' := by
    have hg := hX.heat_compact_slope_bdd K n hn hU hUc p f hu.symm (t k) (ht k)
    have hExp : -K*t k ≤ |K| :=
      (mul_le_mul_of_nonneg_right (neg_le_abs K) (ht k).le).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (ht1 k) (abs_nonneg K))
    filter_upwards [hg] with x hx
    exact hx.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp) L.coe_nonneg)
  choose G hG using fun k => hX.bounded_heat_gram hn p f A hA (ht k)
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  have hmeasure (k : ℕ) : ∃ σ : Measure X, IsFiniteMeasure σ ∧
      (∀ (ψ : SobolevSpace m q) (v : X → ℝ),
        Continuous v → HasCompactSupport v → tsupport v ⊆ ball p (6*R) →
        SobolevSpace.toLp m q ψ =ᵐ[m] v →
        (∫ x, v x ∂σ)=-(1/2:ℝ)*energyForm m q (G k) ψ-
          weightedGamma m q (SobolevSpace.toLp m q ψ) (w k) (D k)-
          K*weightedGamma m q v (w k) (w k)) := by
    obtain ⟨hLip,-⟩ := hX.kernelHeat_bounded_regularity hn p hk f A hA (t k) (ht k)
    have hwr : SobolevSpace.toLp m q (w k) =ᵐ[m] kernelHeat m q hk (t k) f := by
      simpa only [w,heatSobolev_toLp] using (kernelHeat_represents_L2 m q hk (ht k) f).symm
    obtain ⟨M,_hM,hM⟩ := hX.bounded_regular_bochner_mass hn hK p (w k) (D k) (G k)
      (hw k) (kernelHeat m q hk (t k) f) hLip hwr A
      (hX.bounded_heat_sobolev_data hn p f A hA (ht k)).1 (hG k)
    obtain ⟨σ,hσ,hrep,_hmass⟩ := hM (2*R) (by positivity)
    refine ⟨σ,hσ,?_⟩
    intro ψ v hv hvc hvs hψ
    have he : inner ℝ (SobolevSpace.toLp m q ψ) (SobolevSpace.toLp m q (G k)) =
        weightedGamma m q v (w k) (w k) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hψ,hG k] with x hx hy
      change SobolevSpace.toLp m q (G k) x * SobolevSpace.toLp m q ψ x =
        v x * localGamma m q (w k) (w k) x
      change SobolevSpace.toLp m q (G k) x = localGamma m q (w k) (w k) x at hy
      rw [hx,hy]
      ring
    have hh := hrep ψ v hv hvc
      (by simpa only [show 3*(2*R)=6*R by ring] using hvs) hψ
    rw [he] at hh
    linarith only [hh]
  choose σ hσ hrep using hmeasure
  let (k : ℕ) : IsFiniteMeasure (σ k) := hσ k
  obtain ⟨hconv,hdconv⟩ := heat_regularization_value_source_converges m q u d hd t ht ht0
  have hlim := χ.bochner_source_tendsto m q hC u d w D G hw hG L' hgrad
    ((SobolevSpace.minimalSlope_le_lipschitz m q u hU hu).mono fun x hx => hx.trans hLL)
    hconv hdconv
  let P := weightedGammaCLM m q χ.weight.continuous.aestronglyMeasurable
    (C := 1) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (χ.bounds x).1]
      exact (χ.bounds x).2)
  have hp : Tendsto (fun k => weightedGamma m q χ.weight (w k) (w k)) atTop
      (𝓝 (weightedGamma m q χ.weight u u)) :=
    ((P.continuous.clm_apply continuous_id).tendsto u).comp hconv
  have hlimχ : Tendsto (fun k => ∫ x, χ.weight x ∂σ k) atTop
      (𝓝 ((1/2:ℝ)*weightedGamma m q χ.laplacian u u+
        (∫ x, χ.weight x*(d x)^2 ∂m)+weightedGamma m q d u χ.sobolev-
        K*weightedGamma m q χ.weight u u)) := by
    apply (hlim.sub (hp.const_mul K)).congr'
    filter_upwards [] with k
    have hh := hrep k χ.sobolev χ.weight χ.weight.continuous (χ.hasCompactSupport m q)
      ((χ.tsupport_subset m q).trans (closedBall_subset_ball (by linarith))) χ.representative
    have hwgt : weightedGamma m q (SobolevSpace.toLp m q χ.sobolev) (w k) (D k)=
        weightedGamma m q χ.weight (w k) (D k) := by
      apply integral_congr_ae
      filter_upwards [χ.representative] with x hx
      rw [hx]
    rw [hwgt] at hh ⊢
    exact hh.symm
  refine ⟨G,σ,hσ,hG,hrep,?_,hlimχ⟩
  intro k
  have hb : (closedBall p R).indicator (fun _ => (1:ℝ)) ≤ᵐ[σ k] χ.weight := by
    apply Eventually.of_forall
    intro x
    by_cases hx : x∈closedBall p R
    · rw [indicator_of_mem hx,χ.one x
        (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hx) (by linarith)))]
    · simpa only [indicator_of_notMem hx] using (χ.bounds x).1
  have hh := integral_mono_ae ((integrable_const (1:ℝ)).indicator measurableSet_closedBall)
    (χ.weight.continuous.integrable_of_hasCompactSupport (χ.hasCompactSupport m q)) hb
  simpa only [integral_indicator measurableSet_closedBall,setIntegral_const,smul_eq_mul,mul_one] using hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
