import Mathlib
import OAI.Geometry.SmoothYau.Estimates.RealValueCubic

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
namespace YauCounterexamples
open Filter
open scoped Topology ContDiff Manifold
private lemma cubicConstant_nonneg {K U : ℝ} (hK : 0 ≤ K) (hU : 0 ≤ U) :
    0 ≤ 3 + 3 * K ^ 2 * U + K ^ 3 * U := by positivity
private lemma quinticConstant_nonneg {K U : ℝ} (hK : 0 ≤ K) (hU : 0 ≤ U) :
    0 ≤ BoundedAlgebra.remainderConstant K U := by
  unfold BoundedAlgebra.remainderConstant
  positivity
private lemma factor_limit_algebra (Λ ε δ : ℕ → ℝ) (R D I K C V F : ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hΛε : Tendsto (fun n => Λ n * ε n) atTop (𝓝 0))
    (hΛδ : Tendsto (fun n => Λ n * δ n) atTop (𝓝 0))
    (hstart : Tendsto (fun n => Λ n * ε n / δ n) atTop (𝓝 0)) :
    Tendsto (fun n => R * (D * ε n + Λ n * I *
      (K * (5 * C + 1) * ε n + K * V * F * δ n))) atTop (𝓝 0) ∧
    Tendsto (fun n => R * Λ n * I * ((C + 1) * ε n) / δ n) atTop (𝓝 0) := by
  constructor
  · convert ((hε.const_mul (R * D)).add
      ((hΛε.const_mul (R * I * K * (5 * C + 1))).add
        (hΛδ.const_mul (R * I * K * V * F)))) using 1
    · ext n; ring
    · simp
  · convert hstart.const_mul (R * I * (C + 1)) using 1
    · ext n; ring
    · simp
private lemma norm_le_of_sub_bound {X : Type*} [NormedAddCommGroup X]
    (c e : X) (C ε : ℝ) (hC : 0 ≤ C) (hε : ε ≤ 1) (hc : ‖c - e‖ ≤ C * ε) :
    ‖c‖ ≤ ‖e‖ + C := by
  calc
    ‖c‖ ≤ ‖c - e‖ + ‖e‖ := by simpa using norm_add_le (c - e) e
    _ ≤ C * ε + ‖e‖ := add_le_add hc le_rfl
    _ ≤ C * 1 + ‖e‖ := add_le_add (mul_le_mul_of_nonneg_left hε hC) le_rfl
    _ = ‖e‖ + C := by ring
private lemma factor_bound_transfer {r R d D Λ I K C V F ε δ : ℝ}
    (hR : 0 ≤ R) (hd0 : 0 ≤ d) (hΛ : 0 ≤ Λ) (hI : 0 ≤ I)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hV : 0 ≤ V) (hF : 0 ≤ F)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hr : r ≤ R) (hd : d ≤ D * ε) :
    r * (d + Λ * I * (K * (5 * C + 1) * ε + K * V * F * δ)) ≤
      R * (D * ε + Λ * I * (K * (5 * C + 1) * ε + K * V * F * δ)) ∧
    r * Λ * I * ((C + 1) * ε) ≤ R * Λ * I * ((C + 1) * ε) := by
  constructor
  · exact mul_le_mul hr (add_le_add hd le_rfl) (by positivity) hR
  · gcongr
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

theorem eventually_positive_factor
    (hd : Module.finrank ℝ E = 3) (B : ∀ i, A.PatchCoefficients i)
    (ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)))
    (b s : ℕ → M → ℝ)
    (hb : ∀ n, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (b n))
    (hsmooth : ∀ n, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (s n))
    (Λ ε δ : ℕ → ℝ)
    (hΛ : Tendsto Λ atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hΛε : Tendsto (fun n => Λ n * ε n) atTop (𝓝 0))
    (hΛδ : Tendsto (fun n => Λ n * δ n) atTop (𝓝 0))
    (hstart : Tendsto (fun n => Λ n * ε n / δ n) atTop (𝓝 0))
    (hpos : ∀ᶠ n in atTop, 0 ≤ ε n ∧ 0 < δ n)
    (hdata : ∀ᶠ n in atTop,
      ‖A.realOfSmooth _ ht (fun x => b n x - 1) ((hb n).sub contMDiff_const)‖ ≤ ε n ∧
      ‖A.realOfSmooth _ ht (fun x => s n x - 1) ((hsmooth n).sub contMDiff_const)‖ ≤ ε n) :
    ∀ᶠ n in atTop, ∃ u : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u ∧ (∀ x, 0 < u x) ∧
      (∀ x, weightedLaplacian g (b n) u x =
        Λ n * b n x ^ 3 * u x ^ 5 - Λ n * s n x * u x) ∧
      ∃ h : A.realH (2 * ((k + 1 : ℕ) : ℝ)), ‖h‖ ≤ δ n ∧
        ∀ x, A.realValue (2 * ((k + 1 : ℕ) : ℝ)) h x = u x - 1 := by
  let q : ℝ := 2 * ((k + 1 : ℕ) : ℝ)
  let e := A.realOfSmooth q ht (fun _ => 1) contMDiff_const
  let U := ‖e‖
  let K := ‖A.realProduct (k + 1) ht‖
  let C := 3 + 3 * K ^ 2 * U + K ^ 3 * U
  let V := U + C
  let R := 2 * A.parametrixBound
  let I := ‖A.realInclusion‖
  let J := ‖A.representative q‖
  let D := (‖A.realLaplacian B‖ * K +
    2 * ‖A.realProduct k hs‖ * I * ‖A.realLaplacian B‖) / 2
  let F := BoundedAlgebra.remainderConstant K U
  have hU : 0 ≤ U := norm_nonneg e
  have hK : 0 ≤ K := (A.realProduct (k + 1) ht).opNorm_nonneg
  have hC : 0 ≤ C := cubicConstant_nonneg hK hU
  have hV : 0 ≤ V := add_nonneg hU hC
  have hR : 0 ≤ R := mul_nonneg (by norm_num) A.parametrixBound_nonneg
  have hI : 0 ≤ I := A.realInclusion.opNorm_nonneg
  have hJ : 0 ≤ J := (A.representative q).opNorm_nonneg
  have hL : 0 ≤ ‖A.realLaplacian B‖ := (A.realLaplacian B).opNorm_nonneg
  have hlow : 0 ≤ ‖A.realProduct k hs‖ := (A.realProduct k hs).opNorm_nonneg
  have hD : 0 ≤ D := div_nonneg (add_nonneg (mul_nonneg hL hK)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hlow) hI) hL)) (by norm_num)
  have hF : 0 ≤ F := quinticConstant_nonneg hK hU
  obtain ⟨hsmalllim, hstartlim⟩ := factor_limit_algebra Λ ε δ R D I K C V F hε hΛε hΛδ hstart
  have hJε : Tendsto (fun n => J * ε n) atTop (𝓝 0) := by simpa using hε.const_mul J
  have hJδ : Tendsto (fun n => J * δ n) atTop (𝓝 0) := by simpa using hδ.const_mul J
  obtain ⟨a, ha, hadm⟩ := A.exists_parametrix_threshold B
  have hmass : Tendsto (fun n => 4 * Λ n) atTop atTop := Filter.Tendsto.const_mul_atTop (by norm_num) hΛ
  filter_upwards [hpos, hdata, hΛ.eventually (eventually_gt_atTop 0),
    hmass.eventually (eventually_ge_atTop a),
    hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hδ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hsmalllim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hstartlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hJε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hJδ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with n hn hdatan hΛn ham hεn hδn hsmalln hstartn hJεn hJδn
  let β := A.realOfSmooth q ht (fun x => b n x - 1) ((hb n).sub contMDiff_const)
  let τ := A.realOfSmooth q ht (fun x => s n x - 1) ((hsmooth n).sub contMDiff_const)
  let σ := e + τ
  let c := BoundedAlgebra.cubicPerturbation (A.realProduct (k + 1) ht) e β
  have he (x : M) : A.realValue q e x = 1 := A.realOfSmooth_value q ht _ _ x
  have hβ (x : M) : A.realValue q β x = b n x - 1 := A.realOfSmooth_value q ht _ _ x
  have hσ (x : M) : A.realValue q σ x = s n x := by
    dsimp only [σ]
    rw [A.realValue_add, he, A.realOfSmooth_value]
    ring
  have hc (x : M) : A.realValue q c x = b n x ^ 3 := by
    dsimp only [c]
    rw [A.realValue_cubic (k + 1) ht e β he, hβ]
    ring
  have hce : ‖c - e‖ ≤ C * ε n :=
    BoundedAlgebra.cubicPerturbation_bound _ e le_rfl le_rfl hn.1 hεn.le hdatan.1
  have hcs : ‖c‖ ≤ V := norm_le_of_sub_bound c e C (ε n) hC hεn.le hce
  have hσe : ‖σ - e‖ ≤ ε n := by
    have hm : σ - e = τ := by dsimp [σ]; abel
    rw [hm]
    exact hdatan.2
  have hbpos (x : M) : 0 < b n x := by
    have hv := A.realValue_norm_bound q β x
    rw [hβ] at hv
    have hv' : |b n x - 1| < 1 := (hv.trans
      (mul_le_mul_of_nonneg_left hdatan.1 hJ)).trans_lt hJεn
    have := (abs_lt.mp hv').1
    linarith
  obtain ⟨hα, herr⟩ := hadm _ ham
  have hRn : ‖A.realResolvent B (4 * Λ n) (by positivity) hα herr‖ ≤ R :=
    A.realResolvent_norm_bound B _ (by positivity) hα herr
  have hDn : ‖A.realDivergence B β‖ ≤ D * ε n :=
    (A.realDivergence_norm_bound B ht β).trans (mul_le_mul_of_nonneg_left hdatan.1 hD)
  have hdn0 : 0 ≤ ‖A.realDivergence B β‖ := (A.realDivergence B β).opNorm_nonneg
  obtain ⟨hbound, hboundstart⟩ := factor_bound_transfer hR hdn0 hΛn.le hI hK hC hV hF
    hn.1 hn.2.le hRn hDn
  have hsmall' := hbound.trans hsmalln.le
  have hstart' : ‖A.realResolvent B (4 * Λ n) (by positivity) hα herr‖ * Λ n * I *
      ((C + 1) * ε n) ≤ δ n / 2 := by
    calc
      _ ≤ R * Λ n * I * ((C + 1) * ε n) := hboundstart
      _ ≤ (1 / 2) * δ n := (div_le_iff₀ hn.2).mp hstartn.le
      _ = δ n / 2 := by ring
  obtain ⟨u, hu, hup, hueq, _, h, hnorm, hv⟩ := A.exists_positive_factor_of_bounds hd B ht
    (b n) (s n) (hb n) (hsmooth n) hbpos e c σ β he hc hσ hβ
    (Λ n) (δ n) K U (ε n) C V hΛn hn.2.le hδn.le le_rfl le_rfl hce hσe hcs
    hα herr hsmall' hstart' hJδn
  exact ⟨u, hu, hup, hueq, h, hnorm, hv⟩
end CompactMetricAtlas
end YauCounterexamples

end

end OAI
