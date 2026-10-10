import OAI.Geometry.RCD.Metric.CompactFactorScaledSource
import OAI.Geometry.RCD.Sobolev.LocalLaplacianMass

namespace OAI

/-! # Uniform local absolute source mass of the actual scaled heat logs -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p in
theorem compact_heat_local_source_mass (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (z : X) {R r δ : ℝ} (hR : 0 ≤ R) (hr : 0<r)
    (hdist : ∀ y:S, dist z y ≤ R) (hδ : 0<δ)
    (χ : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ)
    (hv : SobolevSpace.toLp (hausdorff n X) hX.quadratic χ =ᵐ[hausdorff n X] v)
    (hvi : Integrable v (hausdorff n X)) (hv0 : ∀ x, 0 ≤ v x)
    (hvzero : ∀ x ∉ closedBall z r, v x=0) (M : ℝ≥0)
    (hχM : ∀ᵐ x ∂hausdorff n X,
      SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic χ x ≤ M) :
    ∃ (L : ℝ≥0) (A : ℝ), 0 ≤ A ∧ ∀ (F : C(S,ℝ)), (∀ y, 0<F y) →
      ∀ {ε s : ℝ} (hε : 0<ε) (_hε1 : ε ≤ 1) (hδs : δ ≤ s) (_hs1 : s ≤ 1),
      ∃ (u : SobolevSpace (hausdorff n X) hX.quadratic) (q : Lp ℝ 2 (hausdorff n X)),
        IsWeakLaplacian (hausdorff n X) hX.quadratic u q ∧
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic u
          =ᵐ[(hausdorff n X).restrict (closedBall z r)] fun x => ε*Real.log
            (hX.compactHeatFactor hn p ν F (ε*s/2)
              (div_pos (mul_pos hε (hδ.trans_le hδs)) (by norm_num)) x)) ∧
        (∀ᵐ x ∂(hausdorff n X).restrict (closedBall z r),
          SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic u x ≤ L) ∧
        Integrable (fun x => v x*|q x|) (hausdorff n X) ∧
        (∫ x, v x*|q x| ∂hausdorff n X) ≤ A := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  obtain ⟨C,D,hC,hD,hdata⟩ := hX.compact_heat_factor_scaled_source hn p hK
  let H := Real.exp |K| *(4*C/δ+16*D*(R+r)^2/δ^2)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  let L : ℝ≥0 := ⟨Real.sqrt H,Real.sqrt_nonneg H⟩
  let E := H+2*(n:ℝ)*|K|+8*(n:ℝ)/δ
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  let A := (L:ℝ)*M*μ.real (closedBall z r)+2*E*(∫ x, v x ∂μ)
  have hiv0 : 0 ≤ ∫ x, v x ∂μ := integral_nonneg hv0
  refine ⟨L,A,by dsimp only [A]; positivity,?_⟩
  intro F hF ε s hε hε1 hδs hs1
  obtain ⟨u,q,hq,hu,hb⟩ := hdata ν ρ hρ hρ0 hB hν F hF hε hε1 hδ hδs hs1 z R hR hdist
    (closedBall z r) (isCompact_closedBall z r)
  have hbound : ∀ᵐ x ∂μ.restrict (closedBall z r),
      SobolevSpace.minimalSlope μ Q u x ≤ L ∧ -E ≤ q x := by
    filter_upwards [hb,ae_restrict_mem measurableSet_closedBall]
      with x hx hmem
    have hxr : dist z x ≤ r := by simpa only [dist_comm] using mem_closedBall.mp hmem
    have hpow : (R+dist z x)^2 ≤ (R+r)^2 :=
      pow_le_pow_left₀ (add_nonneg hR dist_nonneg) (by linarith) 2
    have hcoef : Real.exp |K| *(4*C/δ+16*D*(R+dist z x)^2/δ^2) ≤ H := by
      dsimp only [H]
      gcongr
    have hslope : (SobolevSpace.minimalSlope μ Q u x)^2 ≤ H := hx.1.trans hcoef
    refine ⟨Real.le_sqrt_of_sq_le hslope,?_⟩
    dsimp only [E]
    linarith [hx.2]
  obtain ⟨hi,hm⟩ := local_laplacian_mass μ Q u χ q hq v hv hvi hv0 measurableSet_closedBall
    (isCompact_closedBall z r).measure_lt_top.ne hvzero L M
    (hbound.mono fun _ hx => hx.1) hχM hE (hbound.mono fun _ hx => hx.2)
  exact ⟨u,q,hq,hu,hbound.mono fun _ hx => hx.1,hi,hm⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
