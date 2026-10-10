import OAI.Geometry.RCD.Heat.BoundedHeatSobolevData

namespace OAI

/-! # Actual regular heat approximations to a compact Lipschitz direction -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p in
theorem compact_lipschitz_heat_directions
    (v : SobolevSpace (hausdorff n X) hX.quadratic)
    (V : X → ℝ) (L A : ℝ≥0) (hV : LipschitzWith L V) (hc : HasCompactSupport V)
    (hv : SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[hausdorff n X] V)
    (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic v x| ≤ A) :
    let m := hausdorff n X
    let q := hX.quadratic
    ∃ (u : ℕ → SobolevSpace m q) (d : ℕ → Lp ℝ 2 m)
      (U : ℕ → X → ℝ) (M : ℕ → ℝ≥0) (P : ℝ),
      (∀ k, u k=heatH1 m q (1/(k+1:ℝ)) v) ∧
      (∀ k, IsWeakLaplacian m q (u k) (d k)) ∧
      (∀ k, LipschitzWith (M k) (U k)) ∧
      (∀ k, SobolevSpace.toLp m q (u k) =ᵐ[m] U k) ∧
      (∀ k, ∀ᵐ x ∂m, |SobolevSpace.toLp m q (u k) x| ≤ A) ∧
      0 ≤ P ∧ (∀ k, ∀ᵐ x ∂m, localGamma m q (u k) (u k) x ≤ P) ∧
      Tendsto u atTop (𝓝 v) := by
  intro m q
  let t (k : ℕ) : ℝ := 1/(k+1)
  have ht (k : ℕ) : 0 < t k := by dsimp only [t]; positivity
  have ht1 (k : ℕ) : t k ≤ 1 := by
    dsimp only [t]
    exact (div_le_one (by positivity : 0 < (k:ℝ)+1)).mpr (by
      have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
      linarith)
  let f := SobolevSpace.toLp m q v
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  let u k := heatSobolev m q (t k) (ht k) f
  let d k := -heatGenerator m q (t k) (ht k) f
  let U k := kernelHeat m q hk (t k) f
  let M (k : ℕ) : ℝ≥0 := ⟨Real.sqrt ((A:ℝ)^2/(2*t k*Real.exp (-2 * |K| * t k))),Real.sqrt_nonneg _⟩
  have hM (k : ℕ) : LipschitzWith (M k) (U k) :=
    (hX.kernelHeat_bounded_regularity hn p hk f A hA (t k) (ht k)).1
  let P := ((L:ℝ)*Real.exp |K|)^2
  have hu (k : ℕ) : u k=heatH1 m q (t k) v := by
    simp only [heatH1,dite_eq_left (ht k)]
    rfl
  have he (k : ℕ) : SobolevSpace.toLp m q (u k) =ᵐ[m] U k := by
    simpa only [u,heatSobolev_toLp] using (kernelHeat_represents_L2 m q hk (ht k) f).symm
  refine ⟨u,d,U,M,P,hu,fun k => heatSobolev_weak_laplacian m q (t k) (ht k) f,
    hM,he,fun k => (hX.bounded_heat_sobolev_data hn p f A hA (ht k)).1,
    sq_nonneg _,?_,?_⟩
  · intro k
    have hb := hX.heat_compact_slope_bdd K n hn hV hc p f hv.symm (t k) (ht k)
    have hExp : -K*t k ≤ |K| := by
      calc
        -K*t k ≤ |K| * t k := mul_le_mul_of_nonneg_right (neg_le_abs K) (ht k).le
        _ ≤ |K| := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (ht1 k) (abs_nonneg K)
    have hlarge : (L:ℝ)*Real.exp (-K*t k) ≤ (L:ℝ)*Real.exp |K| :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp) L.coe_nonneg
    filter_upwards [hb,localGamma_self m q (u k),
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg m q (u k))] with x hx he h0
    rw [he]
    exact pow_le_pow_left₀ h0 (hx.trans hlarge) 2
  · have hh := ((heatH1_continuous m q v).tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    rw [heatH1_zero] at hh
    exact hh.congr' (Eventually.of_forall fun k => (hu k).symm)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
