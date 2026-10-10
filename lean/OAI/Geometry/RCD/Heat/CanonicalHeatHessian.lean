import OAI.Geometry.RCD.Heat.CompactLipschitzHeatHessian
import OAI.Geometry.RCD.Sobolev.HessianL1LimitUniqueness
import OAI.Geometry.RCD.Sobolev.HessianActionRepresentatives

namespace OAI

/-! # The canonical local Hessian action defined by heat approximation -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (Q : QuadraticCheegerEnergy μ)

def IsCanonicalHeatHessian (w v : SobolevSpace μ Q) (p : X) (r : ℝ) (φ : X → ℝ)
    (J : Lp ℝ 1 (μ.restrict (closedBall p r))) : Prop :=
  let u (k : ℕ) := heatH1 μ Q (1/(k+1:ℝ)) v
  ∃ WU UU : ℕ → SobolevSpace μ Q,
    (∀ k, SobolevSpace.toLp μ Q (WU k) =ᵐ[μ.restrict (closedBall p r)] localGamma μ Q w (u k)) ∧
    (∀ k, SobolevSpace.toLp μ Q (UU k) =ᵐ[μ.restrict (closedBall p r)] localGamma μ Q (u k) (u k)) ∧
    Tendsto (fun k => ∫ x in closedBall p r,
      |φ x*localHessianAction μ Q w (u k) (u k) (WU k) (WU k) (UU k) x-J x| ∂μ)
      atTop (𝓝 0)

theorem IsCanonicalHeatHessian.unique {w v : SobolevSpace μ Q} {p : X} {r : ℝ} {φ : X → ℝ}
    (hφ : AEStronglyMeasurable φ μ) (D : ℝ≥0) (hD : ∀ᵐ x ∂μ, |φ x| ≤ D)
    {I J : Lp ℝ 1 (μ.restrict (closedBall p r))}
    (hI : IsCanonicalHeatHessian μ Q w v p r φ I)
    (hJ : IsCanonicalHeatHessian μ Q w v p r φ J) : I=J := by
  obtain ⟨A,B,hA,hB,hIl⟩ := hI
  obtain ⟨C,D',hC,hD',hJl⟩ := hJ
  let u (k : ℕ) := heatH1 μ Q (1/(k+1:ℝ)) v
  let F k x := φ x*localHessianAction μ Q w (u k) (u k) (A k) (A k) (B k) x
  let G k x := φ x*localHessianAction μ Q w (u k) (u k) (C k) (C k) (D' k) x
  have hb : ∀ᵐ x ∂μ, ‖φ x‖ ≤ D := by simpa only [Real.norm_eq_abs] using hD
  have hiF (k : ℕ) : Integrable (F k) (μ.restrict (closedBall p r)) :=
    ((localHessianAction_integrable μ Q w (u k) (u k) (A k) (A k) (B k)).bdd_mul hφ hb).integrableOn
  have hiG (k : ℕ) : Integrable (G k) (μ.restrict (closedBall p r)) :=
    ((localHessianAction_integrable μ Q w (u k) (u k) (C k) (C k) (D' k)).bdd_mul hφ hb).integrableOn
  apply L1_limits_eq_of_difference (μ.restrict (closedBall p r)) F G hiF hiG I J hIl hJl
  have he (k : ℕ) : (∫ x in closedBall p r, |F k x-G k x| ∂μ)=0 := by
    have hh := localHessianAction_congr_of_grams μ Q w (u k) (u k) (u k) (u k)
      (A k) (C k) (A k) (C k) (B k) (D' k) EventuallyEq.rfl EventuallyEq.rfl
      (hA k) (hC k) (hA k) (hC k) (hB k) (hD' k)
    apply integral_eq_zero_of_ae
    filter_upwards [hh] with x hx
    simp only [F,G,hx,sub_self,abs_zero,Pi.zero_apply]
  simpa only [he] using (tendsto_const_nhds (x := (0:ℝ)))

theorem NoncollapsedRCD.exists_canonical_heat_hessian {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (p : X)
    [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] (hK : K ≤ 0)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (v : SobolevSpace (hausdorff n X) hX.quadratic)
    (V : X → ℝ) (Lv Av : ℝ≥0) (hV : LipschitzWith Lv V) (hc : HasCompactSupport V)
    (hv : SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[hausdorff n X] V)
    (hAv : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic v x| ≤ Av)
    (φ : X → ℝ) (hφ : AEStronglyMeasurable φ (hausdorff n X)) (D : ℝ≥0)
    (hD : ∀ᵐ x ∂hausdorff n X, |φ x| ≤ D) (hz : ∀ x ∉ closedBall p r, φ x = 0) :
    ∃! J : Lp ℝ 1 ((hausdorff n X).restrict (closedBall p r)),
      IsCanonicalHeatHessian (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic a ha f) v p r φ J := by
  obtain ⟨u,WU,UU,J,hu,hWU,hUU,hJ⟩ := hX.compact_lipschitz_hessian_limit hn p hK f A hf ha hr
    v V Lv Av hV hc hv hAv φ hφ D hD hz
  have hcan : IsCanonicalHeatHessian (hausdorff n X) hX.quadratic
      (heatSobolev (hausdorff n X) hX.quadratic a ha f) v p r φ J := by
    refine ⟨WU,UU,?_,?_,?_⟩
    · simpa only [hu] using hWU
    · simpa only [hu] using hUU
    · simpa only [hu] using hJ
  exact ⟨J,hcan,fun I hI => hI.unique (hausdorff n X) hX.quadratic hφ D hD hcan⟩

end RegularPointCoordinates

end

end OAI
