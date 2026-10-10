import OAI.Geometry.RCD.Heat.ScaledHeatGramBound

namespace OAI

/-! # Uniform rescaled energy of the actual heat-frame coefficients -/

open Set Filter MeasureTheory Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.heat_frame_uniform_energy {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p : X) {r η C D : ℝ} (hr : 0<r) (hη : 0<η) (hη1 : η≤1)
    (hC : 0≤C) (hcurv : (-K)*r^2≤1)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p r C)
    (U : Fin n → compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    (q : Fin n → Lp ℝ 2 (hausdorff n X))
    (hq : ∀ i, IsWeakLaplacian (hausdorff n X) hX.quadratic (U i).val (q i))
    (hq0 : ∀ i, q i =ᵐ[(hausdorff n X).restrict (ball p (4*r))] fun _ => 0)
    (hU : ∀ i, ∀ᵐ x ∂(hausdorff n X).restrict (ball p r),
      localGamma (hausdorff n X) hX.quadratic (U i).val (U i).val x≤4)
    (he : ∀ i, (∫ x in closedBall p (2*r),
      |localGamma (hausdorff n X) hX.quadratic (U i).val (U i).val x-1| ∂hausdorff n X)≤
        D*(hausdorff n X).real (ball p (4*r)))
    (h : Lp ℝ 2 (hausdorff n X)) (V : X → ℝ) (L A a : ℝ≥0)
    (hV : LipschitzWith L V) (hVc : HasCompactSupport V)
    (hrep : V =ᵐ[hausdorff n X] h) (hA : ∀ᵐ x ∂hausdorff n X, |h x|≤A)
    (hscale : (A:ℝ)≤a*r) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    let hs : 0<η*r^2 := mul_pos hη (sq_pos_of_pos hr)
    let w := heatSobolev μ Q (η*r^2) hs h
    let H := (L:ℝ)*Real.exp 1
    let B := 2*(n:ℝ)*(1+1/η)*(a:ℝ)
    let M := 2*H^2*((C/2+1)*D+1)+8*((C/2+1)*H^2+B^2+B*H*C)
    ∃ G : Fin n → SobolevSpace μ Q,
      (∀ i, SobolevSpace.toLp μ Q (G i) =ᵐ[μ.restrict (ball p (4*r))] localGamma μ Q (U i).val w) ∧
      ∀ i, r^2*(∫ x in ball p r, localGamma μ Q (G i) (G i) x ∂μ)≤
        M*μ.real (ball p (4*r)) := by
  intro μ Q hs w H B M
  obtain ⟨G,hG,hGE⟩ := hX.heat_frame_gram_bound hn hK p hr hs hC χ U q hq hq0 hU h V L A hV hVc hrep hA
  let ℓ := (L:ℝ)*Real.exp (-K*(η*r^2))
  let b := (2*(n:ℝ)*(|K|+1/(η*r^2)))*(A:ℝ)
  have hℓ0 : 0≤ℓ := by dsimp only [ℓ]; positivity
  have hb0 : 0≤b := by dsimp only [b]; positivity
  have hℓ : ℓ≤H := by
    apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
    apply Real.exp_le_exp.mpr
    calc
      -K*(η*r^2) = η*((-K)*r^2) := by ring
      _ ≤ η*1 := mul_le_mul_of_nonneg_left hcurv hη.le
      _ ≤ 1 := by simpa only [mul_one] using hη1
  have hb : r*b≤B := by
    have hh := scaled_heat_source_bound hr hη (neg_nonneg.mpr hK) a.coe_nonneg
      (Nat.cast_nonneg n) hcurv hscale
    simpa only [b,B,abs_of_nonpos hK] using hh
  have hmass : μ.real (closedBall p (2*r))≤μ.real (ball p (4*r)) :=
    measureReal_mono (closedBall_subset_ball (by linarith)) (hX.finiteOnBounded _ isBounded_ball).ne
  refine ⟨G,hG,?_⟩
  intro i
  exact scaled_heat_gram_energy_bound hr hC (neg_nonneg.mpr hK) hℓ0 hb0 hℓ hb
    (integral_nonneg (fun _ => abs_nonneg _)) ENNReal.toReal_nonneg hcurv
    (he i) hmass (hGE i)

end RegularPointCoordinates

end

end OAI
