import OAI.Geometry.RCD.Heat.BoundedHeatLogarithmicHessian
import OAI.Geometry.RCD.Sobolev.HessianScaledVelocity

namespace OAI

/-! # Exact velocity-minus-osmotic decomposition for the heat Hessian term

The local logarithms and all their Gram representatives are constructed.
The identity retains the actual product density and the physical scale.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  [(hausdorff n X).Regular] [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n) (p : X)

include hn p in
theorem bounded_heat_velocity_hessian
    (f g h : Lp ℝ 2 (hausdorff n X)) (A B C : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A)
    (hg : ∀ᵐ x ∂hausdorff n X, |g x| ≤ B)
    (hh : ∀ᵐ x ∂hausdorff n X, |h x| ≤ C)
    {s t a : ℝ} (hs : 0 < s) (ht : 0 < t) (ha : 0 < a) (c : ℝ)
    {Ω : Set X} (hΩ : IsCompact Ω)
    (hposf : ∀ x ∈ Ω, 0 < kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) s f x)
    (hposg : ∀ x ∈ Ω, 0 < kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) t g x) :
    let m := hausdorff n X
    let Q := hX.quadratic
    let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
    let u := heatSobolev m Q s hs f
    let v := heatSobolev m Q t ht g
    let w := heatSobolev m Q a ha h
    ∃ wu wv uv θ η wθ wη Gθ Gη : SobolevSpace m Q,
      (SobolevSpace.toLp m Q wu =ᵐ[m] localGamma m Q w u) ∧
      (SobolevSpace.toLp m Q wv =ᵐ[m] localGamma m Q w v) ∧
      (SobolevSpace.toLp m Q uv =ᵐ[m] localGamma m Q u v) ∧
      (SobolevSpace.toLp m Q θ =ᵐ[m.restrict Ω] fun x =>
        c*(Real.log (kernelHeat m Q hk t g x)-Real.log (kernelHeat m Q hk s f x))) ∧
      (SobolevSpace.toLp m Q η =ᵐ[m.restrict Ω] fun x =>
        c*(Real.log (kernelHeat m Q hk t g x)+Real.log (kernelHeat m Q hk s f x))) ∧
      (SobolevSpace.toLp m Q wθ =ᵐ[m.restrict Ω] localGamma m Q w θ) ∧
      (SobolevSpace.toLp m Q wη =ᵐ[m.restrict Ω] localGamma m Q w η) ∧
      (SobolevSpace.toLp m Q Gθ =ᵐ[m.restrict Ω] localGamma m Q θ θ) ∧
      (SobolevSpace.toLp m Q Gη =ᵐ[m.restrict Ω] localGamma m Q η η) ∧
      (fun x => kernelHeat m Q hk s f x*kernelHeat m Q hk t g x*
        (localHessianAction m Q w θ θ wθ wθ Gθ x-
          localHessianAction m Q w η η wη wη Gη x)) =ᵐ[m.restrict Ω]
        fun x => -4*c^2*localHessianAction m Q w u v wu wv uv x := by
  intro m Q hk u v w
  obtain ⟨wu,wv,uv,U,V,wU,wV,UU,VV,UV,hwu,hwv,huv,hU,hV,hwU,hwV,hUU,hVV,hUV,hH⟩ :=
    hX.bounded_heat_logarithmic_hessian hn p f g h A B C hf hg hh hs ht ha hΩ hposf hposg
  let θ := c • (V-U)
  let η := c • (V+U)
  let wθ := c • (wV-wU)
  let wη := c • (wV+wU)
  let Gθ := (c^2) • (UU+VV-(2:ℝ) • UV)
  let Gη := (c^2) • (UU+VV+(2:ℝ) • UV)
  have hθ : SobolevSpace.toLp m Q θ =ᵐ[m.restrict Ω] fun x =>
      c*(Real.log (kernelHeat m Q hk t g x)-Real.log (kernelHeat m Q hk s f x)) := by
    filter_upwards [hU,hV,ae_restrict_of_ae (Lp.coeFn_sub
      (SobolevSpace.toLp m Q V) (SobolevSpace.toLp m Q U)),
      ae_restrict_of_ae (Lp.coeFn_smul c (SobolevSpace.toLp m Q (V-U)))]
      with x hux hvx hd hc
    change (c • (SobolevSpace.toLp m Q V-SobolevSpace.toLp m Q U)) x=_
    simp only [map_sub] at hc
    rw [hc]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hd]
    simp only [Pi.sub_apply]
    rw [hux,hvx]
  have hη : SobolevSpace.toLp m Q η =ᵐ[m.restrict Ω] fun x =>
      c*(Real.log (kernelHeat m Q hk t g x)+Real.log (kernelHeat m Q hk s f x)) := by
    filter_upwards [hU,hV,ae_restrict_of_ae (Lp.coeFn_add
      (SobolevSpace.toLp m Q V) (SobolevSpace.toLp m Q U)),
      ae_restrict_of_ae (Lp.coeFn_smul c (SobolevSpace.toLp m Q (V+U)))]
      with x hux hvx hd hc
    change (c • (SobolevSpace.toLp m Q V+SobolevSpace.toLp m Q U)) x=_
    simp only [map_add] at hc
    rw [hc]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hd]
    simp only [Pi.add_apply]
    rw [hux,hvx]
  have hwθ : SobolevSpace.toLp m Q wθ =ᵐ[m.restrict Ω] localGamma m Q w θ := by
    filter_upwards [hwU,hwV,ae_restrict_of_ae (Lp.coeFn_sub
      (SobolevSpace.toLp m Q wV) (SobolevSpace.toLp m Q wU)),
      ae_restrict_of_ae (Lp.coeFn_smul c (SobolevSpace.toLp m Q (wV-wU))),
      ae_restrict_of_ae (localGamma_smul_right m Q c w (V-U)),
      ae_restrict_of_ae (localGamma_sub_right m Q w V U)]
      with x hux hvx hd hc hg he
    change (c • (SobolevSpace.toLp m Q wV-SobolevSpace.toLp m Q wU)) x=_
    simp only [map_sub] at hc
    rw [hc]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hd]
    simp only [Pi.sub_apply]
    change _ = localGamma m Q w (c • (V-U)) x
    rw [hux,hvx,hg,he]
  have hwη : SobolevSpace.toLp m Q wη =ᵐ[m.restrict Ω] localGamma m Q w η := by
    filter_upwards [hwU,hwV,ae_restrict_of_ae (Lp.coeFn_add
      (SobolevSpace.toLp m Q wV) (SobolevSpace.toLp m Q wU)),
      ae_restrict_of_ae (Lp.coeFn_smul c (SobolevSpace.toLp m Q (wV+wU))),
      ae_restrict_of_ae (localGamma_smul_right m Q c w (V+U)),
      ae_restrict_of_ae (localGamma_add_right m Q w V U)]
      with x hux hvx hd hc hg he
    change (c • (SobolevSpace.toLp m Q wV+SobolevSpace.toLp m Q wU)) x=_
    simp only [map_add] at hc
    rw [hc]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hd]
    simp only [Pi.add_apply]
    change _ = localGamma m Q w (c • (V+U)) x
    rw [hux,hvx,hg,he]
  obtain ⟨hGθ,hGη⟩ := localGamma_velocity_square_reps m Q U V UU VV UV hUU hVV hUV
  refine ⟨wu,wv,uv,θ,η,wθ,wη,Gθ,Gη,hwu,hwv,huv,hθ,hη,hwθ,hwη,
    localGamma_scaled_square_rep m Q (V-U) _ c hGθ,
    localGamma_scaled_square_rep m Q (V+U) _ c hGη,?_⟩
  filter_upwards [hH,ae_restrict_of_ae
    (localHessianAction_scaled_velocity m Q w U V wU wV UU VV UV c)] with x hh hs
  rw [hs]
  calc
    _ = -4*c^2*(kernelHeat m Q hk s f x*kernelHeat m Q hk t g x*
        localHessianAction m Q w U V wU wV UV x) := by ring
    _ = _ := by rw [hh]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
