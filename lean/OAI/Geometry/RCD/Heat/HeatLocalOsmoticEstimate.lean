import OAI.Geometry.RCD.Heat.HeatLocalizedLiYau
import OAI.Geometry.RCD.Heat.HeatProductSourceCancellation
import OAI.Geometry.RCD.Heat.OsmoticEnergyAlgebra
import OAI.Geometry.RCD.Heat.BoundedHeatSobolevData

namespace OAI

/-! # A localized osmotic-energy estimate for the actual heat bridge

The coefficient of velocity energy tends to zero with the Li--Yau
parameter. The cutoff-gradient term is explicit and is not discarded.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p in
theorem heat_local_osmotic_estimate (hK : K ≤ 0) (α : ℝ) (hα : 1 < α)
    (f g : Lp ℝ 2 (hausdorff n X)) (A B : ℝ≥0) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A)
    (hg : ∀ᵐ x ∂hausdorff n X, |g x| ≤ B)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (φ : X → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (hφs : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hposf : ∀ x ∈ tsupport φ, 0 < kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) s f x)
    (hposg : ∀ x ∈ tsupport φ, 0 < kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) t g x) :
    let m := hausdorff n X
    let Q := hX.quadratic
    let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
    let F := kernelHeat m Q hk s f
    let G := kernelHeat m Q hk t g
    let u := heatSobolev m Q s hs f
    let v := heatSobolev m Q t ht g
    let w := SobolevSpace.ofLipschitzCompact m Q hφ hφs
    let S := (∫ x, φ x*(G x/F x)*localGamma m Q u u x ∂m)+
      (∫ x, φ x*(F x/G x)*localGamma m Q v v x ∂m)
    let E := weightedGamma m Q φ u v
    let J := weightedGamma m Q G u w+weightedGamma m Q F v w
    let R := ((n:ℝ)*α^2/2)*(2*|K|/(α-1)+1/s+1/t)*(∫ x, φ x*G x*F x ∂m)
    S+2*E ≤ ((α-1)/(α+1))*(S-2*E)+(2/(α+1))*(R-α*J) := by
  intro m Q hk F G u v w S E J R
  have h₁ := hX.heat_localized_liYau hn p hK α hα f g A B hf0 hg0 hf hg hs ht
    φ hφ.continuous hφs hφ0 hposf
  have h₂ := hX.heat_localized_liYau hn p hK α hα g f B A hg0 hf0 hg hf ht hs
    φ hφ.continuous hφs hφ0 hposg
  dsimp only at h₁ h₂
  have hu : SobolevSpace.toLp m Q u =ᵐ[m] F := by
    simpa only [u,heatSobolev_toLp] using (kernelHeat_represents_L2 m Q hk hs f).symm
  have hv : SobolevSpace.toLp m Q v =ᵐ[m] G := by
    simpa only [v,heatSobolev_toLp] using (kernelHeat_represents_L2 m Q hk ht g).symm
  have hw := SobolevSpace.ofLipschitzCompact_coe m Q hφ hφs
  obtain ⟨M,hM⟩ := hφs.exists_bound_of_continuous hφ.continuous
  let C : ℝ≥0 := ⟨max 0 M,le_max_left _ _⟩
  have hwB : ∀ᵐ x ∂m, |SobolevSpace.toLp m Q w x| ≤ C := by
    filter_upwards [hw] with x hx
    have hb : |φ x| ≤ M := by simpa only [Real.norm_eq_abs] using hM x
    exact hx ▸ hb.trans (le_max_right 0 M)
  have huB := (hX.bounded_heat_sobolev_data hn p f A hf hs).1
  have hvB := (hX.bounded_heat_sobolev_data hn p g B hg ht).1
  have hdu : IsWeakLaplacian m Q u (-heatGeneratorAt m Q s f) := by
    simpa only [heatGeneratorAt_of_pos m Q s hs] using heatSobolev_weak_laplacian m Q s hs f
  have hdv : IsWeakLaplacian m Q v (-heatGeneratorAt m Q t g) := by
    simpa only [heatGeneratorAt_of_pos m Q t ht] using heatSobolev_weak_laplacian m Q t ht g
  have hc := weakLaplacian_two_factor_source m Q u v w _ _ hdu hdv A B C huB hvB hwB
  have hwE : weightedGamma m Q (SobolevSpace.toLp m Q w) u v=E := by
    apply integral_congr_ae
    exact hw.mono fun x hx => congrArg (fun r => r*localGamma m Q u v x) hx
  have hvE : weightedGamma m Q (SobolevSpace.toLp m Q v) u w=weightedGamma m Q G u w := by
    apply integral_congr_ae
    exact hv.mono fun x hx => congrArg (fun r => r*localGamma m Q u w x) hx
  have huE : weightedGamma m Q (SobolevSpace.toLp m Q u) v w=weightedGamma m Q F v w := by
    apply integral_congr_ae
    exact hu.mono fun x hx => congrArg (fun r => r*localGamma m Q v w x) hx
  have hsu : (∫ x, SobolevSpace.toLp m Q w x*SobolevSpace.toLp m Q v x*
      (-heatGeneratorAt m Q s f) x ∂m) = ∫ x, φ x*G x*(-heatGeneratorAt m Q s f) x ∂m := by
    apply integral_congr_ae
    filter_upwards [hw,hv] with x hx hy
    rw [hx,hy]
  have hsv : (∫ x, SobolevSpace.toLp m Q w x*SobolevSpace.toLp m Q u x*
      (-heatGeneratorAt m Q t g) x ∂m) = ∫ x, φ x*F x*(-heatGeneratorAt m Q t g) x ∂m := by
    apply integral_congr_ae
    filter_upwards [hw,hu] with x hx hy
    rw [hx,hy]
  rw [hwE,hvE,huE,hsu,hsv] at hc
  have hm : (∫ x, φ x*F x*G x ∂m) = ∫ x, φ x*G x*F x ∂m :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [hm] at h₂
  change (∫ x, φ x*(G x/F x)*localGamma m Q u u x ∂m) ≤
    α*(∫ x, φ x*G x*(-heatGeneratorAt m Q s f) x ∂m)+
      (((n:ℝ)*α^2/2)*(|K|/(α-1)+1/s))*(∫ x, φ x*G x*F x ∂m) at h₁
  change (∫ x, φ x*(F x/G x)*localGamma m Q v v x ∂m) ≤
    α*(∫ x, φ x*F x*(-heatGeneratorAt m Q t g) x ∂m)+
      (((n:ℝ)*α^2/2)*(|K|/(α-1)+1/t))*(∫ x, φ x*G x*F x ∂m) at h₂
  apply osmotic_energy_algebra hα
  let d₁ := ∫ x, φ x*G x*(-heatGeneratorAt m Q s f) x ∂m
  let d₂ := ∫ x, φ x*F x*(-heatGeneratorAt m Q t g) x ∂m
  let mass := ∫ x, φ x*G x*F x ∂m
  change d₁+d₂ = -2*E-J at hc
  calc
    S ≤ (α*d₁+(((n:ℝ)*α^2/2)*(|K|/(α-1)+1/s))*mass)+
        (α*d₂+(((n:ℝ)*α^2/2)*(|K|/(α-1)+1/t))*mass) := add_le_add h₁ h₂
    _ = α*(d₁+d₂)+R := by dsimp only [R,mass]; ring
    _ = α*(-2*E-J)+R := by rw [hc]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
