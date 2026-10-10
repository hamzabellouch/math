import OAI.Geometry.RCD.Sobolev.BoundedGlobalDimensionalBochner
import OAI.Geometry.RCD.Heat.FisherBochnerIdentity
import OAI.Geometry.RCD.Heat.ShiftedLogarithmSquare
import OAI.Geometry.RCD.Coordinates.RegularizedFisherInterpolation
import OAI.Geometry.RCD.Heat.HeatLogarithmData

namespace OAI

/-! # Dimensional curvature controls the actual Fisher interpolation

The logarithm, its source, and its squared gradient are the previously
constructed Sobolev functions. The test is the actual product of the two
heat evolutions, with the same positive regularization. The square of the
actual logarithmic Laplacian is retained.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates

def regularizedHeatLogSource {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [ProperSpace X] (μ : Measure X) [μ.Regular]
    (Q : QuadraticCheegerEnergy μ) (f : Lp ℝ 2 μ) (ε t : ℝ) (ht : 0<t) : X → ℝ :=
  fun x => (-heatGeneratorAt μ Q t f) x/(ε+heatAt μ Q t f x)-
    localGamma μ Q (heatSobolev μ Q t ht f) (heatSobolev μ Q t ht f) x /
      (ε+heatAt μ Q t f x)^2

namespace NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p

theorem regularizedFisherInterpolation_dimensional
    (hK : K≤0) (f w : Lp ℝ 2 (hausdorff n X)) (hf0 : 0≤f) (hw0 : 0≤w) (A B : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A) (hw : ∀ᵐ x ∂hausdorff n X, |w x|≤B)
    {T t ε : ℝ} (ht : 0<t) (htT : t<T) (hε : 0<ε) :
    ∃ d : ℝ, HasDerivAt (regularizedFisherInterpolation (hausdorff n X) hX.quadratic
      f w ε T) d t ∧
      2*K*regularizedFisherInterpolation (hausdorff n X) hX.quadratic f w ε T t+
        (2/(n:ℝ))*(∫ x, heatAt (hausdorff n X) hX.quadratic t w x *
          (ε+heatAt (hausdorff n X) hX.quadratic (T-t) f x) *
          (regularizedHeatLogSource (hausdorff n X) hX.quadratic f ε (T-t)
            (sub_pos.mpr htT) x)^2 ∂hausdorff n X)≤d := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  have hs : 0<T-t := sub_pos.mpr htT
  let u := heatSobolev μ Q (T-t) hs f
  let d := heatSobolevMap μ Q ((T-t)/2) (half_pos hs)
    (-heatGeneratorAt μ Q (T-t-(T-t)/2) f)
  let W := heatSobolev μ Q t ht w
  let v := hX.boundedHeat hn p f ⟨A,hf⟩ (T-t) hs
  let z := hX.boundedHeat hn p w ⟨B,hw⟩ t ht
  have hv := hX.boundedHeat_lipschitz hn p f ⟨A,hf⟩ (T-t) hs A hf
  have hz := hX.boundedHeat_lipschitz hn p w ⟨B,hw⟩ t ht B hw
  have hur : SobolevSpace.toLp μ Q u =ᵐ[μ] v :=
    hX.boundedHeat_represents hn p f ⟨A,hf⟩ (T-t) hs
  have hwr : SobolevSpace.toLp μ Q W =ᵐ[μ] z :=
    hX.boundedHeat_represents hn p w ⟨B,hw⟩ t ht
  have hu : ∀ᵐ x ∂μ, SobolevSpace.toLp μ Q u x∈Icc 0 (A:ℝ) := by
    filter_upwards [hur] with x hx
    rw [hx]
    exact ⟨hX.boundedHeat_nonneg hn p f ⟨A,hf⟩ (T-t) hs hf0 x,
      (le_abs_self _).trans (hX.boundedHeat_abs_le hn p f ⟨A,hf⟩ (T-t) hs A hf x)⟩
  have hW : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q W x|≤B := by
    simpa only [W,heatSobolev_toLp] using heatAt_abs_le_const μ Q t B w hw
  have hLu := SobolevSpace.minimalSlope_le_lipschitz μ Q u hv hur
  have hd : IsWeakLaplacian μ Q u (SobolevSpace.toLp μ Q d) :=
    heatTail_weak_laplacian μ Q (T-t) hs f
  have hdval : SobolevSpace.toLp μ Q d = -heatGeneratorAt μ Q (T-t) f :=
    IsWeakLaplacian.unique μ Q hd (by
      simpa only [heatGeneratorAt_of_pos μ Q (T-t) hs] using
        heatSobolev_weak_laplacian μ Q (T-t) hs f)
  have he : IsWeakLaplacian μ Q W (-heatGeneratorAt μ Q t w) := by
    simpa only [heatGeneratorAt_of_pos μ Q t ht] using heatSobolev_weak_laplacian μ Q t ht w
  obtain ⟨ℓ,S,H,C,L,hS,hH,hℓ,hLip,hC,hsource⟩ :=
    hX.heat_logarithm_sobolev_data hn p f hf0 A hf hs hε
  have hℓr : SobolevSpace.toLp μ Q ℓ =ᵐ[μ] fun x =>
      Real.log (ε+SobolevSpace.toLp μ Q u x)-Real.log ε := by
    filter_upwards [hℓ,hur] with x hx hy
    exact hx.trans (by rw [hy])
  have hLℓ := SobolevSpace.minimalSlope_le_lipschitz μ Q ℓ hLip hℓ
  have hHr := hH.trans (shifted_logarithm_gamma_self μ Q u ℓ hε A hu hℓr)
  have hHb := gamma_representative_bound μ Q ℓ H L hLℓ hH
  have hSr : SobolevSpace.toLp μ Q S =ᵐ[μ] fun x =>
      SobolevSpace.toLp μ Q d x/(ε+SobolevSpace.toLp μ Q u x)-SobolevSpace.toLp μ Q H x := by
    filter_upwards [hsource,hur,hHr] with x hx hy hh
    change SobolevSpace.toLp μ Q S x = _ at hx
    rw [hx,hh,hdval,hy]
  obtain ⟨R,N,hRr,hRb,hidentity⟩ := fisher_bochner_identity μ Q u d W ℓ S H
    (-heatGeneratorAt μ Q t w) K hd he hS hε A B (L^2) _ L hu hW
    (by simpa only [NNReal.coe_pow] using hHb) hLu hLℓ hℓr hHr hSr
  let q : X → ℝ := fun x => (ε+v x)*z x
  have hq : Continuous q := (continuous_const.add hv.continuous).mul hz.continuous
  have hq0 (x : X) : 0≤q x :=
    mul_nonneg (add_nonneg hε.le (hX.boundedHeat_nonneg hn p f ⟨A,hf⟩ (T-t) hs hf0 x))
      (hX.boundedHeat_nonneg hn p w ⟨B,hw⟩ t ht hw0 x)
  have hqb (x : X) : |q x|≤((⟨ε,hε.le⟩+A)*B:ℝ≥0) := by
    change |(ε+v x)*z x|≤(ε+(A:ℝ))*(B:ℝ)
    rw [abs_mul]
    apply mul_le_mul _ (hX.boundedHeat_abs_le hn p w ⟨B,hw⟩ t ht B hw x) (abs_nonneg _) (by positivity)
    exact (abs_add_le _ _).trans (add_le_add (by rw [abs_of_pos hε])
      (hX.boundedHeat_abs_le hn p f ⟨A,hf⟩ (T-t) hs A hf x))
  have hRq : SobolevSpace.toLp μ Q R =ᵐ[μ] q := by
    filter_upwards [hRr,hur,hwr] with x hx hy hz
    rw [hx,hy,hz]
  have hboch := hX.bounded_global_dimensional_bochner hn hK p ℓ S H R hS _ hLip hℓ C hC hH
    q hq ((⟨ε,hε.le⟩+A)*B) hqb hq0 hRq
  have hderiv := hX.regularizedFisherInterpolation_hasDerivAt hn p f w hf0 A B hf hw ht htT hε
  dsimp only at hderiv
  refine ⟨_,hderiv,?_⟩
  have hSactual : SobolevSpace.toLp μ Q S =ᵐ[μ]
      regularizedHeatLogSource μ Q f ε (T-t) hs := by
    filter_upwards [hsource,hur] with x hx hy
    change heatAt μ Q (T-t) f x = v x at hy
    change SobolevSpace.toLp μ Q S x = _ at hx
    change SobolevSpace.toLp μ Q S x =
      (-heatGeneratorAt μ Q (T-t) f) x/(ε+heatAt μ Q (T-t) f x)-
        localGamma μ Q u u x/(ε+heatAt μ Q (T-t) f x)^2
    rw [hy]
    exact hx
  have hsq : (∫ x, q x*(SobolevSpace.toLp μ Q S x)^2 ∂μ) =
      ∫ x, heatAt μ Q t w x*(ε+heatAt μ Q (T-t) f x)*
        (regularizedHeatLogSource μ Q f ε (T-t) hs x)^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hSactual,hur,hwr] with x hx hy hz
    change heatAt μ Q (T-t) f x = v x at hy
    change heatAt μ Q t w x = z x at hz
    dsimp only [q]
    rw [hy,hz,hx]
    ring
  have hsqR : (∫ x, q x*(SobolevSpace.toLp μ Q S x)^2 ∂μ) =
      ∫ x, SobolevSpace.toLp μ Q R x*(SobolevSpace.toLp μ Q S x)^2 ∂μ := by
    apply integral_congr_ae
    exact hRq.symm.mono fun x hx => congrArg (fun a => a*(SobolevSpace.toLp μ Q S x)^2) hx
  rw [hsqR] at hboch
  have hineq : 2*K*(∫ x, SobolevSpace.toLp μ Q W x*localGamma μ Q u u x /
      (ε+SobolevSpace.toLp μ Q u x) ∂μ)+
      (2/(n:ℝ))*(∫ x, q x*(SobolevSpace.toLp μ Q S x)^2 ∂μ) ≤
      2*(bochnerTestForm μ Q (-K) H R-weightedGamma μ Q (SobolevSpace.toLp μ Q R) ℓ S)+
      2*K*(∫ x, SobolevSpace.toLp μ Q W x*localGamma μ Q u u x /
        (ε+SobolevSpace.toLp μ Q u x) ∂μ) := by
    rw [hsqR]
    simp only [div_eq_mul_inv] at hboch ⊢
    linarith only [hboch]
  rw [←hidentity,hsq] at hineq
  simpa only [u,W,d,heatSobolev_toLp,regularizedFisherInterpolation,dite_eq_left hs] using hineq

end NoncollapsedRCD
end RegularPointCoordinates

end

end OAI
