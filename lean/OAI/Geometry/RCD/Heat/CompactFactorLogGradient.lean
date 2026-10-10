import OAI.Geometry.RCD.Transport.CompactFactorMidpoint
import OAI.Geometry.RCD.Heat.KernelHeatLogarithmicEquation
import OAI.Geometry.RCD.Heat.HeatLogarithmicSlopeBound

namespace OAI

/-! # Quadratic growth of the logarithmic heat-factor gradient

The constants are independent of the endpoint scaling function and its
amplitude. This is the short-time specialization of the estimate used in
Gigli--Tamanini, JEMS 23 (2021), Theorem 3.3. The local logarithm and its
weak Laplacian are constructed on each compact region.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_factor_log_gradient :
    ∃ C D : ℝ, 0≤C ∧ 0<D ∧
      ∀ {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
        (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0≤ρ x) {B : ℝ≥0},
        (∀ᵐ x ∂hausdorff n X, |ρ x|≤B) →
        ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)) →
        ∀ (F : C(S, ℝ)), (∀ a, 0<F a) → ∀ (t : ℝ) (ht : 0<t), t≤1/2 →
        ∀ (z : X) (R : ℝ), 0≤R → (∀ a : S, dist z a≤R) →
        ∀ (Ω : Set X), IsCompact Ω →
        ∃ (v : SobolevSpace (hausdorff n X) hX.quadratic) (q : Lp ℝ 2 (hausdorff n X)),
          IsWeakLaplacian (hausdorff n X) hX.quadratic v q ∧
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[(hausdorff n X).restrict Ω]
            fun x => Real.log (hX.compactHeatFactor hn p ν F (2*t) (by positivity) x)) ∧
          ∀ᵐ x ∂(hausdorff n X).restrict Ω,
            t*Real.exp (-2*|K| * t)*(SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic v x)^2≤
              C+D*(R+dist z x)^2/t := by
  obtain ⟨C,D,hC,hD,hdata⟩ := hX.compact_heat_factor_midpoint hn p
  refine ⟨C,D,hC,hD,?_⟩
  intro S _ ν _ ρ hρ hρ0 B hB hν F hF t ht ht1 z R hR hdist Ω hΩ
  let μ := hausdorff n X
  let Q := hX.quadratic
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  obtain ⟨g,A,_hA,hg0,hgA,he,hgap⟩ := hdata ν ρ hρ hρ0 hB hν F hF t ht ht1
  have hH (x : X) : kernelHeat μ Q hk t g x=
      hX.compactHeatFactor hn p ν F (2*t) (by positivity) x := by
    simpa only [two_mul] using he t ht x
  have hpos (x : X) : 0<kernelHeat μ Q hk t g x := by
    rw [hH]
    exact hX.compactHeatFactor_positive hn p ν F hF (2*t) (by positivity) x
  obtain ⟨u,v,q,hu,hq,hv,_hd,hchain⟩ :=
    hX.kernelHeat_logarithmic_equation hn p hk g A hgA ht hΩ (fun x _ => hpos x)
  have hrep := kernelHeat_represents_L2 μ Q hk ht g
  have huc : u=heatSobolev μ Q t ht g := by
    apply Subtype.ext
    exact Lp.ext (hu.symm.trans hrep)
  have hposAE : ∀ᵐ x ∂μ.restrict Ω, 0<heatAt μ Q t g x := by
    filter_upwards [ae_restrict_of_ae hrep] with x hx
    exact hx ▸ hpos x
  have hc (w : SobolevSpace μ Q) : localGamma μ Q v w =ᵐ[μ.restrict Ω]
      fun x => localGamma μ Q (heatSobolev μ Q t ht g) w x/heatAt μ Q t g x := by
    filter_upwards [hchain w,ae_restrict_of_ae hrep] with x hx hy
    rw [huc,hy] at hx
    exact hx
  have hb := hX.heat_logarithmic_slope_bound hn p g hg0 A hgA ht v hposAE hc
  refine ⟨v,q,hq,?_,?_⟩
  · filter_upwards [hv] with x hx
    exact hx.trans (congrArg Real.log (hH x))
  · filter_upwards [hb,ae_restrict_of_ae hrep] with x hx hy
    have hr := hgap x (R+dist z x) (add_nonneg hR dist_nonneg) (fun a => by
      calc
        dist x a ≤ dist x z+dist z a := dist_triangle x z a
        _ ≤ dist x z+R := add_le_add le_rfl (hdist a)
        _ = R+dist z x := by rw [dist_comm x z]; ring)
    rw [←hy,hH] at hx
    exact hx.trans hr

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
