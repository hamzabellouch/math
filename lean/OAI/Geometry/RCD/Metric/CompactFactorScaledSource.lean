import OAI.Geometry.RCD.Transport.CompactFactorMidpoint
import OAI.Geometry.RCD.Heat.KernelHeatLogarithmicLiYau
import OAI.Geometry.RCD.Heat.HeatLogarithmicSlopeBound
import OAI.Geometry.RCD.Heat.ScaledHamiltonBound
import OAI.Geometry.RCD.Heat.ScaledLiYauSource

namespace OAI

/-! # Uniform lower weak sources for scaled compact-factor logarithms

The source and gradient belong to the same local logarithm. The constants
are independent of the endpoint factor and of its normalization.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_factor_scaled_source (hK : K ≤ 0) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 < D ∧
      ∀ {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
        (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0},
        (∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B) →
        ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)) →
        ∀ (F : C(S, ℝ)), (∀ a, 0 < F a) →
        ∀ {ε s δ : ℝ} (hε : 0 < ε) (_hε1 : ε ≤ 1) (hδ : 0 < δ)
          (hδs : δ ≤ s) (_hs1 : s ≤ 1),
        ∀ (z : X) (R : ℝ), 0 ≤ R → (∀ a : S, dist z a ≤ R) →
        ∀ (Ω : Set X), IsCompact Ω →
        ∃ (v : SobolevSpace (hausdorff n X) hX.quadratic) (q : Lp ℝ 2 (hausdorff n X)),
          IsWeakLaplacian (hausdorff n X) hX.quadratic v q ∧
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[(hausdorff n X).restrict Ω]
            fun x => ε*Real.log (hX.compactHeatFactor hn p ν F (ε*s/2)
              (div_pos (mul_pos hε (hδ.trans_le hδs)) (by norm_num)) x)) ∧
          ∀ᵐ x ∂(hausdorff n X).restrict Ω,
            (SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic v x)^2 ≤
              Real.exp |K| *(4*C/δ+16*D*(R+dist z x)^2/δ^2) ∧
            -(Real.exp |K| *(4*C/δ+16*D*(R+dist z x)^2/δ^2)+
              2*(n:ℝ)*|K| +8*(n:ℝ)/δ) ≤ q x := by
  obtain ⟨C,D,hC,hD,hdata⟩ := hX.compact_heat_factor_midpoint hn p
  refine ⟨C,D,hC,hD,?_⟩
  intro S _ ν _ ρ hρ hρ0 B hB hν F hF ε s δ hε hε1 hδ hδs hs1 z R hR hdist Ω hΩ
  let m := hausdorff n X
  let Q := hX.quadratic
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  let t := ε*s/4
  have hs : 0 < s := hδ.trans_le hδs
  have ht : 0 < t := by dsimp only [t]; positivity
  have ht1 : t ≤ 1/2 := by
    have hm := mul_le_mul hε1 hs1 hs.le (by norm_num : (0:ℝ) ≤ 1)
    dsimp only [t]
    linarith
  have htime : 2*t = ε*s/2 := by dsimp only [t]; ring
  obtain ⟨g,A,_hA,hg0,hgA,he,hgap⟩ := hdata ν ρ hρ hρ0 hB hν F hF t ht ht1
  have hH (x : X) : kernelHeat m Q hk t g x =
      hX.compactHeatFactor hn p ν F (2*t) (by positivity) x := by
    simpa only [two_mul] using he t ht x
  have hpos (x : X) : 0 < kernelHeat m Q hk t g x := by
    rw [hH]
    exact hX.compactHeatFactor_positive hn p ν F hF (2*t) (by positivity) x
  obtain ⟨u,v,q,hu,hq,hv,hchain,hLY⟩ :=
    hX.kernelHeat_logarithmic_liYau hn p hK (1+ε) (by linarith)
      hk g hg0 A hgA ht hΩ (fun x _ => hpos x)
  have hrep := kernelHeat_represents_L2 m Q hk ht g
  have hue : u = heatSobolev m Q t ht g := by
    apply Subtype.ext
    exact Lp.ext (hu.symm.trans hrep)
  have hposAE : ∀ᵐ x ∂m.restrict Ω, 0 < heatAt m Q t g x := by
    filter_upwards [ae_restrict_of_ae hrep] with x hx
    exact hx ▸ hpos x
  have hc (w : SobolevSpace m Q) : localGamma m Q v w =ᵐ[m.restrict Ω]
      fun x => localGamma m Q (heatSobolev m Q t ht g) w x/heatAt m Q t g x := by
    filter_upwards [hchain w,ae_restrict_of_ae hrep] with x hx hy
    rw [hue,hy] at hx
    exact hx
  have hb := hX.heat_logarithmic_slope_bound hn p g hg0 A hgA ht v hposAE hc
  have hgrad : ∀ᵐ x ∂m.restrict Ω, t*Real.exp (-2*|K| *t)*
      (SobolevSpace.minimalSlope m Q v x)^2 ≤ C+D*(R+dist z x)^2/t := by
    filter_upwards [hb,ae_restrict_of_ae hrep] with x hx hy
    have hr := hgap x (R+dist z x) (add_nonneg hR dist_nonneg) (fun a => by
      calc
        dist x a ≤ dist x z+dist z a := dist_triangle x z a
        _ ≤ dist x z+R := add_le_add le_rfl (hdist a)
        _ = R+dist z x := by rw [dist_comm x z]; ring)
    rw [← hy,hH] at hx
    exact hx.trans hr
  refine ⟨ε • v,ε • q,hq.smul m Q ε,?_,?_⟩
  · filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul ε (SobolevSpace.toLp m Q v)),hv]
      with x hx hy
    change SobolevSpace.toLp m Q (ε • v) x = ε*SobolevSpace.toLp m Q v x at hx
    rw [hx,hy,hH]
    simp only [htime]
  · have hscale : SobolevSpace.minimalSlope m Q (ε • v) =ᵐ[m]
        fun x => ε*SobolevSpace.minimalSlope m Q v x := by
      rw [SobolevSpace.minimalSlope_smul_nonneg m Q v hε.le]
      exact Lp.coeFn_smul ε (SobolevSpace.minimalSlope m Q v)
    filter_upwards [hgrad,hLY,ae_restrict_of_ae hscale,
      ae_restrict_of_ae (Lp.coeFn_smul ε q),ae_restrict_of_ae (localGamma_self m Q v)]
      with x hx hly hsc hqs hself
    have hbound := scaled_hamilton_bound (abs_nonneg K) hC hD.le hε hε1 hδ hδs hs1 rfl hx
    rw [hsc]
    refine ⟨hbound,?_⟩
    change (ε • q) x = ε*q x at hqs
    rw [hqs]
    have hly' : localGamma m Q v v x ≤ (1+ε)*(q x+localGamma m Q v v x)+
        ((n:ℝ)*(1+ε)^2/2)*(|K|/ε+1/(ε*s/4)) := by
      dsimp only [t] at hly
      rw [show 1+ε-1 = ε by ring] at hly
      linarith
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hlower := scaled_liYau_source_bound hε hε1 hδ hδs hn0 (abs_nonneg K)
      (show 0 ≤ localGamma m Q v v x by rw [hself]; positivity) hly'
    rw [hself] at hlower
    nlinarith

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
