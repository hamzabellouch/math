import OAI.Geometry.RCD.Heat.SmallRadiusHeatSecondVariation
import OAI.Geometry.RCD.Harmonic.BalancedQuadraticError
import OAI.Geometry.RCD.Heat.HeatMeanStrongLimit

namespace OAI

/-! # Original-potential means at the physical source scale

The balanced Young estimate retains the product of volume and shifted mass.
Its action coefficient is uniform in the center and has fourth-order radius
scaling, as required for shrinking balls.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X} {hn : 2≤n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0<ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)
attribute [local instance] pathBorel pathBorelSpace

theorem small_radius_original_mean_estimate (p₀ : X) (a₀ : S) (b₀ : T) (hK : K≤0)
    (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0≤ρ₀ x) (hp₁ : ∀ x, 0≤ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x|≤C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x|≤C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R : ℝ} (hR : 0<R) (hS : ∀ y:S, dist p y≤R) (hT : ∀ y:T, dist p y≤R)
    (j : ℕ → ℕ) (hj : StrictMono j) (Q₀ : Ioo (0:ℝ) 1 → ProbabilityMeasure X)
    (hweak : ∀ t, Tendsto (fun k => D.interpolationLaw (D.index (j k)) t) atTop (𝓝 (Q₀ t)))
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val)
      (π.map (fun γ => (γ 0,γ 1))))
    {Bπ : ℝ≥0∞} (hBπ : Bπ≠∞) (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤Bπ • hausdorff n X)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (hQeq : ∀ t : Ioo (0:ℝ) 1, (Q₀ t : Measure X)=
      π.map (fun γ => γ (⟨t,t.property.1.le,t.property.2.le⟩ : Time)))
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0) (hA : ∀ᵐ x ∂hausdorff n X, |f x|≤A)
    (s : ℕ → ℝ) (hs : ∀ k, 0<s k) (hs0 : Tendsto s atTop (𝓝 0))
    (U : X → ℝ) (hu : f =ᵐ[hausdorff n X] U) {Cχ : ℝ}
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (12*R) Cχ)
    (GG : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (σ : ℕ → Measure X) [∀ k, IsFiniteMeasure (σ k)] :
    let m := hausdorff n X
    let q := hX.quadratic
    let w k := heatSobolev m q (s k) (hs k) f
    let ds k := heatSobolevMap m q (s k/2) (half_pos (hs k))
      (-heatGeneratorAt m q (s k-s k/2) f)
    (∀ k, SobolevSpace.toLp m q (GG k) =ᵐ[m] localGamma m q (w k) (w k)) →
    (∀ k (ψ : SobolevSpace m q) (z : X → ℝ),
      Continuous z → HasCompactSupport z → tsupport z ⊆ ball p (36*R) →
      SobolevSpace.toLp m q ψ =ᵐ[m] z →
      (∫ x, z x ∂σ k)=-(1/2:ℝ)*energyForm m q (GG k) ψ-
        weightedGamma m q (SobolevSpace.toLp m q ψ) (w k) (ds k)-
        K*weightedGamma m q z (w k) (w k)) →
    ∀ ell B : ℝ, 0≤B →
      Tendsto (fun k => (∫ x, χ.weight x ∂σ k)-
        2*(∫ x, χ.weight x*SobolevSpace.toLp m q (ds k) x ∂m)+
        (n:ℝ)*(∫ x, χ.weight x ∂m)) atTop (𝓝 ell) → ell≤B →
    let Z t := if ht : t∈Ioo (0:ℝ) 1 then ∫ x, U x ∂(Q₀ ⟨t,ht⟩ : Measure X) else 0
    let M a := (3*Real.sqrt (Real.exp |K| *
      (16*(hX.centeredActionBound hn p₀)*(R+32*(6*R))^2/(a/4)^2))*Real.exp |K|)^4
    let C a := (Bπ.toReal/4)*Real.sqrt (m.real (closedBall p (6*R)))*Real.sqrt (M a)
    ∀ a b, 0<a → a<b → b<1 → ∀ x∈Icc a b,
      |Z x-Z a-((Z b-Z a)/(b-a))*(x-a)-
        (∫ γ, dist (γ 0) (γ 1)^2 ∂π)*(x-a)*(x-b)/2|≤
        (C a*Real.sqrt B)*(b-a)^2 := by
  intro m q w ds hGG hσ ell B hB0 hlim hB Z M C a b ha hab hb
  obtain ⟨G,hF,hint,hG⟩ := D.small_radius_heat_second_variation_estimate p₀ a₀ b₀ hK hε1 hε0
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hS hT j hj Q₀ hweak
    π hgeo hopt hBπ hcomp hD hQeq f A hA s hs χ GG σ hGG hσ ell B hlim hB
  have hsmall := hG a b ha hab.le hb
  have hV : 0<(hausdorff n X).real (closedBall p (6*R)) := by
    apply ENNReal.toReal_pos
    · exact ne_of_gt ((hX.fullSupport p (6*R) (by positivity)).trans_le (measure_mono ball_subset_closedBall))
    · exact (hX.finiteOnBounded _ isBounded_closedBall).ne
  have hD0 := hX.centeredActionBound_pos hn p₀
  have hM : 0<M a := by
    dsimp only [M]
    positivity
  have hC : 0≤C a := by dsimp only [C]; positivity
  let H k := kernelHeat m q (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) (s k) f
  let F k t := if ht : t∈Ioo (0:ℝ) 1 then ∫ x, H k x ∂(Q₀ ⟨t,ht⟩ : Measure X) else 0
  have hQ (t : Ioo (0:ℝ) 1) : (Q₀ t : Measure X)≤Bπ • m := by
    rw [hQeq]
    exact hcomp _
  have hmeans := heat_means_uniform_limit m q (hX.canonicalHeatKernel_isContinuousHeatKernel hn p)
    (fun t => (Q₀ t : Measure X)) hBπ hQ f U hu s hs hs0
  have hval (t : ℝ) (ht : t∈Icc a b) : Tendsto (fun k => F k t) atTop (𝓝 (Z t)) := by
    have ht' : t∈Ioo (0:ℝ) 1 := ⟨ha.trans_le ht.1,ht.2.trans_lt hb⟩
    simpa only [F,Z,dite_eq_left ht'] using hmeans.tendsto_at ⟨t,ht'⟩
  have hsmall' (δ : ℝ) (hδ : 0<δ) : ∀ᶠ k in atTop, ∀ t∈Icc a b,
      |G k t-(∫ γ, dist (γ 0) (γ 1)^2 ∂π)|≤C a*Real.sqrt B+δ := by
    have hh := eventual_balanced_error_add
      (fun k (t : Icc a b) => G k t-(∫ γ, dist (γ 0) (γ 1)^2 ∂π))
      (C := Bπ.toReal/4) (V := m.real (closedBall p (6*R))) (M := M a) hV hM hB0
      (fun η hη => by
        filter_upwards [hsmall η hη] with k hk t c hc
        exact hk t t.property c hc) hδ
    filter_upwards [hh] with k hk t ht
    exact hk ⟨t,ht⟩
  intro x hx
  have hbound := quadratic_limit_chord_error F G Z hab
    (mul_nonneg hC (Real.sqrt_nonneg B)) hx
    (fun k t ht => hF k t ⟨ha.trans_le ht.1,ht.2.trans_lt hb⟩)
    (fun k u v hau huv hvb => hint k u v (ha.trans_le hau) huv (hvb.trans_lt hb))
    hsmall' hval
  exact hbound

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
