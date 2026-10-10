import OAI.Geometry.RCD.Heat.CompactHeatIntrinsicSecondVariation
import OAI.Geometry.RCD.Sobolev.CanonicalHessianConstantShift
import OAI.Geometry.RCD.Heat.CompactHeatLocalizedSecondVariation
import OAI.Geometry.RCD.Heat.CenteredHeatPlanEnergy
import OAI.Geometry.RCD.Heat.HeatActionBasepoint
import OAI.Geometry.RCD.Heat.UniformHeatActionRealization
import OAI.Geometry.RCD.Heat.HeatPlanQuadraticEnergy
import OAI.Geometry.RCD.Heat.HeatShiftedHessianBound
import OAI.Geometry.RCD.Harmonic.UniformLocalDifferencePairing

namespace OAI

/-! # Quantitative second variation at an arbitrary positive physical radius

Centered heat-action directions have slope proportional to the physical
radius, uniformly over all centers. The full shifted mass controls their
Hessian error without enlarging the source ball to unit scale.
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

theorem small_radius_heat_second_variation_estimate (p₀ : X) (a₀ : S) (b₀ : T) (hK : K≤0)
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
    (s : ℕ → ℝ) (hs : ∀ k, 0<s k) {Cχ : ℝ}
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
    ∀ ell B : ℝ,
      Tendsto (fun k => (∫ x, χ.weight x ∂σ k)-
        2*(∫ x, χ.weight x*SobolevSpace.toLp m q (ds k) x ∂m)+
        (n:ℝ)*(∫ x, χ.weight x ∂m)) atTop (𝓝 ell) → ell≤B →
    let H k := kernelHeat m q (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) (s k) f
    let F k t := if ht : t∈Ioo (0:ℝ) 1 then ∫ x, H k x ∂(Q₀ ⟨t,ht⟩ : Measure X) else 0
    let M a := (3*Real.sqrt (Real.exp |K| *
      (16*(hX.centeredActionBound hn p₀)*(R+32*(6*R))^2/(a/4)^2))*Real.exp |K|)^4
    ∃ G : ℕ → ℝ → ℝ,
      (∀ k t, t∈Ioo (0:ℝ) 1 → DifferentiableAt ℝ (F k) t) ∧
      (∀ k a b, 0<a → a≤b → b<1 → IntervalIntegrable (G k) volume a b ∧
        (∫ t in a..b, G k t)=deriv (F k) b-deriv (F k) a) ∧
      ∀ a b, 0<a → a≤b → b<1 →
        ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ t∈Icc a b, ∀ c : ℝ, 0<c →
          4*c*|G k t-(∫ γ, dist (γ 0) (γ 1)^2 ∂π)| ≤
            (Bπ.toReal/4)*(4*c^2*m.real (closedBall p (6*R))+(M a)*(B+δ)) := by
  intro m q w ds hGG hσ ell B hlim hB H F M
  let Rbig := max 1 (2*R)
  have hRb : 1≤Rbig := le_max_left _ _
  have hRsmall : R≤Rbig := by dsimp only [Rbig]; linarith [le_max_right (1:ℝ) (2*R)]
  have hsS (y:S) : dist p y≤Rbig := (hS y).trans hRsmall
  have hsT (y:T) : dist p y≤Rbig := (hT y).trans hRsmall
  have hends := optimalPlan_endpoints (μ.map Subtype.val) (ν.map Subtype.val) π hopt
  have hSm : MeasurableSet S := (isCompact_iff_compactSpace.mpr inferInstance).isClosed.measurableSet
  have hTm : MeasurableSet T := (isCompact_iff_compactSpace.mpr inferInstance).isClosed.measurableSet
  have h0 : ∀ᵐ γ ∂π, dist p (γ 0)≤R := by
    apply ae_of_ae_map (μ := π) (p := fun x : X => dist p x≤R) (measurable_path_eval 0).aemeasurable
    rw [hends.1]
    exact (MeasurableEmbedding.subtype_coe hSm).ae_map_iff.mpr (Eventually.of_forall hS)
  have h1 : ∀ᵐ γ ∂π, dist p (γ 1)≤R := by
    apply ae_of_ae_map (μ := π) (p := fun x : X => dist p x≤R) (measurable_path_eval 1).aemeasurable
    rw [hends.2]
    exact (MeasurableEmbedding.subtype_coe hTm).ae_map_iff.mpr (Eventually.of_forall hT)
  have hstay (t : Ioo (0:ℝ) 1) : ∀ᵐ x ∂(Q₀ t : Measure X), x∈closedBall p ((6*R)/2) := by
    rw [hQeq]
    simpa only [show 6*R/2=3*R by ring] using
      geodesic_plan_eval_ball π hgeo p h0 h1 (⟨t,t.property.1.le,t.property.2.le⟩ : Time)
  choose G hdiff _hLip hident hint using fun k => D.localized_limit_mean_second_variation
    a₀ b₀ hK hε1 hε0 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hRb hsS hsT j hj Q₀ hweak
    (by positivity : 0<6*R) (by dsimp only [Rbig]; linarith [le_max_right (1:ℝ) (2*R)] : 6*R≤3*Rbig)
    hstay f A hA (hs k)
  refine ⟨G,hdiff,hint,?_⟩
  intro a b ha _hab hb
  have h6R : 0<6*R := by linarith
  have h3R : 0<3*R := by linarith
  let Y := Icc a b
  have htime (t : Y) : (t:ℝ)/2∈Ioo (a/4) 1 := by
    constructor <;> linarith [t.property.1,t.property.2]
  have ht01 (t : Y) : (t:ℝ)∈Ioo (0:ℝ) 1 := by
    constructor <;> linarith [t.property.1,t.property.2]
  let L : ℝ≥0 := ⟨Real.sqrt (Real.exp |K| *
    (16*(hX.centeredActionBound hn p₀)*(R+32*(6*R))^2/(a/4)^2)),Real.sqrt_nonneg _⟩
  let Lv : ℝ≥0 := 3*L
  have hLv : (Lv:ℝ)=3*(L:ℝ) := by simp only [Lv,NNReal.coe_mul,NNReal.coe_ofNat]
  have hLreal : (L:ℝ)=Real.sqrt (Real.exp |K| *
      (16*(hX.centeredActionBound hn p₀)*(R+32*(6*R))^2/(a/4)^2)) := rfl
  let Av : ℝ≥0 := ⟨2*(6*R)*(L:ℝ),by positivity⟩
  have hreal := (Classical.choose_spec (hX.uniform_centered_heat_action_realization hn p₀)).2
    p μ ρ₀ hm₀ hp₀ hC₀ hμ D.left D.left_pos ε hε hε1 hε0 p D.index D.forward.potential
    D.strict.tendsto_atTop D.forward_limit hR.le hS h6R (by positivity : 0<a/4)
  choose v V hV hVc hvr hAv0 hvloc using fun t : Y => hreal ((t:ℝ)/2) (htime t)
  have hAv (t : Y) : ∀ᵐ x ∂m, |SobolevSpace.toLp m q (v t) x|≤Av := by
    filter_upwards [hvr t] with x hx
    rw [hx]
    exact hAv0 t x
  let φ := radialCutoff p (3*R)
  have hφ : AEStronglyMeasurable φ m := (radialCutoff_lipschitz p h3R).continuous.aestronglyMeasurable
  have hφb : ∀ᵐ x ∂m, |φ x|≤(1:ℝ≥0) := Eventually.of_forall fun x => by
    rw [abs_of_nonneg (radialCutoff_bounds p (3*R) x).1]
    exact (radialCutoff_bounds p (3*R) x).2
  have hφz (x : X) (hx : x∉closedBall p (6*R)) : φ x=0 := by
    apply radialCutoff_eq_zero p h3R
    have hh : 6*R<dist p x := by simpa only [mem_closedBall,dist_comm,not_le] using hx
    linarith
  choose J hJ using fun k (t : Y) => (hX.exists_canonical_heat_hessian hn p hK f A hA (hs k) h6R
    (v t) (V t) Lv Av (hV t) (hVc t) (hvr t) (hAv t) φ hφ 1 hφb hφz).imp
      (fun _ h => h.1)
  intro δ hδ
  have hbound := hX.heat_shifted_hessian_eventual_bound (Y := Y) (C := Cχ) hn hK p f A hA s hs h6R
  rw [show 2*(6*R)=12*R by ring] at hbound
  specialize hbound χ GG σ v V Lv (fun _ => Av) hV hVc hvr hAv φ hφ 1 hφb J hGG
  have hsource : ∀ k (ψ : SobolevSpace m q) (z : X → ℝ),
      Continuous z → HasCompactSupport z → tsupport z ⊆ ball p (6*(6*R)) →
      SobolevSpace.toLp m q ψ =ᵐ[m] z →
      (∫ x, z x ∂σ k)=-(1/2:ℝ)*energyForm m q (GG k) ψ-
        weightedGamma m q (SobolevSpace.toLp m q ψ) (w k) (ds k)-
        K*weightedGamma m q z (w k) (w k) := by
    simpa only [show 6*(6*R)=36*R by ring] using hσ
  specialize hbound hsource hJ ell B hlim hB δ hδ
  filter_upwards [hbound] with k hk t ht c hc
  let y : Y := ⟨t,ht⟩
  have hQ : (Q₀ ⟨t,ht01 y⟩ : Measure X)≤Bπ • m := by rw [hQeq]; exact hcomp _
  have hgi : Integrable (fun x => φ x*localGamma m q (v y) (v y) x)
      (m.restrict (closedBall p (6*R))) :=
    ((localGamma_memL1 m q (v y) (v y)).bdd_mul hφ
      (by simpa only [Real.norm_eq_abs] using hφb)).integrableOn
  obtain ⟨v₀,V₀,L₀,A₀,I,hV₀,hVc₀,hv₀,hA₀,hvloc₀,hcan₀,hGi⟩ := hident k ⟨t,ht01 y⟩
  have hcan₀' : IsCanonicalHeatHessian m q (w k) v₀ p (6*R) φ I := by
    simpa only [show 6*R/2=3*R by ring] using hcan₀
  have hdiffval : (fun x => SobolevSpace.toLp m q (v y) x-SobolevSpace.toLp m q v₀ x)
      =ᵐ[m.restrict (closedBall p (6*R))] fun _ => -D.forward.potential (t/2) p := by
    filter_upwards [hvloc y,hvloc₀] with x hx hz
    rw [hx,hz]
    ring
  have hdiffLp : SobolevSpace.toLp m q (v y-v₀)
      =ᵐ[m.restrict (closedBall p (6*R))] fun _ => -D.forward.potential (t/2) p := by
    filter_upwards [hdiffval,ae_restrict_of_ae (Lp.coeFn_sub
      (SobolevSpace.toLp m q (v y)) (SobolevSpace.toLp m q v₀))] with x hx he
    exact he.trans hx
  have henergy : (∫ x in closedBall p (6*R), φ x*localGamma m q (v y) (v y) x
      ∂(Q₀ ⟨t,ht01 y⟩ : Measure X))=4*∫ γ, dist (γ 0) (γ 1)^2 ∂π := by
    rw [hQeq]
    exact D.centered_heat_plan_quadratic_energy a₀ b₀ hK hε1 hε0 hR hS hT
      π hgeo hopt hBπ hcomp hD _ (ht01 y).1 (ht01 y).2 v₀ (v y) hvloc₀ _ hdiffLp
  have hGk : G k t=(1/4:ℝ)*(∫ x in closedBall p (6*R), J k y x ∂(Q₀ ⟨t,ht01 y⟩ : Measure X)) := by
    have heq := hX.canonical_hessian_locality_of_constant hn p hK f A hA (hs k) h6R
      v₀ (v y) V₀ (V y) L₀ Lv A₀ Av hV₀ (hV y) hVc₀ (hVc y) hv₀ (hvr y) hA₀ (hAv y)
      (-D.forward.potential (t/2) p) hdiffval φ hφ 1 hφb hφz I (J k y) hcan₀' (hJ k y)
    rwa [heq] at hGi
  have hdom : (Q₀ ⟨t,ht01 y⟩ : Measure X).restrict (closedBall p (6*R))≤
      Bπ • m.restrict (closedBall p (6*R)) := by
    simpa only [Measure.restrict_smul] using Measure.restrict_mono (subset_refl _) hQ
  have hcompare := integral_difference_le_of_domination _ _ hBπ hdom
    (memLp_one_iff_integrable.mp (Lp.memLp (J k y))) hgi
  have herr : |G k t-(∫ γ, dist (γ 0) (γ 1)^2 ∂π)|≤
      (Bπ.toReal/4)*(∫ x in closedBall p (6*R),
        |J k y x-φ x*localGamma m q (v y) (v y) x| ∂m) := by
    rw [hGk]
    have hid : (1/4:ℝ)*(∫ x in closedBall p (6*R), J k y x ∂(Q₀ ⟨t,ht01 y⟩ : Measure X))-
        (∫ γ, dist (γ 0) (γ 1)^2 ∂π)=
        (1/4:ℝ)*((∫ x in closedBall p (6*R), J k y x ∂(Q₀ ⟨t,ht01 y⟩ : Measure X))-
          (∫ x in closedBall p (6*R), φ x*localGamma m q (v y) (v y) x ∂(Q₀ ⟨t,ht01 y⟩ : Measure X))) := by
      rw [henergy]
      ring
    rw [hid,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/4)]
    exact (mul_le_mul_of_nonneg_left hcompare (by norm_num : (0:ℝ)≤1/4)).trans_eq (by ring)
  have hh := mul_le_mul_of_nonneg_left herr (show 0≤4*c by positivity)
  have hbnd := mul_le_mul_of_nonneg_left (hk y c hc)
    (div_nonneg (ENNReal.toReal_nonneg (a := Bπ)) (by norm_num : (0:ℝ)≤4))
  apply hh.trans
  convert hbnd using 1
  · dsimp only [m,q]
    ring
  · simp only [hLv,hLreal,NNReal.coe_one]
    dsimp only [m,M]
    ring

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
