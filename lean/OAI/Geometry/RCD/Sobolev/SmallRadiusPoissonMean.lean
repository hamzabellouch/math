import OAI.Geometry.RCD.Heat.SmallRadiusOriginalMean
import OAI.Geometry.RCD.Heat.PoissonHeatShiftedMass
import OAI.Geometry.RCD.Sobolev.SobolevWeakEnergyLower

namespace OAI

/-! # Poisson source control of transport means at every physical radius

The full shifted mass is constructed from the actual positive source. The
balanced estimate uses the radius-dependent centered action bound.
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

theorem small_radius_poisson_mean_estimate (p₀ : X) (a₀ : S) (b₀ : T) (hK : K≤0)
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
    (u q : SobolevSpace (hausdorff n X) hX.quadratic)
    (d : Lp ℝ 2 (hausdorff n X))
    (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d)
    (U : X → ℝ) (L A : ℝ≥0) (hU : LipschitzWith L U) (hUc : HasCompactSupport U)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] U)
    (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic u x|≤A)
    {b a Cχ E : ℝ} (hb : 24*R<b) (hCχ : 0≤Cχ) (hE : 0≤E) (hna : (n:ℝ)≤a)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (12*R) Cχ)
    (hda : d =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => a)
    (ρ : Measure X)
    (hsource : ∀ (ψ : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ) (M : ℝ≥0),
      LipschitzWith M v → HasCompactSupport v → tsupport v ⊆ ball p b →
      SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ =ᵐ[hausdorff n X] v →
      energyForm (hausdorff n X) hX.quadratic q ψ+
        a*(∫ x in ball p b, v x ∂hausdorff n X)=∫ x, v x ∂ρ)
    (heik : (fun x => (1/2:ℝ)*localGamma (hausdorff n X) hX.quadratic q q x)
      =ᵐ[(hausdorff n X).restrict (ball p b)] SobolevSpace.toLp (hausdorff n X) hX.quadratic q)
    (herror : (∫ x in ball p b,
      |(1/2:ℝ)*localGamma (hausdorff n X) hX.quadratic u u x-
        (1/2:ℝ)*localGamma (hausdorff n X) hX.quadratic q q x| ∂hausdorff n X)≤E) :
    let B := (Cχ/(12*R)^2)*E-K*weightedGamma (hausdorff n X) hX.quadratic χ.weight u u
    let Z t := if ht : t∈Ioo (0:ℝ) 1 then ∫ x, U x ∂(Q₀ ⟨t,ht⟩ : Measure X) else 0
    let M l := (3*Real.sqrt (Real.exp |K| *
      (16*(hX.centeredActionBound hn p₀)*(R+32*(6*R))^2/(l/4)^2))*Real.exp |K|)^4
    let C l := (Bπ.toReal/4)*Real.sqrt ((hausdorff n X).real (closedBall p (6*R)))*Real.sqrt (M l)
    ∀ l h, 0<l → l<h → h<1 → ∀ t∈Icc l h,
      |Z t-Z l-((Z h-Z l)/(h-l))*(t-l)-
        (∫ γ, dist (γ 0) (γ 1)^2 ∂π)*(t-l)*(t-h)/2|≤
        (C l*Real.sqrt B)*(h-l)^2 := by
  intro B Z M C
  have h6R : 0<6*R := by linarith
  have hmass := hX.poisson_heat_shifted_mass hn hK p u q d hd U L A hU hUc hu hA
    (R := 6*R) (E := E) h6R hCχ (by linarith : 4*(6*R)<b) hna
  rw [show 2*(6*R)=12*R by ring] at hmass
  obtain ⟨G,σ,ell,hσ,hG,hrep,hlim,hell⟩ := hmass χ hda ρ hsource heik herror
    heatStep heatStep_pos (fun k => by
      unfold heatStep
      exact pow_le_one₀ (by norm_num) (by norm_num)) heatStep_tendsto
  let (k : ℕ) : IsFiniteMeasure (σ k) := hσ k
  have hw : 0≤weightedGamma (hausdorff n X) hX.quadratic χ.weight u u :=
    weightedGamma_nonneg_of_weight _ _ (Eventually.of_forall fun x => (χ.bounds x).1) u
  have hB : 0≤B := by
    dsimp only [B]
    exact sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg hK hw).trans
      (mul_nonneg (div_nonneg hCχ (sq_nonneg _)) hE))
  have hrep' : ∀ k (ψ : SobolevSpace (hausdorff n X) hX.quadratic) (z : X → ℝ),
      Continuous z → HasCompactSupport z → tsupport z ⊆ ball p (36*R) →
      SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ =ᵐ[hausdorff n X] z →
      (∫ x, z x ∂σ k)=-(1/2:ℝ)*energyForm (hausdorff n X) hX.quadratic (G k) ψ-
        weightedGamma (hausdorff n X) hX.quadratic (SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ)
          (heatSobolev (hausdorff n X) hX.quadratic (heatStep k) (heatStep_pos k)
            (SobolevSpace.toLp (hausdorff n X) hX.quadratic u))
          (heatSobolevMap (hausdorff n X) hX.quadratic (heatStep k/2) (half_pos (heatStep_pos k))
            (-heatGeneratorAt (hausdorff n X) hX.quadratic (heatStep k-heatStep k/2)
              (SobolevSpace.toLp (hausdorff n X) hX.quadratic u)))-
        K*weightedGamma (hausdorff n X) hX.quadratic z
          (heatSobolev (hausdorff n X) hX.quadratic (heatStep k) (heatStep_pos k)
            (SobolevSpace.toLp (hausdorff n X) hX.quadratic u))
          (heatSobolev (hausdorff n X) hX.quadratic (heatStep k) (heatStep_pos k)
            (SobolevSpace.toLp (hausdorff n X) hX.quadratic u)) := by
    simpa only [show 6*(6*R)=36*R by ring] using hrep
  exact D.small_radius_original_mean_estimate p₀ a₀ b₀ hK hε1 hε0 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁
    hC₀ hC₁ hμ hν hR hS hT j hj Q₀ hweak π hgeo hopt hBπ hcomp hD hQeq
    (SobolevSpace.toLp (hausdorff n X) hX.quadratic u) A hA heatStep heatStep_pos
    heatStep_tendsto U hu χ G σ hG hrep' ell B hB hlim hell

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
