import OAI.Geometry.RCD.Sobolev.DistancePoissonRepresentative
import OAI.Geometry.RCD.Sobolev.SmallRadiusPoissonMean

namespace OAI

/-! # Quantitative transport means of the constructed distance replacements -/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X} {hn : 2≤n} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {κ B J C : ℝ} {p : ℕ → X} {r : ℕ → ℝ} {hr : ∀ k, 0<r k}
  {F : DistancePoissonFamily (hausdorff n X) hX.quadratic n κ B J C p r hr}
  (W : DistancePoissonMeanData F) (k : ℕ)
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ j, 0<ε j}
  (D : hX.CompactHeatScalingData hn (p k) μ ν ε hε)
attribute [local instance] pathBorel pathBorelSpace

theorem DistancePoissonMeanData.mean_estimate (p₀ : X) (a₀ : S) (b₀ : T)
    (hK : K≤0) (hκ : 0≤κ) (hBJ : 0≤J+B/2)
    (hε1 : ∀ j, ε j≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0≤ρ₀ x) (hp₁ : ∀ x, 0≤ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x|≤C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x|≤C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (hS : ∀ y:S, dist (p k) y≤r k/512) (hT : ∀ y:T, dist (p k) y≤r k/512)
    (j : ℕ → ℕ) (hj : StrictMono j) (Q₀ : Ioo (0:ℝ) 1 → ProbabilityMeasure X)
    (hweak : ∀ t, Tendsto (fun i => D.interpolationLaw (D.index (j i)) t) atTop (𝓝 (Q₀ t)))
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val)
      (π.map (fun γ => (γ 0,γ 1))))
    {Bπ : ℝ≥0∞} (hBπ : Bπ≠∞) (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤Bπ • hausdorff n X)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (hQeq : ∀ t : Ioo (0:ℝ) 1, (Q₀ t : Measure X)=
      π.map (fun γ => γ (⟨t,t.property.1.le,t.property.2.le⟩ : Time))) :
    let Z t := if ht : t∈Ioo (0:ℝ) 1 then ∫ x, W.representative k x ∂(Q₀ ⟨t,ht⟩ : Measure X) else 0
    ∀ l h, 0<l → l<h → h<1 → ∀ t∈Icc l h,
      |Z t-Z l-((Z h-Z l)/(h-l))*(t-l)-
        (∫ γ, dist (γ 0) (γ 1)^2 ∂π)*(t-l)*(t-h)/2|≤
      (poissonMeanConstant K (hX.centeredActionBound hn p₀) l*(h-l)^2)*
        (r k)^2*Bπ.toReal*Real.sqrt ((hausdorff n X).real (ball (p k) (r k)))*
          Real.sqrt (W.budget K k) := by
  intro Z l h hl hlh hh t ht
  have hk := hr k
  obtain ⟨L,A,hU,hUc,hu,hA⟩ := W.representative_spec k
  obtain ⟨hsource,heik,herror⟩ := F.extension_local_data k (W.extension k).val (W.replacement_eq k)
  have hE : 0≤(J+B/2)*(r k)^2*(F.source k).real (ball (p k) (r k)) := by positivity
  have hna : (n:ℝ)≤(n:ℝ)+κ*(4*r k)^2 := le_add_of_nonneg_right (by positivity)
  have hmean := D.small_radius_poisson_mean_estimate p₀ a₀ b₀ hK hε1 hε0
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν
    (by positivity : 0<r k/512) hS hT j hj Q₀ hweak π hgeo hopt hBπ hcomp hD hQeq
    (W.extension k).val (F.datum k) (W.laplacian k) (W.weak_laplacian k)
    (W.representative k) L A hU hUc hu hA
    (by linarith : 24*(r k/512)<r k/16) (zero_le_one.trans W.cutoff_one_le) hE hna
    (W.cutoff k) (W.source_eq k) (F.source k) hsource heik herror
  have he := hmean l h hl hlh hh t ht
  change _ ≤ _*Real.sqrt (W.budget K k)*(h-l)^2 at he
  have hV : (hausdorff n X).real (closedBall (p k) (6*(r k/512)))≤
      (hausdorff n X).real (ball (p k) (r k)) :=
    measureReal_mono (closedBall_subset_ball (by linarith)) measure_ball_lt_top.ne
  apply he.trans
  calc
    _ ≤ (Bπ.toReal/4)*Real.sqrt ((hausdorff n X).real (ball (p k) (r k)))*
        Real.sqrt ((3*Real.sqrt (Real.exp |K| *
          (16*(hX.centeredActionBound hn p₀)*((r k/512)+32*(6*(r k/512)))^2/(l/4)^2))*Real.exp |K|)^4)*
          Real.sqrt (W.budget K k)*(h-l)^2 := by
      dsimp only
      gcongr
    _ = _ := by
      have hcoef := centered_mean_coefficient (K := K) (a := l)
        (hX.centeredActionBound_pos hn p₀).le hk
      linear_combination Bπ.toReal*Real.sqrt ((hausdorff n X).real (ball (p k) (r k)))*
        Real.sqrt (W.budget K k)*(h-l)^2*hcoef

end RegularPointCoordinates

end

end OAI
