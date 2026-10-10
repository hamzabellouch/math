import OAI.Geometry.RCD.Sobolev.DistancePoissonMeanEstimate
import OAI.Geometry.RCD.Heat.CompactHeatActualPlanLimit
import OAI.Geometry.RCD.Transport.CompressedFiniteUnique

namespace OAI

/-! # The actual Poisson mean estimate on every compressed optimal plan -/

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
attribute [local instance] pathBorel pathBorelSpace

theorem DistancePoissonMeanData.optimal_mean_estimate (p₀ : X) (a₀ : S) (b₀ : T)
    (hK : K≤0) (hκ : 0≤κ) (hBJ : 0≤J+B/2) (hr1 : r k≤1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0≤ρ₀ x) (hp₁ : ∀ x, 0≤ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x|≤C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x|≤C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (hS : ∀ y:S, dist (p k) y≤r k/512) (hT : ∀ y:T, dist (p k) y≤r k/512)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val)
      (π.map (fun γ => (γ 0,γ 1))))
    {Bπ : ℝ≥0∞} (hBπ : Bπ≠∞) (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤Bπ • hausdorff n X) :
    let Z t := ∫ γ, W.representative k (γ t) ∂π
    ∀ (l h t : Time), 0<(l:ℝ) → (l:ℝ)<h → (h:ℝ)<1 → (t:ℝ)∈Icc (l:ℝ) h →
      |Z t-Z l-((Z h-Z l)/((h:ℝ)-l))*((t:ℝ)-l)-
        (∫ γ, dist (γ 0) (γ 1)^2 ∂π)*((t:ℝ)-l)*((t:ℝ)-h)/2|≤
      (poissonMeanConstant K (hX.centeredActionBound hn p₀) l*((h:ℝ)-l)^2)*
        (r k)^2*Bπ.toReal*Real.sqrt ((hausdorff n X).real (ball (p k) (r k)))*
          Real.sqrt (W.budget K k) := by
  intro Z l h t hl hlh hh ht
  have he1 (j : ℕ) : heatStep j≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hR : 0≤r k/512 := (div_pos (hr k) (by norm_num)).le
  obtain ⟨D⟩ := hX.exists_compact_heat_scaling_data hn (p k) hK a₀ b₀ μ ν
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν heatStep heatStep_pos he1 heatStep_tendsto
    hR hS hT
  have hS1 (y : S) : dist (p k) y≤1 := (hS y).trans (by linarith)
  have hT1 (y : T) : dist (p k) y≤1 := (hT y).trans (by linarith)
  obtain ⟨π',j,B',A',hj,hB',hg',hp',hlen,hc',_hf,_hb,hlim,_hcal⟩ :=
    D.exists_actual_heat_limit_plan a₀ b₀ hK he1 heatStep_tendsto ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁
      hC₀ hC₁ hμ hν (le_refl (1:ℝ)) hS1 hT1
  have hs₀ : ∀ᵐ x ∂μ.map Subtype.val, dist x (p k)≤1 := by
    apply (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_le (by fun_prop) measurable_const)).mpr
    exact Eventually.of_forall fun y => by simpa only [dist_comm] using hS1 y
  have hs₁ : ∀ᵐ x ∂ν.map Subtype.val, dist x (p k)≤1 := by
    apply (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_le (by fun_prop) measurable_const)).mpr
    exact Eventually.of_forall fun y => by simpa only [dist_comm] using hT1 y
  have heq := hX.compressed_plan_unique_finite hn (p k) (by norm_num : (0:ℝ)≤1)
    π (π' : Measure C(Time,X)) hgeo hg' hopt hp' hBπ hB' hcomp hc' hs₀ hs₁
  have hlen' : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) π := heq.symm ▸ hlen
  have hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π :=
    (memLp_two_iff_integrable_sq (((measurable_path_eval 0).dist
      (measurable_path_eval 1)).aestronglyMeasurable)).mpr hlen'
  let Q₀ (s : Ioo (0:ℝ) 1) := π'.map (fun γ => γ (⟨s,s.property.1.le,s.property.2.le⟩ : Time))
  have hQeq (s : Ioo (0:ℝ) 1) : (Q₀ s : Measure X)=
      π.map (fun γ => γ (⟨s,s.property.1.le,s.property.2.le⟩ : Time)) := by
    change (π' : Measure C(Time,X)).map _=π.map _
    rw [heq]
  have hmean := W.mean_estimate k D p₀ a₀ b₀ hK hκ hBJ he1 heatStep_tendsto
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hS hT j hj Q₀ (fun s => (hlim s).1)
    π hgeo hopt hBπ hcomp hD hQeq
  obtain ⟨LV,AV,hV,_hc,_he,_hA⟩ := W.representative_spec k
  have hs (s : Time) (hs0 : 0<(s:ℝ)) (hs1 : (s:ℝ)<1) :
      (if hs : (s:ℝ)∈Ioo (0:ℝ) 1 then ∫ x, W.representative k x ∂(Q₀ ⟨s,hs⟩ : Measure X) else 0)=Z s := by
    rw [dite_eq_left ⟨hs0,hs1⟩,hQeq]
    exact integral_map (measurable_path_eval s).aemeasurable hV.continuous.aestronglyMeasurable
  have hlast := hmean l h hl hlh hh t ht
  dsimp only at hlast
  rw [hs t (lt_of_lt_of_le hl ht.1) (lt_of_le_of_lt ht.2 hh),hs l hl (hlh.trans hh),
    hs h (hl.trans hlh) hh] at hlast
  exact hlast

end RegularPointCoordinates

end

end OAI
