import OAI.Geometry.RCD.Heat.CompactHeatJointConcentration
import OAI.Geometry.RCD.Heat.CompactHeatJointSlack
import OAI.Geometry.RCD.Heat.CompactHeatDualSaturation

namespace OAI

/-! # Every actual joint bridge limit is concentrated on geodesic triples -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem joint_limit_endpoint_marginals (t : Ioo (0:ℝ) 1) (i : ℕ → ℕ)
    (Q : ProbabilityMeasure (X × (S × T)))
    (hweak : Tendsto (fun k => D.jointLaw (D.index (i k)) t) atTop (𝓝 Q)) :
    (Q.map Prod.snd : Measure (S × T)).map Prod.fst=μ ∧
      (Q.map Prod.snd : Measure (S × T)).map Prod.snd=ν := by
  have hp := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ Q hweak continuous_snd
  have he k : (D.jointLaw (D.index (i k)) t).map Prod.snd=D.coupling (i k) :=
    ProbabilityMeasure.toMeasure_injective (D.jointMeasure_snd _ _)
  simp only [he] at hp
  have hl := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hp continuous_fst
  have hr := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hp continuous_snd
  have heL k : (D.coupling (i k)).map Prod.fst=μ.toProbabilityMeasure :=
    Subtype.ext (continuousDensityCoupling_fst μ ν (D.density (i k))
      (fun z => (D.density_pos _ z).le) (D.density_row _))
  have heR k : (D.coupling (i k)).map Prod.snd=ν.toProbabilityMeasure :=
    Subtype.ext (continuousDensityCoupling_snd μ ν (D.density (i k))
      (fun z => (D.density_pos _ z).le) (D.density_col _))
  simp only [heL] at hl
  simp only [heR] at hr
  have hL := congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique hl tendsto_const_nhds)
  have hR := congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique hr tendsto_const_nhds)
  exact ⟨hL,hR⟩

theorem joint_limit_geodesic (a₀ : S) (b₀ : T) (hK : K ≤ 0)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0))
    {R : ℝ} (hR : 0 ≤ R) (hS : ∀ a:S, dist p a ≤ R) (hT : ∀ b:T, dist p b ≤ R)
    (t : Ioo (0:ℝ) 1) (i : ℕ → ℕ) (hi : StrictMono i)
    (Q : ProbabilityMeasure (X × (S × T)))
    (hweak : Tendsto (fun k => D.jointLaw (D.index (i k)) t) atTop (𝓝 Q)) :
    ∃ c : ℝ, (∀ a b, b ∈ ν.support → D.slack a₀ b₀ c (a,b) ≤ 0) ∧
      ∀ᵐ z ∂(Q : Measure (X × (S × T))),
      dist z.1 (z.2.1:X)=(t:ℝ)*dist (z.2.1:X) (z.2.2:X) ∧
        dist z.1 (z.2.2:X)=(1-(t:ℝ))*dist (z.2.1:X) (z.2.2:X) ∧
        D.slack a₀ b₀ c z.2=0 := by
  obtain ⟨c,hc,hdual,_⟩ := D.dual_limit a₀ b₀ hK hε1 hε0 hR hS hT
  have hnonneg := D.joint_limit_nonnegative_slack a₀ b₀ c hK hε1 hε0 hR hS hT hc t i hi Q hweak
  obtain ⟨_,hr⟩ := D.joint_limit_endpoint_marginals t i Q hweak
  have hbsupp := coupling_snd_support (ν := ν) (π := (Q.map Prod.snd : Measure (S × T))) hr
  have hbsupp' : ∀ᵐ z ∂(Q : Measure (X × (S × T))), z.2.2 ∈ ν.support :=
    ae_of_ae_map measurable_snd.aemeasurable hbsupp
  refine ⟨c,hdual,?_⟩
  filter_upwards [hnonneg,hbsupp'] with z hz hb
  have hd := hdual z.2.1 z.2.2 hb
  exact D.jointSlack_zero_geodesic a₀ b₀ c t z.1 z.2.1 z.2.2 hd
    (le_antisymm (D.jointSlack_nonpos a₀ b₀ c t z.1 z.2.1 z.2.2 hd) hz)

theorem joint_limit_bounded (a₀ : S) (b₀ : T) (hK : K ≤ 0)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0))
    {R : ℝ} (hR : 0 ≤ R) (hS : ∀ a:S, dist p a ≤ R) (hT : ∀ b:T, dist p b ≤ R)
    (t : Ioo (0:ℝ) 1) (i : ℕ → ℕ) (hi : StrictMono i)
    (Q : ProbabilityMeasure (X × (S × T)))
    (hweak : Tendsto (fun k => D.jointLaw (D.index (i k)) t) atTop (𝓝 Q)) :
    ∀ᵐ x ∂(Q.map Prod.fst : Measure X), dist x p ≤ 3*R := by
  obtain ⟨_,_,hgeo⟩ := D.joint_limit_geodesic a₀ b₀ hK hε1 hε0 hR hS hT t i hi Q hweak
  apply (ae_map_iff measurable_fst.aemeasurable
    (measurableSet_le (by fun_prop) measurable_const)).mpr
  filter_upwards [hgeo] with z hz
  have ha : dist (z.2.1:X) p ≤ R := by simpa only [dist_comm] using hS z.2.1
  have hb : dist (z.2.2:X) p ≤ R := by simpa only [dist_comm] using hT z.2.2
  have hab : dist (z.2.1:X) (z.2.2:X) ≤ 2*R := by
    have hh := dist_triangle (z.2.1:X) p (z.2.2:X)
    rw [dist_comm p (z.2.2:X)] at hh
    linarith only [hh,ha,hb]
  have htx := mul_le_of_le_one_left (dist_nonneg (x := (z.2.1:X)) (y := (z.2.2:X))) t.property.2.le
  have hx := dist_triangle z.1 (z.2.1:X) p
  rw [hz.1] at hx
  linarith only [hx,htx,ha,hab]

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
