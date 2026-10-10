import OAI.Geometry.RCD.Heat.CompactHeatJointLogLimit
import OAI.Geometry.RCD.Metric.NegativeLogDensityMass

namespace OAI

/-! # Joint bridge limits carry no negative logarithmic slack

The reference measure may have infinite total mass. The argument only uses
finite mass on compact intermediate balls, then countable exhaustion.
-/

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

theorem joint_negative_mass (a₀ : S) (b₀ : T) (c : ℝ) (hK : K ≤ 0)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0))
    {R : ℝ} (hR : 0 ≤ R) (hS : ∀ a:S, dist p a ≤ R) (hT : ∀ b:T, dist p b ≤ R)
    (hc : Tendsto (fun k => ε (D.index k)*(Real.log (D.left (D.index k) a₀)+
      Real.log (D.right (D.index k) b₀))) atTop (𝓝 c))
    (t : Ioo (0:ℝ) 1) (r : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k => (D.jointMeasure (D.index k) t)
      {z | dist z.1 p < r ∧ D.jointSlack a₀ b₀ c t z < -δ}) atTop (𝓝 0) := by
  let U : Set (X × (S × T)) := {z | dist z.1 p < r ∧ D.jointSlack a₀ b₀ c t z < -δ}
  let m := (hausdorff n X).prod (μ.prod ν)
  have hU : IsOpen U :=
    (isOpen_lt (continuous_fst.dist continuous_const) continuous_const).inter
      (isOpen_lt (D.jointSlack_continuous a₀ b₀ c t) continuous_const)
  have hfin : m U ≠ ∞ := by
    have hsub : U ⊆ closedBall p r ×ˢ (univ : Set (S × T)) := by
      intro z hz
      exact ⟨hz.1.le,mem_univ _⟩
    apply ne_top_of_le_ne_top _ (measure_mono hsub)
    change ((hausdorff n X).prod (μ.prod ν)) (closedBall p r ×ˢ univ) ≠ ∞
    rw [Measure.prod_prod,measure_univ,mul_one]
    exact (isCompact_closedBall p r).measure_lt_top.ne
  have hlog : TendstoUniformlyOn (fun k z => ε (D.index k)*Real.log (D.jointDensity (D.index k) t z))
      (D.jointSlack a₀ b₀ c t) atTop U := by
    have hh := D.joint_log_limit a₀ b₀ c hK hε1 hε0 hR hS hT hc r t
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro η hη
    filter_upwards [(Metric.tendstoUniformly_iff.mp hh) η hη] with k hk
    intro z hz
    exact hk (⟨z.1,hz.1.le⟩,z.2)
  exact negative_log_density_mass m (fun k => D.jointDensity (D.index k) t)
    (fun k => ε (D.index k)) (fun k => hε (D.index k)) (hε0.comp D.strict.tendsto_atTop)
    hU.measurableSet hfin (fun k z _ => D.jointDensity_pos _ t z)
    (D.jointSlack a₀ b₀ c t) hδ (fun _ hz => hz.2.le) hlog

theorem joint_limit_nonnegative_slack (a₀ : S) (b₀ : T) (c : ℝ) (hK : K ≤ 0)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0))
    {R : ℝ} (hR : 0 ≤ R) (hS : ∀ a:S, dist p a ≤ R) (hT : ∀ b:T, dist p b ≤ R)
    (hc : Tendsto (fun k => ε (D.index k)*(Real.log (D.left (D.index k) a₀)+
      Real.log (D.right (D.index k) b₀))) atTop (𝓝 c))
    (t : Ioo (0:ℝ) 1) (i : ℕ → ℕ) (hi : StrictMono i)
    (Q : ProbabilityMeasure (X × (S × T)))
    (hweak : Tendsto (fun k => D.jointLaw (D.index (i k)) t) atTop (𝓝 Q)) :
    ∀ᵐ z ∂(Q : Measure (X × (S × T))), 0 ≤ D.jointSlack a₀ b₀ c t z := by
  let U (N : ℕ) : Set (X × (S × T)) :=
    {z | dist z.1 p < (N:ℝ)+1 ∧ D.jointSlack a₀ b₀ c t z < -(1/((N:ℝ)+1))}
  have hnull N : (Q : Measure (X × (S × T))) (U N)=0 := by
    have hmass := (D.joint_negative_mass a₀ b₀ c hK hε1 hε0 hR hS hT hc t ((N:ℝ)+1)
      (show 0 < 1/((N:ℝ)+1) by positivity)).comp hi.tendsto_atTop
    change Tendsto (fun k => (D.jointMeasure (D.index (i k)) t) (U N)) atTop (𝓝 0) at hmass
    have hopen : IsOpen (U N) :=
      (isOpen_lt (continuous_fst.dist continuous_const) continuous_const).inter
        (isOpen_lt (D.jointSlack_continuous a₀ b₀ c t) continuous_const)
    have hb := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hopen
    change (Q : Measure (X × (S × T))) (U N) ≤ atTop.liminf
      (fun k => (D.jointMeasure (D.index (i k)) t) (U N)) at hb
    rw [hmass.liminf_eq] at hb
    exact le_antisymm hb bot_le
  have hae N : ∀ᵐ z ∂(Q : Measure (X × (S × T))), z ∉ U N := by
    apply ae_iff.mpr
    convert hnull N using 1
    congr 1
    ext z
    simp
  filter_upwards [ae_all_iff.mpr hae] with z hz
  by_contra hneg
  have hneg' : D.jointSlack a₀ b₀ c t z < 0 := lt_of_not_ge hneg
  obtain ⟨N,hN⟩ := exists_nat_gt (max (dist z.1 p) (1/(-D.jointSlack a₀ b₀ c t z)))
  have hdist : dist z.1 p < (N:ℝ)+1 := by
    have hh := lt_of_le_of_lt (le_max_left _ _) hN
    linarith
  have hinv : 1/(-D.jointSlack a₀ b₀ c t z) < (N:ℝ)+1 := by
    have hh := lt_of_le_of_lt (le_max_right _ _) hN
    linarith
  have hd : 1/((N:ℝ)+1) < -D.jointSlack a₀ b₀ c t z := by
    apply (div_lt_iff₀ (show 0 < (N:ℝ)+1 by positivity)).mpr
    have hh := (div_lt_iff₀ (neg_pos.mpr hneg')).mp hinv
    nlinarith only [hh]
  apply hz N
  exact ⟨hdist,by linarith only [hd]⟩

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
