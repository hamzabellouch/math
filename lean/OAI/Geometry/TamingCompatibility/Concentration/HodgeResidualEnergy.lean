import Mathlib
import OAI.Geometry.TamingCompatibility.Currents.Restriction
import OAI.Geometry.TamingCompatibility.Hodge.HodgeAntiL2Cross
import OAI.Geometry.TamingCompatibility.Hodge.HodgePositiveCrossLower

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set _root_.MeasureTheory _root_.OAI.MeasureTheory Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel unitT2

omit [T2Space X] in
lemma hodgeCubeRepresents_add {r : ℝ}
    {F G : PreL2 A J α hs ht true →ₗ[ℝ] ℝ} {U V : L2 A J α hs ht true}
    (hU : hodgeCubeRepresents A J α hs ht r F U) (hV : hodgeCubeRepresents A J α hs ht r G V) :
    hodgeCubeRepresents A J α hs ht r (F+G) (U+V) := by
  intro a
  rw [inner_add_left,hU a,hV a]
  rfl

lemma hodge_residual_energy_zero
    (μ ν : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (Q : L2 A J α hs ht true) (hQ : l2Star A J α hs ht Q = Q)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0)
    (hν : ∀ ξ : PreL2 A J α hs ht false,
      (positiveL2Source A J α hs ht ν + l2CurrentSource A J α hs ht Q)
        (hodgePreD A J α hs ht ξ) = 0)
    (r : ℝ) (hr : 0 < r) :
    let P := hodgePositiveCurrentFamily A J α hs ht D hD (hermitianMetric J α hs ht) μ r
    let P' := hodgePositiveCurrentFamily A J α hs ht D hD (hermitianMetric J α hs ht) ν r
    let V := hodgeRegularization A J α hs ht r Q
    ⟪P,l2Star A J α hs ht P'⟫+⟪P,V⟫+⟪P',V⟫+‖V‖^2 = 0 := by
  dsimp only
  let S := hodgeSmoothingCover A J α hs ht D hD r hr
  let g := hermitianMetric J α hs ht
  let V := hodgeRegularization A J α hs ht r Q
  have hV : l2Star A J α hs ht V = V := by
    dsimp only [V]
    rw [← hodgeRegularization_star,hQ]
  have hrep := hodgeRegularization_l2_represents A J α hs ht Q hr
  have he := hodge_regularized_zero_pairing A J α hs ht D hD r hr
    (positiveL2Source A J α hs ht μ+l2CurrentSource A J α hs ht Q)
    (positiveL2Source A J α hs ht ν+l2CurrentSource A J α hs ht Q)
    (S.regularize g μ+V) (S.regularize g ν+V)
    (hodgeCubeRepresents_add A J α hs ht (positiveL2Source_represents A J α hs ht D hD μ r hr S) hrep)
    (hodgeCubeRepresents_add A J α hs ht (positiveL2Source_represents A J α hs ht D hD ν r hr S) hrep)
    hT hν
  have hcross : ⟪V,l2Star A J α hs ht (S.regularize g ν)⟫ = ⟪S.regularize g ν,V⟫ := by
    rw [← l2Star_self_adjoint,hV,real_inner_comm]
  rw [map_add,inner_add_left,inner_add_right,inner_add_right,hV,hcross,real_inner_self_eq_norm_sq] at he
  simp only [hodgePositiveCurrentFamily,dite_eq_left hr]
  change ⟪S.regularize g μ,l2Star A J α hs ht (S.regularize g ν)⟫+
    ⟪S.regularize g μ,V⟫+⟪S.regularize g ν,V⟫+‖V‖^2 = 0
  linarith
end TamingCompatibility.GeometricHilbert

end
end

section

noncomputable section
open Filter
open scoped Topology
namespace TamingCompatibility
lemma zero_of_residual_energy_limit
    {V : Type*} [NormedAddCommGroup V]
    (q : ℕ → V) (Q : V) (w e a b : ℕ → ℝ)
    (hq : Tendsto q atTop (𝓝 Q)) (he : Tendsto e atTop (𝓝 0))
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (hlower : ∀ n, -e n ≤ w n)
    (henergy : ∀ n, w n+a n+b n+‖q n‖^2 = 0) : Q = 0 := by
  have hh : ∀ n, ‖q n‖^2 ≤ e n-a n-b n := by
    intro n
    have h₁ := hlower n
    have h₂ := henergy n
    linarith
  have hlim : ‖Q‖^2 ≤ (0:ℝ) := by
    have hl := le_of_tendsto_of_tendsto (hq.norm.pow 2) ((he.sub ha).sub hb) (Eventually.of_forall hh)
    simpa only [sub_zero] using hl
  apply norm_eq_zero.mp
  have hn := norm_nonneg Q
  nlinarith
end TamingCompatibility

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set _root_.MeasureTheory _root_.OAI.MeasureTheory Filter SummableCutoff
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

include D hD in
lemma concentration_forces_correction_zero
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (Q : L2 A J α hs ht true) (haQ : l2AntiProjection A J α hs ht Q = Q)
    (hQ : l2Star A J α hs ht Q = Q)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a+⟪Q,smoothL2 A J α hs ht true a⟫ = 0)
    (S : ConcentrationActivationData A J α hs ht E hE μ Q) : Q = 0 := by
  let Z := (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) ⁻¹' (exceptional S.cutoff)ᶜ
  let ν := μ.restrict Z
  have hre (U : Set (MetricUnit (hermitianMetric J α hs ht))) : ν.real U ≤ μ.real U :=
    ENNReal.toReal_mono (measure_ne_top μ U) (Measure.restrict_apply_le Z U)
  have hν1 : ν.real univ ≤ 1 := by simpa only [probReal_univ] using hre univ
  obtain ⟨M,hM,hgrowth⟩ := separating_probability_quadratic_growth J α hs ht μ hann
  have hνgrowth : ∀ x : X, ∀ s : ℝ, 0 < s →
      ν.real {u | hermitianEDist J α hs ht x u.val.proj < ENNReal.ofReal s} ≤ M*s^2 := by
    intro x s hs'
    exact (hre _).trans (hgrowth x s hs')
  have hr : Tendsto S.radius atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨S.radius_limit,Eventually.of_forall S.radius_pos⟩
  let P := fun n => hodgePositiveCurrentFamily A J α hs ht D hD (hermitianMetric J α hs ht) μ (S.radius n)
  let P' := fun n => hodgePositiveCurrentFamily A J α hs ht D hD (hermitianMetric J α hs ht) ν (S.radius n)
  let V := fun n => hodgeRegularization A J α hs ht (S.radius n) Q
  have hV : Tendsto V atTop (𝓝 Q) := (hodgeRegularization_tendsto A J α hs ht Q).comp hr
  have hp : Tendsto (fun n => ⟪P n,V n⟫) atTop (𝓝 0) :=
    (subprob_anti_cross_tendsto A J α hs ht E hE D hD μ (by simp) M hM hgrowth Q haQ).comp hr
  have hp' : Tendsto (fun n => ⟪P' n,V n⟫) atTop (𝓝 0) :=
    (subprob_anti_cross_tendsto A J α hs ht E hE D hD ν hν1 M hM hνgrowth Q haQ).comp hr
  obtain ⟨C,B,hC,hB,hbound⟩ := same_resolvent_positive_cross_lower A J α hs ht E hE D hD
  let e := fun n => C*(∫ v, physicalProfileMass J α hs ht μ (S.radius n) v.val.proj/(S.radius n)^2 ∂ν)+
    B*(S.radius n)^2*ν.real univ
  have he : Tendsto e atTop (𝓝 0) := by
    have hl := concentration_double_physical_tail A J α hs ht E hE μ Q S hann
    have hh := (hl.const_mul C).add (((S.radius_limit.pow 2).const_mul B).mul_const (ν.real univ))
    simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul,add_zero] using hh
  have hlower (n : ℕ) : -e n ≤ ⟪P n,l2Star A J α hs ht (P' n)⟫ := by
    have hh := hbound μ ν (S.radius n) (S.radius_pos n)
      (hodgeSmoothingCover A J α hs ht D hD (S.radius n) (S.radius_pos n))
    simp only [P,P',hodgePositiveCurrentFamily,dite_eq_left (S.radius_pos n)]
    dsimp only [e]
    convert hh using 1; ring
  have hν := concentration_residual_source_closed A J α hs ht E hE μ Q S hT
  have henergy (n : ℕ) : ⟪P n,l2Star A J α hs ht (P' n)⟫+⟪P n,V n⟫+⟪P' n,V n⟫+‖V n‖^2 = 0 :=
    hodge_residual_energy_zero A J α hs ht D hD μ ν Q hQ hT hν (S.radius n) (S.radius_pos n)
  exact zero_of_residual_energy_limit V Q (fun n => ⟪P n,l2Star A J α hs ht (P' n)⟫) e
    (fun n => ⟪P n,V n⟫) (fun n => ⟪P' n,V n⟫) hV he hp hp' hlower henergy
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
