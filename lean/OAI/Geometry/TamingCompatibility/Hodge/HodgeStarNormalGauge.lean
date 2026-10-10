import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.HodgeCompactResidual
import OAI.Geometry.TamingCompatibility.Hodge.HodgeApproximateIdentity
import OAI.Geometry.TamingCompatibility.Hodge.HodgeStarGeometry

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol HodgeStarGeometry FirstJetGauge OrthogonalJets Filter Set OperatorCalculus
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance hodgeStarNormalGaugeCommuteMetricNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeStarNormalGaugeCommuteMetricNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma pullCoefficient_intertwines (a : Fin 4 → W →L[ℝ] Q) (C : Space →L[ℝ] Space)
    (h : ∀ k, a k ∘L starMap = swapMap ∘L a k) (i : Fin 4) :
    pullCoefficient a C i ∘L starMap = swapMap ∘L pullCoefficient a C i := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [pullCoefficient,ContinuousLinearMap.comp_apply,sum_apply,smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg ((C (EuclideanEnergy.e k) i) • ·)
    (congrArg (fun L : W →L[ℝ] Q => L u) (h k))

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

lemma pulledA_intertwines (q z : Space) (i : Fin 4) :
    pulledA J α ht p D g B q i z ∘L starMap =
      swapMap ∘L pulledA J α ht p D g B q i z := by
  exact pullCoefficient_intertwines _ _ (fun k => principal_intertwines _ k) i

lemma pulledB_intertwines (hs : IsSmooth α) {q z : Space}
    (hz : normalMap g B q z ∈ D.domain) :
    pulledB J α ht p D g B q z ∘L starMap = swapMap ∘L pulledB J α ht p D g B q z :=
  geometric_lower_intertwines J α ht p D hs hz

lemma normalFirst_commutes (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ normalDomain J α ht p D g B) (j : Fin 4) :
    Commute (normalFirst J α ht p D g B j x) starMap := by
  apply firstMatrix_commutes _ _ _ _ starMap swapMap starMap_adjoint swapMap_adjoint
  · intro i
    exact ((pulledA_joint J α ht p D g B hg hB hx.1 i).comp x.2
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  · exact ((normalDensity_smooth g B hg hB hx.2).comp x.2
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  · exact fun i => Filter.Eventually.of_forall fun y => pulledA_intertwines J α ht p D g B x.1 y i
  · exact pulledB_intertwines J α ht p D g B hs hx.1.1

lemma normalGauge_commutes (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {q : Space} (hq : (q,0) ∈ normalDomain J α ht p D g B) (z : Space) :
    Commute (normalGauge J α ht p D g B (q,z)) starMap := by
  unfold normalGauge
  exact gauge_commutes _ _ starMap (fun j => normalFirst_commutes J α ht p D g B hs hg hB hq j) z

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.UnitaryFrame
open HodgeStarGeometry
open scoped RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma unitary_star_angular (U : W →L[ℝ] W) (hU : U ∈ unitary (W →L[ℝ] W))
    (hstar : Commute U starMap) (v w : V) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ⟪line v, star (U (line w))⟫ =
      (1/2 : ℝ)*‖line v-U (line w)‖^2 - (1/4 : ℝ)*‖fundamental-U fundamental‖^2 := by
  have hcomm (u : W) : U (star u) = star (U u) :=
    congrArg (fun L : W →L[ℝ] W => L u) hstar
  have hdual : selfDualPart (U (line w)) = (1/2 : ℝ) • U fundamental := by
    rw [selfDualPart,← hcomm,← map_add,← map_smul]
    simpa only [selfDualPart,map_smul] using congrArg U (unit_line_selfDualPart hw)
  exact angular_identity _ _ _ _ (unit_line_norm hv)
    ((ContinuousLinearMap.norm_map_of_mem_unitary hU _).trans (unit_line_norm hw))
    fundamental_norm_sq
    (by rw [ContinuousLinearMap.norm_map_of_mem_unitary hU,fundamental_norm_sq])
    (unit_line_selfDualPart hv) hdual

end TamingCompatibility.UnitaryFrame

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol HodgeStarGeometry FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance hodgeStarNormalGaugeAngularMetricNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeStarNormalGaugeAngularMetricNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

@[simp] lemma normalGauge_zero (q : Space) : normalGauge J α ht p D g B (q,0) = 1 := by
  simp [normalGauge]

attribute [local irreducible] normalGauge normalFirst

lemma normalGauge_angular (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {q : Space} (hactual : ActualData J α ht p D q g B) (z v w : Space)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ⟪UnitaryFrame.line v,UnitaryFrame.star (normalGauge J α ht p D g B (q,z) (UnitaryFrame.line w))⟫ =
      (1/2 : ℝ)*‖UnitaryFrame.line v-normalGauge J α ht p D g B (q,z) (UnitaryFrame.line w)‖^2 -
      (1/4 : ℝ)*‖UnitaryFrame.fundamental-normalGauge J α ht p D g B (q,z) UnitaryFrame.fundamental‖^2 := by
  exact UnitaryFrame.unitary_star_angular _
    (normalGauge_unitary J α ht p D g B hs hg hB hactual z)
    (normalGauge_commutes J α ht p D g B hs hg hB (hactual.center J α ht p D g B).1 z) v w hv hw

lemma compact_normalGauge_angular (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (K : Set Space) (hK : IsCompact K)
    (hactual : ∀ q ∈ K, ActualData J α ht p D q g B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧ ∀ q ∈ K, ∀ z : Space, ‖z‖ ≤ r →
      ∀ v w : Space, ‖v‖ = 1 → ‖w‖ = 1 →
        (1/2 : ℝ)*‖UnitaryFrame.line v-normalGauge J α ht p D g B (q,z) (UnitaryFrame.line w)‖^2 - C*‖z‖^2 ≤
        ⟪UnitaryFrame.line v,UnitaryFrame.star (normalGauge J α ht p D g B (q,z) (UnitaryFrame.line w))⟫ := by
  let F : Space × Space → W := fun x => normalGauge J α ht p D g B x UnitaryFrame.fundamental
  let Ω : Set (Space × Space) := (fun x : Space × Space => (x.1,(0 : Space))) ⁻¹' normalDomain J α ht p D g B
  have hΩ : IsOpen Ω := (normalDomain_open J α ht p D g B hg hB).preimage
    (continuous_fst.prodMk continuous_const)
  have hKΩ : K ×ˢ {(0 : Space)} ⊆ Ω := by
    rintro ⟨q,z⟩ ⟨hq,_⟩
    exact ((hactual q hq).center J α ht p D g B).1
  have hF : ∀ x ∈ Ω, ContDiffAt ℝ ∞ F x := fun x hx =>
    (normalGauge_smooth J α ht p D g B hs hg hB hx).clm_apply contDiffAt_const
  obtain ⟨C,hC,r,hr,_,hb⟩ := local_linear_bound F K hK Ω hΩ hKΩ hF
  refine ⟨C ^ 2,by positivity,r,hr,fun q hq z hz v w hv hw => ?_⟩
  rw [normalGauge_angular J α ht p D g B hs hg hB (hactual q hq) z v w hv hw]
  have hbound : ‖UnitaryFrame.fundamental-normalGauge J α ht p D g B (q,z) UnitaryFrame.fundamental‖ ≤ C*‖z‖ := by
    have hh := hb q hq z hz
    simpa only [F,normalGauge_zero,one_apply_eq_self,norm_sub_rev] using hh
  have hsq := sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg z)) |>.mpr hbound
  nlinarith [sq_nonneg ‖UnitaryFrame.fundamental-normalGauge J α ht p D g B (q,z) UnitaryFrame.fundamental‖]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
