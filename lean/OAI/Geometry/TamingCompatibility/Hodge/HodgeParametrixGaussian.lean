import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.HodgeCompactResidual
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCutoffSquare
import OAI.Geometry.TamingCompatibility.Hodge.HodgeParametrixPatch

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FlatHeat
lemma heat_compare {t a : ℝ} (ht : 0 < t) (ha : 0 < a) {z w : V}
    (hw : ‖w‖ ≤ a*‖z‖) : heat t z ≤ a^4*heat (a^2*t) w := by
  have hs : ‖w‖^2 ≤ a^2*‖z‖^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg w) hw 2
  have he : -‖z‖^2/(4*t) ≤ -‖w‖^2/(4*(a^2*t)) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*(a^2*t))).mpr
    have heq : (-‖z‖^2/(4*t))*(4*(a^2*t)) = -(a^2*‖z‖^2) := by field_simp
    rw [heq]
    linarith
  have hp : a^4*(4*Real.pi*(a^2*t))⁻¹^2 = (4*Real.pi*t)⁻¹^2 := by
    field_simp
  unfold heat
  rw [←mul_assoc,hp]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (sq_nonneg _)
end TamingCompatibility.GeometricHilbert.FlatHeat

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set MeasureTheory
open HodgeNormalSymbol FirstJetGauge OrthogonalJets UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance hodgeParametrixGaussianMetricNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeParametrixGaussianMetricNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
  (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)

include hg hB

lemma normalMap_compact_bound (K : Set Space) (hK : IsCompact K) {r : ℝ} (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ q ∈ K, ∀ z : Space, ‖z‖ ≤ r →
      ‖normalMap g B q z - q‖ ≤ C*‖z‖ := by
  obtain ⟨C,hC,hb⟩ := linear_bound_on_tube (fun x : Space × Space => normalMap g B x.1 x.2)
    K hK hr (fun _ _ => (normalMap_joint g B hg hB).contDiffAt)
  refine ⟨C+1,by linarith,fun q hq z hz => ?_⟩
  have hh : ‖normalMap g B q z - q‖ ≤ C*‖z‖ := by
    simpa only [normalMap_zero] using hb q hq z hz
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg z))

attribute [local irreducible] normalGauge normalFirst

lemma normalGauge_norm_le (hs : IsSmooth α) {q : Space}
    (hactual : ActualData J α ht p D q g B) (z : Space) :
    ‖normalGauge J α ht p D g B (q,z)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [ContinuousLinearMap.norm_map_of_mem_unitary
    (normalGauge_unitary J α ht p D g B hs hg hB hactual z),one_mul]

lemma leadingPatch_gaussian (hs : IsSmooth α)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (hψ : ∀ q, 0 ≤ ψ q ∧ ψ q ≤ 1) (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (K : Set Space) (hK : IsCompact K) (hψK : Function.support ψ ⊆ K)
    (hactual : ∀ q ∈ K, ActualData J α ht p D q g B)
    {r : ℝ} (hr : 0 ≤ r) (hχr : Function.support χ ⊆ Metric.closedBall (0 : Space) r) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ q y : Space,
      ‖leadingPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t (q,y)‖ ≤
        C ^ 4*FlatHeat.heat (C ^ 2*t) (y - q) := by
  classical
  obtain ⟨C,hC,hmap⟩ := normalMap_compact_bound g B hg hB K hK hr
  refine ⟨C,hC,fun t htpos q y => ?_⟩
  let A := geometricNormalChart g B hg hB q₀ Bq hBq
  by_cases hy : (q,y) ∈ A.target
  · let x := A.symm (q,y)
    have hfst : x.1 = q := geometricNormalChart_symm_fst g B hg hB q₀ Bq hBq hy
    have hsnd : normalMap g B q x.2 = y := geometricNormalChart_symm_right g B hg hB q₀ Bq hBq hy
    have he : leadingPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t (q,y) =
        (ψ q*χ x.2*FlatHeat.heat t x.2) • normalGauge J α ht p D g B (q,x.2) := by
      change (if (q,y) ∈ A.target then leadingCoordinate J α ht p D g B ψ χ t x else 0) = _
      rw [ite_eq_left hy]
      unfold leadingCoordinate
      change (ψ x.1*χ x.2*FlatHeat.heat t x.2) • normalGauge J α ht p D g B x = _
      conv_lhs => rw [show x = (q,x.2) from Prod.ext hfst rfl]
    rw [he]
    by_cases hq : ψ q = 0
    · simp only [hq,zero_mul,norm_smul,Real.norm_eq_abs,abs_zero]
      exact mul_nonneg (by positivity) (FlatHeat.heat_nonneg _ _)
    by_cases hz : χ x.2 = 0
    · simp only [hz,mul_zero,zero_mul,norm_smul,Real.norm_eq_abs,abs_zero]
      exact mul_nonneg (by positivity) (FlatHeat.heat_nonneg _ _)
    have hqK := hψK hq
    have hzr : ‖x.2‖ ≤ r := by simpa using hχr hz
    have hU := normalGauge_norm_le J α ht p D g B hg hB hs (hactual q hqK) x.2
    have hscalar : 0 ≤ ψ q*χ x.2*FlatHeat.heat t x.2 := by
      exact mul_nonneg (mul_nonneg (hψ q).1 (hχ x.2).1) (FlatHeat.heat_nonneg _ _)
    have hprod : ψ q*χ x.2 ≤ 1 := by
      simpa using mul_le_mul (hψ q).2 (hχ x.2).2 (hχ x.2).1 zero_le_one
    calc
      _ = (ψ q*χ x.2*FlatHeat.heat t x.2)*‖normalGauge J α ht p D g B (q,x.2)‖ := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hscalar]
      _ ≤ (ψ q*χ x.2*FlatHeat.heat t x.2)*1 := mul_le_mul_of_nonneg_left hU hscalar
      _ ≤ FlatHeat.heat t x.2 := by
        simpa only [mul_one,one_mul] using mul_le_mul_of_nonneg_right hprod (FlatHeat.heat_nonneg t x.2)
      _ ≤ _ := FlatHeat.heat_compare htpos hC (by rw [← hsnd]; exact hmap q hqK x.2 hzr)
  · have hz : leadingPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t (q,y) = 0 := by
      exact ite_eq_right hy
    rw [hz,norm_zero]
    exact mul_nonneg (by positivity) (FlatHeat.heat_nonneg _ _)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
