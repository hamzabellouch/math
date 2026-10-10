import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeAtlasPatches

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open Set UniformJets
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : ParametrixData J α ht p)

lemma normalChart_smooth : ContDiff ℝ ∞ (D.normalChart : Space × Space → Space × Space) :=
  geometricNormalChart_smooth _ _ _ _ _ _ _

lemma normalChart_diagonal {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p p) D.radius) :
    (q,q) ∈ inverseRegularDomain D.normalChart ∧ D.normalChart.symm (q,q) = (q,0) := by
  have hx : (q,0) ∈ D.normalCompact := ⟨hq,Metric.mem_closedBall_self D.radius_pos.le⟩
  have hi := (D.tube hx).1.1.2
  have he := D.normalChart.left_inv (D.normalCompact_source hx)
  have hh : D.normalChart (q,0) = (q,q) := by
    change (q,normalMap D.metricExtension D.frameExtension q 0) = (q,q)
    rw [normalMap_zero]
  change D.normalChart (q,0) ∈ inverseRegularDomain D.normalChart at hi
  rw [hh] at hi he
  exact ⟨hi,he⟩

lemma normal_inverse_near :
    ∃ L : ℝ, 0 < L ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ q : Space,
      q ∈ Metric.closedBall (extChartAt Model p p) D.radius → ∀ y : Space, ‖y-q‖ ≤ ε →
      (q,y) ∈ D.physicalCompact ∧
      ‖(D.normalChart.symm (q,y)).2‖ ≤ L*‖y-q‖ ∧
      D.normalCutoff (D.normalChart.symm (q,y)).2 = 1 := by
  let K := Metric.closedBall (extChartAt Model p p) D.radius
  let T : Space × Space → Space × Space := fun x => (x.1,x.1+x.2)
  let O := T ⁻¹' inverseRegularDomain D.normalChart
  let F : Space × Space → Space := fun x => (D.normalChart.symm (T x)).2
  have hT : ContDiff ℝ ∞ T := contDiff_fst.prodMk (contDiff_fst.add contDiff_snd)
  have hO : IsOpen O := (inverseRegularDomain_open D.normalChart D.normalChart_smooth).preimage hT.continuous
  have hKO : K ×ˢ {(0 : Space)} ⊆ O := by
    rintro ⟨q,z⟩ ⟨hq,hz⟩
    have hz' : z = 0 := hz
    subst z
    simpa only [O,T,Set.mem_preimage,add_zero] using (D.normalChart_diagonal hq).1
  have hF : ∀ x ∈ O, ContDiffAt ℝ ∞ F x := by
    intro x hx
    exact (((inverseRegularDomain_smooth D.normalChart D.normalChart_smooth) (T x) hx).contDiffAt
      ((inverseRegularDomain_open D.normalChart D.normalChart_smooth).mem_nhds hx)).comp x hT.contDiffAt |>.snd
  obtain ⟨C,hC,r,hr,hsub,hlin⟩ := local_linear_bound F K (isCompact_closedBall _ _) O hO hKO hF
  let L := C+1
  have hL : 0 < L := by dsimp [L]; linarith
  let ε := min r (D.radius/(4*L))
  have hε : 0 < ε := lt_min hr (div_pos D.radius_pos (by positivity))
  refine ⟨L,hL,ε,hε,fun q hq y hy => ?_⟩
  have hyr : ‖y-q‖ ≤ r := hy.trans (min_le_left _ _)
  have horg := hsub (show (q,y-q) ∈ K ×ˢ Metric.closedBall (0 : Space) r from
    ⟨hq,by simpa only [Metric.mem_closedBall,dist_zero_right] using hyr⟩)
  have hmem : (q,y) ∈ inverseRegularDomain D.normalChart := by
    simpa only [O,T,Set.mem_preimage,add_sub_cancel] using horg
  have he0 : F (q,0) = 0 := by
    dsimp only [F,T]
    rw [add_zero,(D.normalChart_diagonal hq).2]
  have hnorm : ‖(D.normalChart.symm (q,y)).2‖ ≤ L*‖y-q‖ := by
    have hh := hlin q hq (y-q) hyr
    rw [he0,sub_zero] at hh
    change ‖(D.normalChart.symm (q,q+(y-q))).2‖ ≤ C*‖y-q‖ at hh
    rw [add_sub_cancel] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) (norm_nonneg _))
  have hz : ‖(D.normalChart.symm (q,y)).2‖ ≤ D.radius/4 := by
    apply hnorm.trans
    calc
      L*‖y-q‖ ≤ L*(D.radius/(4*L)) :=
        mul_le_mul_of_nonneg_left (hy.trans (min_le_right _ _)) hL.le
      _ = D.radius/4 := by field_simp
  have hfst : (D.normalChart.symm (q,y)).1 = q :=
    geometricNormalChart_symm_fst _ _ _ _ _ _ _ hmem.1
  have hn : D.normalChart.symm (q,y) ∈ D.normalCompact := by
    refine ⟨?_,?_⟩
    · rw [hfst]; exact hq
    · rw [Metric.mem_closedBall,dist_zero_right]
      exact hz.trans (by linarith [D.radius_pos])
  refine ⟨⟨D.normalChart.symm (q,y),hn,D.normalChart.right_inv hmem.1⟩,hnorm,?_⟩
  exact D.normalCutoff.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right,normalCutoff] using hz)
end ParametrixData
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
