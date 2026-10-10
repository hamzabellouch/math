import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.ChartUnitaryData
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGeometricCoefficients
import OAI.Geometry.TamingCompatibility.Charts.MetricCalculus

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.HodgeStarGeometry
open HodgeNormalSymbol HodgeNormalOperator HodgeFrame MetricModel MetricForms MetricHodge
open scoped ContDiff Topology RealInnerProductSpace
open ContinuousAlternatingMap Filter
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def starMap : W →L[ℝ] W := LinearMap.toContinuousLinearMap {
  toFun := UnitaryFrame.star
  map_add' := UnitaryFrame.star_add
  map_smul' := UnitaryFrame.star_smul }
@[simp] lemma starMap_apply (u : W) : starMap u = UnitaryFrame.star u := rfl
lemma starMap_adjoint : starMap.adjoint = starMap := by
  apply Eq.symm
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr UnitaryFrame.star_self_adjoint

 def swap (u : Q) : Q := WithLp.toLp 2 ![u 4,u 5,u 6,u 7,u 0,u 1,u 2,u 3]
def swapMap : Q →L[ℝ] Q := LinearMap.toContinuousLinearMap {
  toFun := swap
  map_add' := by intro a b; ext i; fin_cases i <;> simp [swap]
  map_smul' := by intro c a; ext i; fin_cases i <;> simp [swap] }
@[simp] lemma swapMap_apply (u : Q) : swapMap u = swap u := rfl
lemma swapMap_adjoint : swapMap.adjoint = swapMap := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_succ,swap]
  ring

lemma principal_intertwines (b : Fin 4 → EuclideanEnergy.V) (i : Fin 4) :
    HodgeFrozenEnergy.coefficient b i ∘L starMap = swapMap ∘L HodgeFrozenEnergy.coefficient b i := by
  ext u k
  simp only [ContinuousLinearMap.comp_apply,starMap_apply,swapMap_apply,
    HodgeFrozenEnergy.coefficient,normalSymbol_apply,symbol,UnitaryFrame.star_square]
  fin_cases k <;> rfl

lemma swap_join (u v : EuclideanEnergy.V) : swapMap (join u v) = join v u := by
  ext i
  fin_cases i <;> rfl
lemma swap_left (b : Fin 4 → EuclideanEnergy.V) (a : MetricForms.Form EuclideanEnergy.V 1) :
    swapMap (left b a) = right b a := by
  exact swap_join _ _
lemma swap_right (b : Fin 4 → EuclideanEnergy.V) (a : MetricForms.Form EuclideanEnergy.V 1) :
    swapMap (right b a) = left b a := by
  exact swap_join _ _

variable (g : Metric EuclideanEnergy.V) (J : EuclideanEnergy.V →L[ℝ] EuclideanEnergy.V)
  (F : MetricForms.Form EuclideanEnergy.V 2) (b : Fin 4 → EuclideanEnergy.V)
  (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
  (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
  (h0 : J (b 0)=b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2)=b 3) (h3 : J (b 3) = -b 2)
  (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
include hb horth h0 h1 h2 h3 hF
lemma combine_star_frame (u : W) :
    combine (fun j => starTwo g J F (basisForm g b j)) u = combine (basisForm g b) (starMap u) := by
  rw [combine_star_basis,combine_basis]
  apply coordinates_injective g (by simp [EuclideanEnergy.V]) b hb
  rw [coordinates_star g (by simp [EuclideanEnergy.V]) b hb J horth h0 h1 h2 h3 F hF,
    coordinates_reconstruct g b hb,coordinates_reconstruct g b hb]
  rfl

end TamingCompatibility.HodgeStarGeometry

end
end

section

noncomputable section
namespace TamingCompatibility.HodgeStarGeometry
open HodgeNormalSymbol HodgeNormalOperator HodgeFrame MetricModel MetricForms MetricHodge
open EuclideanEnergy ContinuousAlternatingMap Filter Set
open scoped ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma combineThree_extDeriv (ψ : Fin 6 → V → MetricForms.Form V 2) {x : V}
    (hψ : ∀ j, DifferentiableAt ℝ (ψ j) x) (u : W) :
    combineThree (fun j => extDeriv (ψ j) x) u =
      extDeriv (fun y => combine (fun j => ψ j y) u) x := by
  simp only [combine_apply,combineThree_apply]
  rw [HodgeFrame.extDeriv_sum (f := fun j y => u j • ψ j y)
    (fun j => (hψ j).const_smul (u j))]
  apply Finset.sum_congr rfl
  intro j _
  exact (extDeriv_fun_smul (u j) (ψ j)).symm

lemma combineThree_intertwines (ψ φ : Fin 6 → V → MetricForms.Form V 2) {x : V}
    (hψ : ∀ j, DifferentiableAt ℝ (ψ j) x) (hφ : ∀ j, DifferentiableAt ℝ (φ j) x)
    (hstar : ∀ᶠ y in 𝓝 x, ∀ u : W, combine (fun j => φ j y) u = combine (fun j => ψ j y) (starMap u))
    (u : W) : combineThree (fun j => extDeriv (φ j) x) u =
      combineThree (fun j => extDeriv (ψ j) x) (starMap u) := by
  rw [combineThree_extDeriv φ hφ,combineThree_extDeriv ψ hψ]
  have he : (fun y => combine (fun j => φ j y) u) =ᶠ[𝓝 x]
      (fun y => combine (fun j => ψ j y) (starMap u)) := hstar.mono fun _ h => h u
  unfold extDeriv
  rw [he.fderiv_eq (𝕜 := ℝ)]

lemma lower_intertwines (g : Metric V) (F : MetricForms.Form V 2) (b : Fin 4 → V)
    (ψ φ : Fin 6 → V → MetricForms.Form V 2) {x : V}
    (hψ : ∀ j, DifferentiableAt ℝ (ψ j) x) (hφ : ∀ j, DifferentiableAt ℝ (φ j) x)
    (hstar : ∀ᶠ y in 𝓝 x, ∀ u : W, combine (fun j => φ j y) u = combine (fun j => ψ j y) (starMap u)) :
    HodgeNormalOperator.lower g F b ψ φ x ∘L starMap =
      swapMap ∘L HodgeNormalOperator.lower g F b ψ φ x := by
  have h1 (u : W) := combineThree_intertwines ψ φ hψ hφ hstar u
  have h2 (u : W) : combineThree (fun j => extDeriv (φ j) x) (starMap u) =
      combineThree (fun j => extDeriv (ψ j) x) u := by
    simpa only [starMap_apply,UnitaryFrame.star_square] using h1 (starMap u)
  apply ContinuousLinearMap.ext
  intro u
  simp only [HodgeNormalOperator.lower,ContinuousLinearMap.comp_apply,_root_.add_apply,
    map_add,swap_left,swap_right,h2,h1,add_comm]

end TamingCompatibility.HodgeStarGeometry

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus
open HodgeNormalSymbol HodgeStarGeometry HodgeGeometricCoefficients HodgeNormalOperator HodgeFrame
open Filter Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance starGeometryMetricTensorNormedAddCommGroup : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance starGeometryMetricTensorNormedSpace : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)

lemma geometric_lower_intertwines (hs : IsSmooth α) {x : Space} (hx : x ∈ D.domain) :
    HodgeGeometricCoefficients.lower (coordinateMetric J α ht p) (coordinateJ J p)
      (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm) D.frame x ∘L starMap =
    swapMap ∘L HodgeGeometricCoefficients.lower (coordinateMetric J α ht p) (coordinateJ J p)
      (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm) D.frame x := by
  let g := coordinateMetric J α ht p
  let j := coordinateJ J p
  let F := ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm
  have hg := (coordinateMetric_smooth J α hs ht p).mono D.domain_subset
  have hj := (coordinateJ_smooth J p).mono D.domain_subset
  have hF := (ManifoldForms.smooth_chart _ (hs.invariantPart J) p).mono D.domain_subset
  have hψ := HodgeGeometricCoefficients.frame_smooth hg D.frame_smooth
  have hφ := HodgeGeometricCoefficients.starFrame_smooth g j F D.frame D.domain_open hg hj
    (fun y hy => coordinateJ_square J p (D.domain_subset hy))
    (fun y hy => coordinateMetric_hermitian J α ht p (D.domain_subset hy)) hF D.frame_smooth
  apply lower_intertwines
  · exact fun k => ((hψ k).contDiffAt (D.domain_open.mem_nhds hx)).differentiableAt (by simp)
  · exact fun k => ((hφ k).contDiffAt (D.domain_open.mem_nhds hx)).differentiableAt (by simp)
  · filter_upwards [D.domain_open.mem_nhds hx] with y hy
    intro u
    obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex y hy
    exact combine_star_frame (g y) (j y) (F y) (fun k => D.frame k y) (D.frame_gram y hy)
      (coordinateMetric_hermitian J α ht p (D.domain_subset hy)) h0 h1 h2 h3
      (ManifoldTop.coordinateFundamental J α ht p (D.domain_subset hy)) u

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
