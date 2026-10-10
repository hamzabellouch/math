import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.ChartUnitaryData
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGeometricCoefficients

namespace OAI

section
section

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff SchwartzMap RealInnerProductSpace
namespace TamingCompatibility.HodgeGeometricCoefficients
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy HodgeFrame HodgeNormalOperator
open HodgeNormalSymbol (W Q)
open HodgeMatrixEnergy (Field)

def field (g : V → Metric V) (b : Fin 4 → V → V) (f : Field) (x : V) : MetricForms.Form V 2 :=
  ∑ j, f j x • frame g b j x
def starredField (g : V → Metric V) (J : V → V →L[ℝ] V) (F : V → MetricForms.Form V 2)
    (b : Fin 4 → V → V) (f : Field) (x : V) : MetricForms.Form V 2 :=
  ∑ j, f j x • starFrame g J F b j x
def operator (g : V → Metric V) (J : V → V →L[ℝ] V) (F : V → MetricForms.Form V 2)
    (b : Fin 4 → V → V) (f : Field) (x : V) : Q :=
  left (fun i => b i x) (starThree (g x) (F x) (extDeriv (starredField g J F b f) x)) +
    right (fun i => b i x) (starThree (g x) (F x) (extDeriv (field g b f) x))

lemma starredField_eq (g : V → Metric V) (J : V → V →L[ℝ] V) (F : V → MetricForms.Form V 2)
    (b : Fin 4 → V → V) (f : Field) (x : V) :
    starredField g J F b f x = starTwo (g x) (J x) (F x) (field g b f x) :=
  combine_star_basis (g x) (J x) (F x) (fun i => b i x) (HodgeMatrixEnergy.value f x)

lemma extDeriv_sum_zero {f : Field} {x : V} (hf : ∀ j, x ∉ tsupport (f j))
    (a : Fin 6 → V → MetricForms.Form V 2) : extDeriv (fun y => ∑ j, f j y • a j y) x = 0 := by
  have he : (fun y => ∑ j, f j y • a j y) =ᶠ[𝓝 x] (fun _ => 0) := by
    have h := Filter.eventually_all.mpr (fun j => notMem_tsupport_iff_eventuallyEq.mp (hf j))
    filter_upwards [h] with y hy
    simp only [hy,Pi.zero_apply,zero_smul,Finset.sum_const_zero]
  unfold extDeriv
  rw [he.fderiv_eq,fderiv_fun_const]
  exact map_zero _

variable (g : V → Metric V) (J : V → V →L[ℝ] V) (F : V → MetricForms.Form V 2)
  (b : Fin 4 → V → V) {U : Set V} (hU : IsOpen U)
  (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
  (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
  (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
  (hF : ContDiffOn ℝ ∞ F U) (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U)
  (hgram : ∀ x ∈ U, ∀ i j, (g x).bilinear (b i x) (b j x) = if i=j then 1 else 0)
  (hcplx : ∀ x ∈ U, J x (b 0 x) = b 1 x ∧ J x (b 1 x) = -b 0 x ∧
    J x (b 2 x) = b 3 x ∧ J x (b 3 x) = -b 2 x)
  (hfund : ∀ x ∈ U, ∀ u v, F x ![u,v] = (g x).bilinear (J x u) v)
include hU hg hJ hJs hgJ hF hb hgram hcplx hfund
lemma operator_system (f : Field) (hf : ∀ j, tsupport (f j) ⊆ U) (x : V) :
    operator g J F b f x = HodgeMatrixEnergy.system (principal b) (lower g J F b) f x := by
  by_cases hx : x ∈ U
  · obtain ⟨h0,h1,h2,h3⟩ := hcplx x hx
    have he := operator_expansion (g x) (F x) (fun i => b i x)
      (frame g b) (starFrame g J F b) (fun j => f j) (fun j => (f j).differentiableAt)
      (fun j => ((frame_smooth hg hb j).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx))
      (fun j => ((starFrame_smooth g J F b hU hg hJ hJs hgJ hF hb j).differentiableOn
        (by simp)).differentiableAt (hU.mem_nhds hx))
    have hr (i : Fin 4) : rawPrincipal (g x) (F x) (fun i => b i x)
        (fun j => frame g b j x) (fun j => starFrame g J F b j x) i = principal b i x :=
      rawPrincipal_eq (g x) (F x) (fun i => b i x) (hgram x hx) (J x) (hgJ x hx)
        h0 h1 h2 h3 (hfund x hx) i
    simp only [hr] at he
    change left _ (starThree _ _ (extDeriv (fun y => ∑ j, f j y • starFrame g J F b j y) x)) +
      right _ (starThree _ _ (extDeriv (fun y => ∑ j, f j y • frame g b j y) x)) =
      (∑ i, principal b i x (WithLp.toLp 2 (fun j => fderiv ℝ (f j) x (e i)))) +
      HodgeNormalOperator.lower (g x) (F x) (fun i => b i x) (frame g b) (starFrame g J F b) x
        (WithLp.toLp 2 (fun j => f j x))
    exact he
  · have hn (j : Fin 6) : x ∉ tsupport (f j) := fun h => hx (hf j h)
    have hz (j : Fin 6) := image_eq_zero_of_notMem_tsupport (hn j)
    have hd (j : Fin 6) := fderiv_of_notMem_tsupport ℝ (hn j)
    have hv : HodgeMatrixEnergy.value f x = 0 := by ext j; exact hz j
    have hdv (i : Fin 4) : HodgeMatrixEnergy.derivative f i x = 0 := by
      ext j
      change coordinateDeriv i (f j) x = 0
      simp only [coordinateDeriv,SchwartzMap.lineDerivOp_apply_eq_fderiv,hd,zero_apply]
    change left _ (starThree _ _ (extDeriv (fun y => ∑ j, f j y • starFrame g J F b j y) x)) +
      right _ (starThree _ _ (extDeriv (fun y => ∑ j, f j y • frame g b j y) x)) = _
    rw [extDeriv_sum_zero hn, extDeriv_sum_zero hn]
    simp only [MetricHodge.starThree_zero, _root_.map_zero, add_zero,
      HodgeMatrixEnergy.system, hv, hdv, Finset.sum_const_zero]

theorem geometric_local_garding {x₀ : V} (hx₀ : x₀ ∈ U) :
    ∃ r K C : ℝ, 0 < r ∧ 0 < K ∧ 0 < C ∧ Metric.closedBall x₀ (2*r) ⊆ U ∧
      ∀ f : Field, (∀ j, tsupport (f j) ⊆ Metric.closedBall x₀ r) →
        (∫ x, HodgeMatrixEnergy.gradient f x) ≤ K * (∫ x, ‖operator g J F b f x‖^2) +
          C * (∫ x, ‖HodgeMatrixEnergy.value f x‖^2) := by
  let B := (basisOfFrame (g x₀) (by simp [V]) (fun i => b i x₀) (hgram x₀ hx₀)).toBasis.map
    (equiv (g x₀)).toLinearEquiv
  have hB (i : Fin 4) : B i = b i x₀ := by
    simp only [B,Module.Basis.map_apply,OrthonormalBasis.coe_toBasis,basisOfFrame_apply]
    rfl
  have hBe : (fun i => b i x₀) = B := (funext hB).symm
  let K := DirectionalEnergy.coordinateConstant B
  have hK : 0 < K := DirectionalEnergy.coordinateConstant_pos B
  have henergy (f : Field) : (∫ x, HodgeMatrixEnergy.gradient f x) ≤ K *
      (∫ x, ‖HodgeMatrixEnergy.constantSystem (principal b · x₀) f x‖^2) := by
    simpa only [principal,hBe] using HodgeFrozenEnergy.frozen_energy B f
  obtain ⟨r,C,hr,hC,hrU,he⟩ := HodgeMatrixEnergy.local_garding (principal b · x₀) hK henergy
    hU hx₀ (principal b) (lower g J F b) (fun i => (principal_smooth hb i).continuousOn)
    (lower_smooth g J F b hU hg hJ hJs hgJ hF hb).continuousOn (fun _ => rfl)
  refine ⟨r,4*K,8*K*C^2,hr,by positivity,by positivity,hrU,?_⟩
  intro f hf
  have hrU' : Metric.closedBall x₀ r ⊆ U :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hrU
  simpa only [operator_system g J F b hU hg hJ hJs hgJ hF hb hgram hcplx hfund f
    (fun j => (hf j).trans hrU')] using he f hf
end TamingCompatibility.HodgeGeometricCoefficients

end
end

section
noncomputable section
open scoped Manifold ContDiff SchwartzMap
namespace TamingCompatibility.HodgeChart
open ManifoldHodge ManifoldVolume ManifoldForms ManifoldLocalization
open MetricModel MetricForms MetricHodge EuclideanEnergy
open MeasureTheory Set
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

structure Data (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X)
    extends GeometricChart.Data J α ht p where
  fullEnergyConstant : ℝ
  fullLowerConstant : ℝ
  fullEnergy_pos : 0 < fullEnergyConstant
  fullLower_pos : 0 < fullLowerConstant
  fullGarding : ∀ f : HodgeMatrixEnergy.Field,
    (∀ j, tsupport (f j) ⊆ Metric.closedBall (extChartAt Model p p) radius) →
    (∫ x, HodgeMatrixEnergy.gradient f x) ≤ fullEnergyConstant * (∫ x,
      ‖HodgeGeometricCoefficients.operator (coordinateMetric J α ht p) (coordinateJ J p)
        (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm) frame f x‖^2) +
      fullLowerConstant * (∫ x, ‖HodgeMatrixEnergy.value f x‖^2)

theorem data_nonempty (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
    (ht : Tames α J) (p : X) : Nonempty (Data J α ht p) := by
  let D := GeometricChart.data J α hs ht p
  have hp : extChartAt Model p p ∈ D.domain := D.ball_subset
    (Metric.mem_closedBall_self (by linarith [D.radius_pos]))
  obtain ⟨r,K,C,hr,hK,hC,hrU,hgard⟩ := HodgeGeometricCoefficients.geometric_local_garding
    (coordinateMetric J α ht p) (coordinateJ J p)
    (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm) D.frame D.domain_open
    ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset)
    ((coordinateJ_smooth J p).mono D.domain_subset)
    (fun x hx => coordinateJ_square J p (D.domain_subset hx))
    (fun x hx => coordinateMetric_hermitian J α ht p (D.domain_subset hx))
    ((smooth_chart _ (hs.invariantPart J) p).mono D.domain_subset) D.frame_smooth
    D.frame_gram D.frame_complex
    (fun x hx => ManifoldTop.coordinateFundamental J α ht p (D.domain_subset hx)) hp
  let D' : GeometricChart.Data J α ht p := { D with
    radius := min r D.radius
    radius_pos := lt_min hr D.radius_pos
    ball_subset := (Metric.closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))).trans hrU
    garding := fun A B hA hB => D.garding A B
      (hA.trans (Metric.closedBall_subset_closedBall (min_le_right _ _)))
      (hB.trans (Metric.closedBall_subset_closedBall (min_le_right _ _))) }
  exact ⟨{ toData := D'
           fullEnergyConstant := K
           fullLowerConstant := C
           fullEnergy_pos := hK
           fullLower_pos := hC
           fullGarding := fun f hf => hgard f (fun j => (hf j).trans
             (Metric.closedBall_subset_closedBall (min_le_left _ _))) }⟩

def data (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
    (ht : Tames α J) (p : X) : Data J α ht p := Classical.choice (data_nonempty J α hs ht p)

theorem finite_data_partition [T2Space X] [CompactSpace X]
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J) :
    ∃ A : ManifoldLocalization.FiniteCharts X,
      ∀ p : A.centers, tsupport (A.partition p) ⊆ (data J α hs ht p.val).toData.source := by
  classical
  obtain ⟨s,hscover⟩ := isCompact_univ.elim_finite_subcover
    (fun p : X => (data J α hs ht p).toData.source)
    (fun p => (data J α hs ht p).toData.source_open)
    (fun p _ => mem_iUnion_of_mem p (data J α hs ht p).toData.mem_source)
  have hc : (univ : Set X) ⊆ ⋃ p : s, (data J α hs ht p.val).toData.source := by
    intro x hx
    obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (hscover hx)
    exact mem_iUnion_of_mem ⟨p,hp⟩ hxp
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate Model isClosed_univ
    (fun p : s => (data J α hs ht p.val).toData.source)
    (fun p => (data J α hs ht p.val).toData.source_open) hc
  refine ⟨⟨s,ρ,fun p => (hρ p).trans (data J α hs ht p.val).toData.source_subset⟩,?_⟩
  exact hρ
end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
