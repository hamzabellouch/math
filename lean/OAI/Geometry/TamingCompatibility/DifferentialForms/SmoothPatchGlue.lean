import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.AntiSmoothMultiply

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma smooth_multiply_pair (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ)
    (a b : antiPre A J α hs ht) :
    ⟪smoothL2 A J α hs ht true b.val,smoothL2 A J α hs ht true (antiMultiply A J α hs ht ρ hρ a).val⟫ =
    ⟪smoothL2 A J α hs ht true (antiMultiply A J α hs ht ρ hρ b).val,smoothL2 A J α hs ht true a.val⟫ := by
  rw [(smoothL2 A J α hs ht true).inner_map_map,(smoothL2 A J α hs ht true).inner_map_map,
    preL2_inner,preL2_inner]
  apply integral_congr_ae
  filter_upwards [] with x
  exact (MetricForms.pairing_smul_right _ _ _ _).trans (MetricForms.pairing_smul_left _ _ _ _).symm

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma anti_partition_sum {ι : Type*} [Fintype ι] (ρ : ι → X → ℝ)
    (hρ : ∀ i, ContMDiff Model 𝓘(ℝ,ℝ) ∞ (ρ i)) (h1 : ∀ x, ∑ i, ρ i x = 1)
    (a : antiPre A J α hs ht) : ∑ i, antiMultiply A J α hs ht (ρ i) (hρ i) a = a := by
  have he := map_sum (((smoothForms X 2).subtype).comp (antiPre A J α hs ht).subtype)
    (fun i => antiMultiply A J α hs ht (ρ i) (hρ i) a) Finset.univ
  apply Subtype.ext
  apply Subtype.ext
  refine he.trans ?_
  funext x
  rw [Finset.sum_apply]
  change (∑ i, ρ i x • a.val.val x) = a.val.val x
  rw [← Finset.sum_smul,h1,one_smul]

lemma energy_eq_of_pair_smooth (u v : antiEnergy A J α hs ht)
    (h : ∀ a : antiPre A J α hs ht,
      ⟪energyInclusion A J α hs ht u,smoothL2 A J α hs ht true a.val⟫ =
      ⟪energyInclusion A J α hs ht v,smoothL2 A J α hs ht true a.val⟫) : u = v := by
  have he : (fun z : antiEnergy A J α hs ht =>
      ⟪energyInclusion A J α hs ht u,energyInclusion A J α hs ht z⟫) =
      (fun z : antiEnergy A J α hs ht =>
      ⟪energyInclusion A J α hs ht v,energyInclusion A J α hs ht z⟫) :=
    (antiToEnergy_dense A J α hs ht).equalizer
      (continuous_const.inner (energyInclusion A J α hs ht).continuous)
      (continuous_const.inner (energyInclusion A J α hs ht).continuous) (funext h)
  apply energyInclusion_injective A J α hs ht
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  have hh := congrFun he (u-v)
  rw [map_sub] at hh
  rw [inner_sub_left,hh,sub_self]

lemma glue_weak_patches {ι : Type*} [Fintype ι] (ρ : ι → X → ℝ)
    (hρ : ∀ i, ContMDiff Model 𝓘(ℝ,ℝ) ∞ (ρ i)) (h1 : ∀ x, ∑ i, ρ i x = 1)
    (u : antiEnergy A J α hs ht) (w : ι → antiPre A J α hs ht)
    (hw : ∀ i a, ⟪energyInclusion A J α hs ht u,
        smoothL2 A J α hs ht true (antiMultiply A J α hs ht (ρ i) (hρ i) a).val⟫ =
      ⟪smoothL2 A J α hs ht true (w i).val,
        smoothL2 A J α hs ht true (antiMultiply A J α hs ht (ρ i) (hρ i) a).val⟫) :
    ∃ b : antiPre A J α hs ht, antiToEnergy A J α hs ht b = u := by
  classical
  let b := ∑ i, antiMultiply A J α hs ht (ρ i) (hρ i) (w i)
  refine ⟨b,(energy_eq_of_pair_smooth A J α hs ht u (antiToEnergy A J α hs ht b) ?_).symm⟩
  intro a
  have ha := congrArg (fun c : antiPre A J α hs ht => smoothL2 A J α hs ht true c.val)
    (anti_partition_sum A J α hs ht ρ hρ h1 a)
  have hsum (t : ι → antiPre A J α hs ht) :
      smoothL2 A J α hs ht true (∑ i, t i).val = ∑ i, smoothL2 A J α hs ht true (t i).val := by
    exact map_sum ((smoothL2 A J α hs ht true).toLinearMap.comp (antiPre A J α hs ht).subtype) t Finset.univ
  rw [hsum] at ha
  change ⟪energyInclusion A J α hs ht u,smoothL2 A J α hs ht true a.val⟫ =
    ⟪smoothL2 A J α hs ht true b.val,smoothL2 A J α hs ht true a.val⟫
  rw [← ha,inner_sum]
  conv_rhs => rw [show b = ∑ i, antiMultiply A J α hs ht (ρ i) (hρ i) (w i) from rfl,hsum,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [hw,smooth_multiply_pair,ha]

end TamingCompatibility.GeometricHilbert

end

end OAI
