import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeResolventDifferential
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSmoothPatch

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open scoped SchwartzMap
lemma real_full_decompose {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (q : 𝓢(E,R n)) :
    (q : E → R n) = ∑ j, (componentTest j (realComponent q j) : E → R n) := by
  classical
  ext x k
  simp [componentTest_apply,EuclideanSpace.single,Pi.single_apply]
end TamingCompatibility.ComplexMatrix
namespace TamingCompatibility.ManifoldForms
open scoped Manifold
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] {k : ℕ}
lemma chartLift_finset_sum {ι : Type*} (p : X) (s : Finset ι)
    (a : ι → Space → Space [⋀^Fin k]→L[ℝ] ℝ) :
    chartLift p (∑ i ∈ s, a i) = ∑ i ∈ s, chartLift p (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    funext x
    simp only [chartLift]
    split_ifs <;> rfl
  | @insert i s hi ih => rw [Finset.sum_insert hi,Finset.sum_insert hi,chartLift_add,ih]
end TamingCompatibility.ManifoldForms
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X)
  (D : GeometricChart.Data J α ht p)
lemma manifoldTest_sum {ι : Type*} (s : Finset ι) (q : ι → Space → HodgeNormalSymbol.W) :
    manifoldTest J α ht p D (∑ i ∈ s, q i) = ∑ i ∈ s, manifoldTest J α ht p D (q i) := by
  classical
  have he : coordinateTest J α ht p D (∑ i ∈ s, q i) = ∑ i ∈ s, coordinateTest J α ht p D (q i) := by
    funext z
    simp only [coordinateTest,Finset.sum_apply,map_sum]
  unfold manifoldTest
  rw [he,chartLift_finset_sum]

end TamingCompatibility.HodgeChart
namespace TamingCompatibility.GeometricHilbert

section LocalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set ComplexMatrix
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
lemma hodge_pair_all_tests_eq (p : A.centers) {U : Set Space} (hUD : U ⊆ (D p).domain)
    (u v : L2 A J α hs ht true)
    (h : ∀ (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ))
      (hφU : tsupport φ ⊆ U) (j : Fin 6),
      ⟪u,smoothL2 A J α hs ht true
        (hodgeTest A J α hs ht D p (componentTest j φ) (full_componentTest_compact j φ hc)
          ((full_componentTest_support j φ).trans (hφU.trans hUD)))⟫ =
      ⟪v,smoothL2 A J α hs ht true
        (hodgeTest A J α hs ht D p (componentTest j φ) (full_componentTest_compact j φ hc)
          ((full_componentTest_support j φ).trans (hφU.trans hUD)))⟫)
    (q : 𝓢(Space,HodgeNormalSymbol.W)) (hc : HasCompactSupport (q : Space → HodgeNormalSymbol.W))
    (hqU : tsupport q ⊆ U) :
    ⟪u,smoothL2 A J α hs ht true (hodgeTest A J α hs ht D p q hc (hqU.trans hUD))⟫ =
    ⟪v,smoothL2 A J α hs ht true (hodgeTest A J α hs ht D p q hc (hqU.trans hUD))⟫ := by
  classical
  let φ (j : Fin 6) := realComponent q j
  have hφc (j : Fin 6) : HasCompactSupport (φ j : Space → ℝ) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (realComponent_support q j)
  have hφU (j : Fin 6) : tsupport (φ j) ⊆ U := (realComponent_support q j).trans hqU
  let w (j : Fin 6) := hodgeTest A J α hs ht D p (componentTest j (φ j))
    (full_componentTest_compact j (φ j) (hφc j)) ((full_componentTest_support j (φ j)).trans ((hφU j).trans hUD))
  have he : hodgeTest A J α hs ht D p q hc (hqU.trans hUD) = ∑ j, w j := by
    apply Subtype.ext
    change manifoldTest J α ht p.val (D p).toData q = (∑ j, w j).val
    rw [show (∑ j, w j).val = ∑ j, (w j).val from
      map_sum (smoothForms X 2).subtype w Finset.univ]
    change manifoldTest J α ht p.val (D p).toData q =
      ∑ j, manifoldTest J α ht p.val (D p).toData (componentTest j (φ j))
    rw [← manifoldTest_sum]
    exact congrArg (manifoldTest J α ht p.val (D p).toData) (real_full_decompose q)
  rw [he,map_sum,inner_sum,inner_sum]
  exact Finset.sum_congr rfl (fun j _ => h (φ j) (hφc j) (hφU j) j)
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open HilbertSobolev
variable (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include D hD in
lemma hodge_exists_weak_patch (r : ℝ) (hr : 0 < r) (j : ℕ)
    (f : PreL2 A J α hs ht true) (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ w : PreL2 A J α hs ht true,
      ∀ (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ), tsupport ρ ⊆ V →
        ∀ a : PreL2 A J α hs ht true,
          ⟪hodgeInclusion A J α hs ht ((hodgeGraphResolvent A J α hs ht r hr ^ j)
            (hodgeSmooth A J α hs ht f)),smoothL2 A J α hs ht true (hodgeMultiply A J α hs ht ρ hρ a)⟫ =
          ⟪smoothL2 A J α hs ht true w,smoothL2 A J α hs ht true (hodgeMultiply A J α hs ht ρ hρ a)⟫ := by
  obtain ⟨p,hp,hxp⟩ := exists_nonzero_weight_chart A J α ht (fun p => (D p).toData) hD x
  have hxs : x ∈ (extChartAt Model p.val).source := (A.subordinate p) (subset_closure hp)
  have hw : coordinateWeight A p (extChartAt Model p.val x) ≠ 0 := by
    simpa only [coordinateWeight,(extChartAt Model p.val).left_inv hxs] using hp
  obtain ⟨τ,-,-,U,hU,hxU,hUD,hτ⟩ := SchwartzCutoff.exists_reciprocal
    (D p).domain_open ((coordinateWeight_smooth A p).mono (D p).domain_subset) hxp hw
  obtain ⟨V,hV,hxV,hVU,g,hgs,hgd⟩ := hodgeGraphResolvent_local_smooth A J α hs ht D hD p τ
    hU hUD hτ (extChartAt Model p.val x) hxU r hr j f
  obtain ⟨W,hW,hxW,hWV,w,hw⟩ := hodge_exists_patch A J α hs ht D p hV (hVU.trans hUD) hxV g hgs
  let Z := (extChartAt Model p.val).source ∩ (extChartAt Model p.val) ⁻¹' W
  have hZ : IsOpen Z := (continuousOn_extChartAt p.val).isOpen_inter_preimage (isOpen_extChartAt_source p.val) hW
  refine ⟨Z,hZ,⟨hxs,hxW⟩,w,fun ρ hρ hρZ a => ?_⟩
  obtain ⟨q,hqc,hqW,hq⟩ := hodge_supported_test A J α hs ht D p hW
    (hWV.trans (hVU.trans hUD)) ρ hρ hρZ a
  rw [← hq]
  refine hodge_pair_all_tests_eq A J α hs ht D p (hWV.trans (hVU.trans hUD)) _ _ ?_ q hqc hqW
  intro φ hc hφW k
  exact hodge_local_pairing_eq A J α hs ht D hD p τ hW (hWV.trans (hVU.trans hUD))
    (fun z hz => hτ z (hVU (hWV hz))) _ g
    (fun χ hc hχ => tests_eq_of_localize hV hgd χ hc (hχ.trans hWV)) w hw φ hc hφW k
end LocalCharts

open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
lemma hodge_smooth_multiply_pair (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ)
    (a b : PreL2 A J α hs ht true) :
    ⟪smoothL2 A J α hs ht true b,smoothL2 A J α hs ht true (hodgeMultiply A J α hs ht ρ hρ a)⟫ =
    ⟪smoothL2 A J α hs ht true (hodgeMultiply A J α hs ht ρ hρ b),smoothL2 A J α hs ht true a⟫ := by
  rw [(smoothL2 A J α hs ht true).inner_map_map,(smoothL2 A J α hs ht true).inner_map_map,
    preL2_inner,preL2_inner]
  apply integral_congr_ae
  filter_upwards [] with x
  exact (MetricForms.pairing_smul_right _ _ _ _).trans (MetricForms.pairing_smul_left _ _ _ _).symm
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma hodge_partition_sum {ι : Type*} [Fintype ι] (ρ : ι → X → ℝ)
    (hρ : ∀ i, ContMDiff Model 𝓘(ℝ,ℝ) ∞ (ρ i)) (h1 : ∀ x, ∑ i, ρ i x = 1)
    (a : PreL2 A J α hs ht true) : ∑ i, hodgeMultiply A J α hs ht (ρ i) (hρ i) a = a := by
  have he := map_sum (smoothForms X 2).subtype
    (fun i => hodgeMultiply A J α hs ht (ρ i) (hρ i) a) Finset.univ
  apply Subtype.ext
  refine he.trans ?_
  funext x
  rw [Finset.sum_apply]
  change (∑ i, ρ i x • a.val x) = a.val x
  rw [← Finset.sum_smul,h1,one_smul]
lemma hodge_energy_eq_of_pair_smooth (u v : hodgeEnergy A J α hs ht)
    (h : ∀ a : PreL2 A J α hs ht true,
      ⟪hodgeInclusion A J α hs ht u,smoothL2 A J α hs ht true a⟫ =
      ⟪hodgeInclusion A J α hs ht v,smoothL2 A J α hs ht true a⟫) : u = v := by
  have he : (fun z : hodgeEnergy A J α hs ht =>
      ⟪hodgeInclusion A J α hs ht u,hodgeInclusion A J α hs ht z⟫) =
      (fun z : hodgeEnergy A J α hs ht =>
      ⟪hodgeInclusion A J α hs ht v,hodgeInclusion A J α hs ht z⟫) :=
    (hodgeSmooth_dense A J α hs ht).equalizer
      (continuous_const.inner (hodgeInclusion A J α hs ht).continuous)
      (continuous_const.inner (hodgeInclusion A J α hs ht).continuous)
      (funext (fun a => by simpa only [Function.comp_apply,hodgeInclusion_smooth] using h a))
  apply hodgeInclusion_injective A J α hs ht
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  have hh := congrFun he (u-v)
  rw [map_sub] at hh
  rw [inner_sub_left,hh,sub_self]
lemma hodge_glue_weak_patches {ι : Type*} [Fintype ι] (ρ : ι → X → ℝ)
    (hρ : ∀ i, ContMDiff Model 𝓘(ℝ,ℝ) ∞ (ρ i)) (h1 : ∀ x, ∑ i, ρ i x = 1)
    (u : hodgeEnergy A J α hs ht) (w : ι → PreL2 A J α hs ht true)
    (hw : ∀ i a, ⟪hodgeInclusion A J α hs ht u,
        smoothL2 A J α hs ht true (hodgeMultiply A J α hs ht (ρ i) (hρ i) a)⟫ =
      ⟪smoothL2 A J α hs ht true (w i),
        smoothL2 A J α hs ht true (hodgeMultiply A J α hs ht (ρ i) (hρ i) a)⟫) :
    ∃ b : PreL2 A J α hs ht true, hodgeSmooth A J α hs ht b = u := by
  classical
  let b := ∑ i, hodgeMultiply A J α hs ht (ρ i) (hρ i) (w i)
  refine ⟨b,(hodge_energy_eq_of_pair_smooth A J α hs ht u (hodgeSmooth A J α hs ht b) ?_).symm⟩
  intro a
  have ha := congrArg (smoothL2 A J α hs ht true) (hodge_partition_sum A J α hs ht ρ hρ h1 a)
  rw [map_sum] at ha
  rw [hodgeInclusion_smooth]
  rw [← ha,inner_sum]
  conv_rhs => rw [show b = ∑ i, hodgeMultiply A J α hs ht (ρ i) (hρ i) (w i) from rfl,map_sum,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [hw,hodge_smooth_multiply_pair,ha]
end TamingCompatibility.GeometricHilbert

end

end OAI
