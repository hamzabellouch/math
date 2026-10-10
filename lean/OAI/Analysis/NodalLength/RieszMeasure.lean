import OAI.Analysis.NodalLength.Distributional

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory

namespace SharpNodal.Profiles
open Carleman

def smoothCompactTests : Submodule ℝ C_c(Plane, ℝ) where
  carrier := {f | Smooth (f : Plane → ℝ)}
  zero_mem' := by
    change Smooth (fun _ : Plane => (0:ℝ))
    exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change Smooth (f : Plane → ℝ) at hf
    change Smooth (g : Plane → ℝ) at hg
    change Smooth (fun x => f x+g x)
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change Smooth (f : Plane → ℝ) at hf
    change Smooth (fun x => c*f x)
    exact contDiff_const.mul hf

lemma smoothCompactTests_dominate (f : C_c(Plane,ℝ)) :
    ∃g : smoothCompactTests, 0 ≤ (g.val+f) := by
  obtain ⟨r,hr⟩ := (Metric.isBounded_iff_subset_closedBall (0:Plane)).mp f.hasCompactSupport.isBounded
  let R := max r 1
  have hR : 0<R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let χ : ContDiffBump (0:Plane) := ⟨R,R+1,hR,by linarith⟩
  obtain ⟨M,hM⟩ := f.continuous.norm.bddAbove_range_of_hasCompactSupport f.hasCompactSupport.norm
  let N := max M 0
  let g : C_c(Plane,ℝ) := ⟨⟨fun x => N*χ x,χ.continuous.const_mul N⟩,χ.hasCompactSupport.mul_left⟩
  have hg : g∈smoothCompactTests := contDiff_const.mul χ.contDiff
  refine ⟨⟨g,hg⟩,?_⟩
  intro x
  change 0≤N*χ x+f x
  by_cases hx : x∈tsupport f
  · have hχ : χ x=1 := χ.one_of_mem_closedBall (Metric.closedBall_subset_closedBall (le_max_left r 1) (hr hx))
    have hMb : |f x|≤M := by
      convert! hM (mem_range_self x) using 1
    have hb : |f x|≤N := hMb.trans (le_max_left _ _)
    rw [hχ,mul_one]
    linarith [(abs_le.mp hb).1]
  · rw [image_eq_zero_of_notMem_tsupport hx,add_zero]
    exact mul_nonneg (le_max_right _ _) χ.nonneg

def compactTestsPositiveCone : PointedCone ℝ C_c(Plane,ℝ) where
  carrier := {f | ∀x,0≤f x}
  zero_mem' := by intro x; rfl
  add_mem' := by intro f g hf hg x; exact add_nonneg (hf x) (hg x)
  smul_mem' := by intro c f hf x; exact mul_nonneg c.property (hf x)

theorem positive_smooth_tests_representable (F : smoothCompactTests →ₗ[ℝ] ℝ)
    (hF : ∀f : smoothCompactTests, (∀x,0≤f.val x) → 0≤F f) :
    ∃μ : Measure Plane, IsFiniteMeasureOnCompacts μ ∧
      (∀f : smoothCompactTests,(∫x,f.val x ∂μ)=F f) ∧
      ∀(K : Set Plane),IsCompact K → ∀f : smoothCompactTests,
        (∀x,0≤f.val x) → (∀x∈K,f.val x=1) → μ K≤ENNReal.ofReal (F f) := by
  let p : C_c(Plane,ℝ) →ₗ.[ℝ] ℝ := ⟨smoothCompactTests,F⟩
  obtain ⟨g,hg,hgpos⟩ := riesz_extension compactTestsPositiveCone p
    (fun f hf => hF f hf) (fun f => smoothCompactTests_dominate f)
  let G : C_c(Plane,ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ g (fun f hf => hgpos f hf)
  refine ⟨RealRMK.rieszMeasure G,inferInstance,?_,?_⟩
  · intro f
    rw [RealRMK.integral_rieszMeasure]
    exact hg f
  · intro K hK f hf hKf
    have hh := RealRMK.rieszMeasure_le_of_eq_one G hf hK hKf
    change RealRMK.rieszMeasure G K≤ENNReal.ofReal (g f.val) at hh
    rw [hg f] at hh
    exact hh

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def localizedLaplacianFunctional {w ζ : Plane → ℝ} (hw : Integrable w)
    (hζ : Smooth ζ) (hcζ : HasCompactSupport ζ) : smoothCompactTests →ₗ[ℝ] ℝ where
  toFun f := ∫x,w x*euclideanLaplacian (fun y => ζ y*f.val y) x
  map_add' := by
    intro f g
    have hf : Smooth (f.val : Plane → ℝ) := f.property
    have hg : Smooth (g.val : Plane → ℝ) := g.property
    change (∫x,w x*euclideanLaplacian (fun y => ζ y*(f.val y+g.val y)) x)=_
    simp_rw [mul_add,laplacian_add (hζ.mul hf) (hζ.mul hg),mul_add]
    exact integral_add (integrable_mul_continuous_compact hw (smooth_laplacian (hζ.mul hf)).continuous (compact_laplacian hcζ.mul_right))
      (integrable_mul_continuous_compact hw (smooth_laplacian (hζ.mul hg)).continuous (compact_laplacian hcζ.mul_right))
  map_smul' := by
    intro c f
    have hf : Smooth (f.val : Plane → ℝ) := f.property
    change (∫x,w x*euclideanLaplacian (fun y => ζ y*(c*f.val y)) x)=c*(∫x,w x*euclideanLaplacian (fun y => ζ y*f.val y) x)
    simp_rw [show (fun y => ζ y*(c*f.val y))=(fun y => c*(ζ y*f.val y)) by funext y; ring,
      laplacian_const_mul (hζ.mul hf) c]
    simp_rw [show ∀x,w x*(c*euclideanLaplacian (fun y => ζ y*f.val y) x)=c*(w x*euclideanLaplacian (fun y => ζ y*f.val y) x) by intro x; ring]
    exact integral_const_mul _ _

theorem localized_laplacian_measure {w ζ : Plane → ℝ} {Ω O : Set Plane}
    (hw : Integrable w) (hζ : Smooth ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ⊆Ω) (hnζ : ∀x,0≤ζ x) (hoζ : ∀x∈O,ζ x=1)
    (hpos : ∀ψ : Plane → ℝ,Smooth ψ → HasCompactSupport ψ → tsupport ψ⊆Ω →
      (∀x,0≤ψ x) → 0≤∫x,w x*euclideanLaplacian ψ x) :
    ∃μ : Measure Plane, IsFiniteMeasureOnCompacts μ ∧
      (∀ψ : Plane → ℝ,Smooth ψ → HasCompactSupport ψ → tsupport ψ⊆O →
        (∫x,ψ x ∂μ)=∫x,w x*euclideanLaplacian ψ x) ∧
      ∀(K : Set Plane),IsCompact K → ∀ψ : Plane → ℝ,Smooth ψ → HasCompactSupport ψ →
        tsupport ψ⊆O → (∀x,0≤ψ x) → (∀x∈K,ψ x=1) →
        μ K≤ENNReal.ofReal (∫x,w x*euclideanLaplacian ψ x) := by
  let F := localizedLaplacianFunctional hw hζ hcζ
  have hF : ∀f : smoothCompactTests,(∀x,0≤f.val x) → 0≤F f := by
    intro f hf
    apply hpos (fun x => ζ x*f.val x) (hζ.mul f.property) hcζ.mul_right
    · exact tsupport_mul_subset_left.trans hsζ
    · exact fun x => mul_nonneg (hnζ x) (hf x)
  obtain ⟨μ,hμ,hrep,hbound⟩ := positive_smooth_tests_representable F hF
  have he (ψ : Plane → ℝ) (hsψ : tsupport ψ⊆O) : (fun x => ζ x*ψ x)=ψ := by
    funext x
    by_cases hx : ψ x=0
    · simp [hx]
    · rw [hoζ x (hsψ (subset_tsupport ψ hx)),one_mul]
  refine ⟨μ,hμ,?_,?_⟩
  · intro ψ hψ hcψ hsψ
    let f : smoothCompactTests := ⟨⟨⟨ψ,hψ.continuous⟩,hcψ⟩,hψ⟩
    have hh := hrep f
    change (∫x,ψ x ∂μ)=∫x,w x*euclideanLaplacian (fun y => ζ y*ψ y) x at hh
    simpa only [he ψ hsψ] using hh
  · intro K hK ψ hψ hcψ hsψ hnψ hoψ
    let f : smoothCompactTests := ⟨⟨⟨ψ,hψ.continuous⟩,hcψ⟩,hψ⟩
    have hh := hbound K hK f hnψ hoψ
    change μ K≤ENNReal.ofReal (∫x,w x*euclideanLaplacian (fun y => ζ y*ψ y) x) at hh
    simpa only [he ψ hsψ] using hh

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma integral_mul_le_norm_bound {w f : Plane → ℝ} (hw : Integrable w)
    {C : ℝ} (hf : ∀x,‖f x‖≤C) :
    (∫x,w x*f x)≤C*(∫x,‖w x‖) := by
  apply (le_abs_self _).trans
  have hh := norm_integral_le_of_norm_le (hw.norm.const_mul C)
    (f:=fun x => w x*f x) (Filter.Eventually.of_forall fun x => by
      rw [norm_mul,mul_comm C]
      exact mul_le_mul_of_nonneg_left (hf x) (norm_nonneg _))
  simpa only [Real.norm_eq_abs,integral_const_mul] using hh

theorem local_positive_measure_uniform : ∃C : ℝ,0≤C ∧ ∀w : Plane → ℝ,
    Integrable w →
    (∀ψ : Plane → ℝ,Smooth ψ → HasCompactSupport ψ → tsupport ψ⊆Metric.ball 0 6 →
      (∀x,0≤ψ x) → 0≤∫x,w x*euclideanLaplacian ψ x) →
    ∃μ : Measure Plane, IsFiniteMeasureOnCompacts μ ∧
      μ (Metric.closedBall (0:Plane) 5)≤ENNReal.ofReal (C*(∫x,‖w x‖)) ∧
      ∀ψ : Plane → ℝ,Smooth ψ → HasCompactSupport ψ → tsupport ψ⊆Metric.ball 0 (11/2) →
        (∫x,ψ x ∂μ)=∫x,w x*euclideanLaplacian ψ x := by
  let ζ : ContDiffBump (0:Plane) := ⟨11/2,23/4,by norm_num,by norm_num⟩
  let χ : ContDiffBump (0:Plane) := ⟨5,21/4,by norm_num,by norm_num⟩
  obtain ⟨M,hM⟩ := (smooth_laplacian χ.contDiff).continuous.norm.bddAbove_range_of_hasCompactSupport
    (compact_laplacian χ.hasCompactSupport).norm
  let C := max M 0
  have hbound (x : Plane) : ‖euclideanLaplacian χ x‖≤C := (hM (mem_range_self x)).trans (le_max_left _ _)
  refine ⟨C,le_max_right _ _,?_⟩
  intro w hw hpos
  have hsζ : tsupport (ζ : Plane → ℝ)⊆Metric.ball 0 6 := by
    rw [ζ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by norm_num : (23:ℝ)/4<6)
  have hsχ : tsupport (χ : Plane → ℝ)⊆Metric.ball 0 (11/2) := by
    rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by norm_num : (21:ℝ)/4<11/2)
  obtain ⟨μ,hμ,hrep,hboundμ⟩ := localized_laplacian_measure hw ζ.contDiff ζ.hasCompactSupport hsζ
    (fun _ => ζ.nonneg) (fun x hx => ζ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)) hpos
  have hh := hboundμ (Metric.closedBall 0 5) (isCompact_closedBall _ _) χ χ.contDiff χ.hasCompactSupport hsχ
    (fun _ => χ.nonneg) (fun x hx => χ.one_of_mem_closedBall hx)
  refine ⟨μ,hμ,hh.trans (ENNReal.ofReal_le_ofReal (integral_mul_le_norm_bound hw hbound)),hrep⟩

theorem profile_riesz_uniform : ∃C : ℝ,0≤C ∧ ∀V : Plane → EReal,
    UpperSemicontinuousOn V (Metric.ball 0 1000) →
    (∀x∈Metric.ball (0:Plane) 1000,V x≤0) →
    FullTestProperty (Metric.ball 0 1000) V →
    (∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a) →
    ∃μ : Measure Plane, IsFiniteMeasureOnCompacts μ ∧
      μ (Metric.closedBall (0:Plane) 5)≤ENNReal.ofReal C ∧
      ∀ψ : Plane → ℝ,Smooth ψ → HasCompactSupport ψ → tsupport ψ⊆Metric.ball 0 (11/2) →
        (∫x,ψ x ∂μ)=∫x in Metric.ball (0:Plane) 8,(V x).toReal*euclideanLaplacian ψ x := by
  obtain ⟨C,hC,hCprop⟩ := local_positive_measure_uniform
  refine ⟨C*(100*Real.pi),by positivity,?_⟩
  intro V hV hneg htest ⟨a,ha,hanchor⟩
  have hball : Metric.ball (0:Plane) 8⊆Metric.ball (0:Plane) 1000 := Metric.ball_subset_ball (by norm_num)
  have hlin := profile_lintegral_D8 hV hneg htest ha hanchor
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin
  have hi := (profile_integrable_of_lintegral_ne_top measurableSet_ball (hV.mono hball)
    (fun x hx => hneg x (hball hx)) hfin).1
  let w := (Metric.ball (0:Plane) 8).indicator (fun x => (V x).toReal)
  have hw : Integrable w := hi.integrable_indicator measurableSet_ball
  have he (ψ : Plane → ℝ) : (∫x,w x*euclideanLaplacian ψ x)=
      ∫x in Metric.ball (0:Plane) 8,(V x).toReal*euclideanLaplacian ψ x := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈Metric.ball (0:Plane) 8 <;> simp [w,hx]
  have hpos (ψ : Plane → ℝ) (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ)
      (hsψ : tsupport ψ⊆Metric.ball 0 6) (hnψ : ∀x,0≤ψ x) : 0≤∫x,w x*euclideanLaplacian ψ x := by
    rw [he]
    exact profile_distribution_D6 hV hneg htest hball hfin hψ hcψ hsψ hnψ
  obtain ⟨μ,hμ,hmass,hrep⟩ := hCprop w hw hpos
  have hnorm : (∫x,‖w x‖)≤100*Real.pi := by
    have heq : (fun x => ‖w x‖)=(Metric.ball (0:Plane) 8).indicator (fun x => |(V x).toReal|) := by
      funext x
      by_cases hx : x∈Metric.ball (0:Plane) 8 <;> simp [w,hx,Real.norm_eq_abs]
    rw [heq,integral_indicator measurableSet_ball]
    exact profile_norm_integral_le measurableSet_ball (hV.mono hball) (fun x hx => hneg x (hball hx)) (by positivity) hlin
  refine ⟨μ,hμ,hmass.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hnorm hC)),?_⟩
  intro ψ hψ hcψ hsψ
  exact (hrep ψ hψ hcψ hsψ).trans (he ψ)

end SharpNodal.Profiles

end
end
end

end OAI
