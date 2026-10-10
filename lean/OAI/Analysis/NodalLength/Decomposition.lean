import OAI.Analysis.NodalLength.Parametrix

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
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory

namespace SharpNodal.Profiles
open Carleman

lemma indicator_mul_laplacian {w ψ : Plane → ℝ} {Ω : Set Plane}
    (hsψ : tsupport ψ⊆Ω) : (fun x => Ω.indicator w x*euclideanLaplacian ψ x)=
      (fun x => w x*euclideanLaplacian ψ x) := by
  funext x
  by_cases hx : x∈Ω
  · rw [indicator_of_mem hx]
  · have hz : euclideanLaplacian ψ x=0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hx (hsψ (laplacian_tsupport_subset ψ ht)))
    simp only [hz,mul_zero]

lemma integrable_aeLogPotential_mul_compact (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) {ψ : Plane → ℝ} (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun x => aeLogPotential ν x*ψ x) := by
  obtain ⟨R,hR⟩ := hcψ.isBounded.subset_ball (0:Plane)
  have hi := (aeLogPotential_integrableOn ν hs R).integrable_indicator measurableSet_ball
  apply (integrable_mul_continuous_compact hi hψ hcψ).congr
  filter_upwards [] with x
  by_cases hx : x∈Metric.ball (0:Plane) R
  · rw [indicator_of_mem hx]
  · rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hR ht)),mul_zero,mul_zero]

lemma potential_difference_integrable {w : Plane → ℝ} (hw : Integrable w)
    (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ} (hs : ∀ᵐz ∂ν,‖z‖<S) :
    Integrable ((Metric.ball (0:Plane) 4).indicator (fun x => w x-aeLogPotential ν x)) :=
  (hw.integrableOn.sub (aeLogPotential_integrableOn ν hs 4)).integrable_indicator measurableSet_ball

lemma potential_difference_weakHarmonic {w : Plane → ℝ} (hw : Integrable w)
    (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ} (hs : ∀ᵐz ∂ν,‖z‖<S)
    (hrep : ∀ψ : Plane → ℝ,Smooth ψ → HasCompactSupport ψ → tsupport ψ⊆Metric.ball (0:Plane) 4 →
      (∫x,w x*euclideanLaplacian ψ x)=2*Real.pi*(∫x,ψ x ∂ν)) :
    WeakHarmonicOn ((Metric.ball (0:Plane) 4).indicator (fun x => w x-aeLogPotential ν x)) (Metric.ball (0:Plane) 4) := by
  intro ψ hψ hcψ hsψ
  rw [indicator_mul_laplacian hsψ]
  have he : (fun x => (w x-aeLogPotential ν x)*euclideanLaplacian ψ x)=
      (fun x => w x*euclideanLaplacian ψ x-aeLogPotential ν x*euclideanLaplacian ψ x) := by funext x; ring
  rw [he,integral_sub (integrable_mul_continuous_compact hw (smooth_laplacian hψ).continuous (compact_laplacian hcψ))
    (integrable_aeLogPotential_mul_compact ν hs (smooth_laplacian hψ).continuous (compact_laplacian hcψ)),
    hrep ψ hψ hcψ hsψ,aeLogPotential_distribution ν hs hψ hcψ,sub_self]

lemma potential_difference_norm_bound {w : Plane → ℝ} (hw : Integrable w)
    (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ} (hs : ∀ᵐz ∂ν,‖z‖<S) :
    (∫x,‖(Metric.ball (0:Plane) 4).indicator (fun x => w x-aeLogPotential ν x) x‖) ≤
      (∫x,‖w x‖)+ν.real univ*(∫x in Metric.ball (0:Plane) (4+S),‖Real.log ‖x‖‖) := by
  have he : (fun x => ‖(Metric.ball (0:Plane) 4).indicator (fun x => w x-aeLogPotential ν x) x‖)=
      (Metric.ball (0:Plane) 4).indicator (fun x => ‖w x-aeLogPotential ν x‖) := by
    funext x; by_cases hx : x∈Metric.ball (0:Plane) 4 <;> simp [hx]
  rw [he,integral_indicator measurableSet_ball]
  calc
    _ ≤ ∫x in Metric.ball (0:Plane) 4,‖w x‖+‖aeLogPotential ν x‖ := integral_mono
      (hw.integrableOn.sub (aeLogPotential_integrableOn ν hs 4)).norm
      (hw.norm.integrableOn.add (aeLogPotential_integrableOn ν hs 4).norm) (fun x => norm_sub_le _ _)
    _ = (∫x in Metric.ball (0:Plane) 4,‖w x‖)+(∫x in Metric.ball (0:Plane) 4,‖aeLogPotential ν x‖) :=
      integral_add hw.norm.integrableOn (aeLogPotential_integrableOn ν hs 4).norm
    _ ≤ _ := add_le_add (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall (fun x => norm_nonneg _)) hw.norm)
      (aeLogPotential_norm_bound ν hs 4)

lemma ae_potential_decomposition {w : Plane → ℝ} (hw : Integrable w)
    (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ} (hs : ∀ᵐz ∂ν,‖z‖<S)
    (hrep : ∀ψ : Plane → ℝ,Smooth ψ → HasCompactSupport ψ → tsupport ψ⊆Metric.ball (0:Plane) 4 →
      (∫x,w x*euclideanLaplacian ψ x)=2*Real.pi*(∫x,ψ x ∂ν)) :
    ∃h : Plane → ℝ,Smooth h ∧ (∀x∈Metric.ball (0:Plane) 3,euclideanLaplacian h x=0) ∧
      (∀ᵐx : Plane,x∈Metric.ball (0:Plane) 3 → w x=h x+aeLogPotential ν x) := by
  let d := (Metric.ball (0:Plane) 4).indicator (fun x => w x-aeLogPotential ν x)
  have hd : Integrable d := potential_difference_integrable hw ν hs
  have hweak : WeakHarmonicOn d (Metric.ball (0:Plane) 4) := potential_difference_weakHarmonic hw ν hs hrep
  refine ⟨weylRepresentative d,smooth_weylRepresentative hd,weylRepresentative_harmonic hd hweak,?_⟩
  filter_upwards [weylRepresentative_ae hd hweak] with x hx hm
  have hdisk : x∈Metric.ball (0:Plane) 4 := Metric.ball_subset_ball (by norm_num : (3:ℝ)≤4) hm
  have he := hx hm
  change (Metric.ball (0:Plane) 4).indicator (fun x => w x-aeLogPotential ν x) x=weylRepresentative d x at he
  rw [indicator_of_mem hdisk] at he
  linarith

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def normalizedRiesz (μ : Measure Plane) : Measure Plane :=
  ENNReal.ofReal ((2*Real.pi)⁻¹) • μ.restrict (Metric.ball (0:Plane) 4)

lemma normalizedRiesz_finite {μ : Measure Plane} {C : ℝ}
    (hmass : μ (Metric.closedBall (0:Plane) 5)≤ENNReal.ofReal C) :
    IsFiniteMeasure (normalizedRiesz μ) := by
  have hball : μ (Metric.ball (0:Plane) 4)≠(⊤:ℝ≥0∞) := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((measure_mono ((Metric.ball_subset_ball (by norm_num : (4:ℝ)≤5)).trans Metric.ball_subset_closedBall)).trans hmass)
  refine ⟨?_⟩
  simp only [normalizedRiesz,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  change ENNReal.ofReal ((2*Real.pi)⁻¹)*μ (Metric.ball (0:Plane) 4)<⊤
  exact (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hball).lt_top

lemma normalizedRiesz_support (μ : Measure Plane) : ∀ᵐz ∂normalizedRiesz μ,‖z‖<4 := by
  apply Measure.ae_smul_measure
  filter_upwards [self_mem_ae_restrict measurableSet_ball] with z hz
  simpa only [Metric.mem_ball,dist_zero_right] using hz

lemma normalizedRiesz_mass {μ : Measure Plane} {C : ℝ} (hC : 0≤C)
    (hmass : μ (Metric.closedBall (0:Plane) 5)≤ENNReal.ofReal C) :
    (normalizedRiesz μ).real univ≤(2*Real.pi)⁻¹*C := by
  apply le_trans (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (show (normalizedRiesz μ) univ≤ENNReal.ofReal ((2*Real.pi)⁻¹)*ENNReal.ofReal C from ?_))
  · simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0≤(2*Real.pi)⁻¹),ENNReal.toReal_ofReal hC]
    exact le_rfl
  · simp only [normalizedRiesz,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
    exact mul_le_mul' le_rfl ((measure_mono ((Metric.ball_subset_ball (by norm_num : (4:ℝ)≤5)).trans Metric.ball_subset_closedBall)).trans hmass)

lemma normalizedRiesz_test (μ : Measure Plane) {ψ : Plane → ℝ}
    (hsψ : tsupport ψ⊆Metric.ball (0:Plane) 4) :
    2*Real.pi*(∫x,ψ x ∂normalizedRiesz μ)=∫x,ψ x ∂μ := by
  have he : (Metric.ball (0:Plane) 4).indicator ψ=ψ := by
    funext x
    by_cases hx : x∈Metric.ball (0:Plane) 4
    · exact indicator_of_mem hx ψ
    · rw [indicator_of_notMem hx ψ,image_eq_zero_of_notMem_tsupport (fun ht => hx (hsψ ht))]
  rw [normalizedRiesz,integral_smul_measure,ENNReal.toReal_ofReal (by positivity : 0≤(2*Real.pi)⁻¹)]
  change 2*Real.pi*((2*Real.pi)⁻¹*(∫x in Metric.ball (0:Plane) 4,ψ x ∂μ))=_
  rw [← integral_indicator measurableSet_ball,he]
  field_simp

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

theorem profile_ae_decomposition_uniform : ∃C : ℝ,0≤C ∧ ∀V : Plane → EReal,
    UpperSemicontinuousOn V (Metric.ball 0 1000) →
    (∀x∈Metric.ball (0:Plane) 1000,V x≤0) →
    FullTestProperty (Metric.ball 0 1000) V →
    (∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a) →
    ∃ν : Measure Plane, IsFiniteMeasure ν ∧ (∀ᵐz ∂ν,‖z‖<4) ∧ ν.real univ≤C ∧
    ∃h : Plane → ℝ,Smooth h ∧ (∀x∈Metric.ball (0:Plane) 3,euclideanLaplacian h x=0) ∧
      (∀ᵐx : Plane,x∈Metric.ball (0:Plane) 3 → (V x).toReal=h x+aeLogPotential ν x) ∧
      (∀x : Plane,(∀i : Fin 2,|coordPartial h i x|≤C) ∧
        (∀i j : Fin 2,|coordPartial (coordPartial h i) j x|≤C)) := by
  obtain ⟨Cμ,hCμ,hμprop⟩ := profile_riesz_uniform
  obtain ⟨Ch,hCh,hderiv⟩ := uniform_weyl_derivative_bounds
  let L := ∫x in Metric.ball (0:Plane) 8,‖Real.log ‖x‖‖
  have hL : 0≤L := integral_nonneg (fun x => norm_nonneg _)
  let N := (2*Real.pi)⁻¹*Cμ
  have hN : 0≤N := by dsimp [N]; positivity
  let C := N+Ch*(100*Real.pi+N*L)
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro V hV hneg htest hanchor
  obtain ⟨μ,_hμ,hmass,hrep⟩ := hμprop V hV hneg htest hanchor
  let ν := normalizedRiesz μ
  have hν : IsFiniteMeasure ν := normalizedRiesz_finite hmass
  let := hν
  have hs : ∀ᵐz ∂ν,‖z‖<4 := normalizedRiesz_support μ
  have hνmass : ν.real univ≤N := normalizedRiesz_mass hCμ hmass
  obtain ⟨a,ha,hanchor⟩ := hanchor
  have hball : Metric.ball (0:Plane) 8⊆Metric.ball (0:Plane) 1000 := Metric.ball_subset_ball (by norm_num)
  have hlin := profile_lintegral_D8 hV hneg htest ha hanchor
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin
  have hi := (profile_integrable_of_lintegral_ne_top measurableSet_ball (hV.mono hball)
    (fun x hx => hneg x (hball hx)) hfin).1
  let w := (Metric.ball (0:Plane) 8).indicator (fun x => (V x).toReal)
  have hw : Integrable w := hi.integrable_indicator measurableSet_ball
  have hnorm : (∫x,‖w x‖)≤100*Real.pi := by
    have heq : (fun x => ‖w x‖)=(Metric.ball (0:Plane) 8).indicator (fun x => |(V x).toReal|) := by
      funext x
      by_cases hx : x∈Metric.ball (0:Plane) 8 <;> simp [w,hx,Real.norm_eq_abs]
    rw [heq,integral_indicator measurableSet_ball]
    exact profile_norm_integral_le measurableSet_ball (hV.mono hball) (fun x hx => hneg x (hball hx)) (by positivity) hlin
  have hwrep (ψ : Plane → ℝ) (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ)
      (hsψ : tsupport ψ⊆Metric.ball (0:Plane) 4) :
      (∫x,w x*euclideanLaplacian ψ x)=2*Real.pi*(∫x,ψ x ∂ν) := by
    rw [normalizedRiesz_test μ hsψ]
    rw [hrep ψ hψ hcψ (hsψ.trans (Metric.ball_subset_ball (by norm_num : (4:ℝ)≤11/2)))]
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈Metric.ball (0:Plane) 8 <;> simp [w,hx]
  let d := (Metric.ball (0:Plane) 4).indicator (fun x => w x-aeLogPotential ν x)
  have hd : Integrable d := potential_difference_integrable hw ν hs
  have hweak : WeakHarmonicOn d (Metric.ball (0:Plane) 4) := potential_difference_weakHarmonic hw ν hs hwrep
  have hdN : (∫x,‖d x‖)≤100*Real.pi+N*L := by
    exact (potential_difference_norm_bound hw ν hs).trans
      (add_le_add hnorm (by simpa only [show (4+4:ℝ)=8 by norm_num] using (mul_le_mul_of_nonneg_right hνmass hL)))
  refine ⟨ν,hν,hs,hνmass.trans (le_add_of_nonneg_right (by positivity)),
    weylRepresentative d,smooth_weylRepresentative hd,weylRepresentative_harmonic hd hweak,?_,?_⟩
  · filter_upwards [weylRepresentative_ae hd hweak] with x hx hm
    have h4 : x∈Metric.ball (0:Plane) 4 := Metric.ball_subset_ball (by norm_num : (3:ℝ)≤4) hm
    have h8 : x∈Metric.ball (0:Plane) 8 := Metric.ball_subset_ball (by norm_num : (3:ℝ)≤8) hm
    have he := hx hm
    change (Metric.ball (0:Plane) 4).indicator (fun x => w x-aeLogPotential ν x) x=weylRepresentative d x at he
    rw [indicator_of_mem h4] at he
    have hwx : w x=(V x).toReal := indicator_of_mem h8 _
    rw [hwx] at he
    linarith
  · intro x
    have hb : Ch*(∫y,‖d y‖)≤C := (mul_le_mul_of_nonneg_left hdN hCh).trans (le_add_of_nonneg_left hN)
    exact ⟨fun i => ((hderiv d hd x).1 i).trans hb,fun i j => ((hderiv d hd x).2 i j).trans hb⟩

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma profile_le_continuous_of_ae {Ω U : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (htest : FullTestProperty Ω V) (hU : IsOpen U) (hUΩ : U⊆Ω)
    {g : Plane → ℝ} (hg : Continuous g)
    (hae : ∀ᵐx ∂volume.restrict U,V x≤(g x:EReal)) : ∀x∈U,V x≤(g x:EReal) := by
  intro x hx
  by_contra hh
  obtain ⟨c,hgc,hcV⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hh)
  have hgc' : g x<c := EReal.coe_lt_coe_iff.mp hgc
  have hne : 0≤ -V x := by simpa using EReal.neg_le_neg_iff.mpr (hneg x (hUΩ hx))
  have hnhds : U∩{y | g y<c}∈𝓝 x := (hU.inter (isOpen_lt hg continuous_const)).mem_nhds ⟨hx,hgc'⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hbU : Metric.ball x r⊆U := fun y hy => (hball hy).1
  have hlower : ENNReal.ofReal (Real.pi*r^2)*ENNReal.ofReal (-c)≤
      ∫⁻y in Metric.ball x r,(-V y).toENNReal := by
    have hb : ∀ᵐy ∂volume.restrict (Metric.ball x r),ENNReal.ofReal (-c)≤(-V y).toENNReal := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hbU hae,self_mem_ae_restrict measurableSet_ball] with y hy hym
      have hle : V y≤(c:EReal) := hy.trans (EReal.coe_le_coe_iff.mpr (hball hym).2.le)
      simpa only [← EReal.coe_neg,EReal.real_coe_toENNReal] using
        EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr hle)
    have hi := lintegral_mono_ae hb
    simpa only [lintegral_const,Measure.restrict_apply_univ,EuclideanSpace.volume_ball_fin_two,
      ENNReal.ofReal_mul (by positivity : 0≤Real.pi),ENNReal.ofReal_pow hr.le,mul_comm] using hi
  have hu := disk_submean hV hneg htest hr (hbU.trans hUΩ)
  have hl : (-V x).toENNReal<ENNReal.ofReal (-c) := by
    simpa only [← EReal.coe_neg,EReal.real_coe_toENNReal] using
      EReal.toENNReal_lt_toENNReal hne (EReal.neg_lt_neg_iff.mpr hcV)
  apply (not_le_of_gt (ENNReal.mul_lt_mul_left (by positivity : ENNReal.ofReal (Real.pi*r^2)≠0)
    ENNReal.ofReal_ne_top hl))
  simpa only [mul_comm] using (hlower.trans hu)

lemma profile_le_continuous_of_toReal_ae {Ω U : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (htest : FullTestProperty Ω V) (hU : IsOpen U) (hUΩ : U⊆Ω)
    {g : Plane → ℝ} (hg : Continuous g)
    (hae : ∀ᵐx ∂volume.restrict U,(V x).toReal≤g x) : ∀x∈U,V x≤(g x:EReal) := by
  apply profile_le_continuous_of_ae hV hneg htest hU hUΩ hg
  filter_upwards [hae,self_mem_ae_restrict hU.measurableSet] with x hx hmem
  by_cases hb : V x=⊥
  · simp [hb]
  · have ht : V x≠⊤ := ne_top_of_le_ne_top (by simp) (hneg x (hUΩ hmem))
    rw [← EReal.coe_toReal ht hb]
    exact EReal.coe_le_coe_iff.mpr hx

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma plane_basis_expansion (v : Plane) :
    v=(v 0) • EuclideanSpace.single 0 1+(v 1) • EuclideanSpace.single 1 1 := by
  ext i
  fin_cases i <;> simp

lemma plane_component_norm_le (v : Plane) (i : Fin 2) : |v i|≤‖v‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i

lemma plane_clm_norm_le_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : Plane →L[ℝ] F) {C : ℝ} (hC : 0≤C)
    (hA : ∀i : Fin 2,‖A (EuclideanSpace.single i 1)‖≤C) : ‖A‖≤2*C := by
  apply A.opNorm_le_bound (by positivity)
  intro v
  conv_lhs => rw [plane_basis_expansion v]
  rw [map_add,map_smul,map_smul]
  calc
    _ ≤ ‖(v 0) • A (EuclideanSpace.single 0 1)‖+‖(v 1) • A (EuclideanSpace.single 1 1)‖ := norm_add_le _ _
    _ = |v 0| *‖A (EuclideanSpace.single 0 1)‖+|v 1| *‖A (EuclideanSpace.single 1 1)‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ ‖v‖*C+‖v‖*C := add_le_add
      (mul_le_mul (plane_component_norm_le v 0) (hA 0) (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul (plane_component_norm_le v 1) (hA 1) (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

lemma fderiv_norm_le_two {f : Plane → ℝ} {C : ℝ} (hC : 0≤C) (x : Plane)
    (h : ∀i : Fin 2,|coordPartial f i x|≤C) : ‖fderiv ℝ f x‖≤2*C :=
  plane_clm_norm_le_two _ hC (fun i => by simpa only [coordPartial,Real.norm_eq_abs] using h i)

lemma fderiv_sub_norm_le_two {f : Plane → ℝ} {C : ℝ} (hC : 0≤C) (x y : Plane)
    (h : ∀i : Fin 2,|coordPartial f i x-coordPartial f i y|≤C) :
    ‖fderiv ℝ f x-fderiv ℝ f y‖≤2*C :=
  plane_clm_norm_le_two _ hC (fun i => by simpa only [sub_apply,coordPartial,Real.norm_eq_abs] using h i)

lemma affine_error_bound_ball {f : Plane → ℝ} (hf : Smooth f) {y x : Plane} {r C : ℝ}
    (hr : 0≤r) (hC : 0≤C)
    (hess : ∀z∈Metric.closedBall y r,∀i j : Fin 2,|coordPartial (coordPartial f i) j z|≤C)
    (hx : x∈Metric.closedBall y r) :
    |f x-f y-(fderiv ℝ f y) (x-y)|≤4*C*r^2 := by
  have hy : y∈Metric.closedBall y r := Metric.mem_closedBall_self hr
  have hp (i : Fin 2) (z : Plane) (hz : z∈Metric.closedBall y r) :
      |coordPartial f i z-coordPartial f i y|≤2*C*r := by
    have hh := (convex_closedBall y r).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (smooth_partial hf i).differentiable (by simp) z)
      (fun z hz => fderiv_norm_le_two hC z (hess z hz i)) hy hz
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz) (by positivity))
  have hder (z : Plane) (hz : z∈Metric.closedBall y r) :
      ‖fderiv ℝ f z-fderiv ℝ f y‖≤4*C*r := by
    have ht := fderiv_sub_norm_le_two (by positivity : 0≤2*C*r) z y (fun i => hp i z hz)
    convert ht using 1; ring
  have ht := (convex_closedBall y r).norm_image_sub_le_of_norm_fderiv_le'
    (fun z _ => hf.differentiable (by simp) z) hder hy hx
  rw [Real.norm_eq_abs] at ht
  exact ht.trans (by
    have hxr : ‖x-y‖≤r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
    nlinarith [mul_le_mul_of_nonneg_left hxr (show 0≤4*C*r by positivity)])

end SharpNodal.Profiles

end
end
end
end
end

end OAI
