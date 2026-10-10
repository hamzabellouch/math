import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.NormalPatch
import OAI.Geometry.TamingCompatibility.Elliptic.OperatorCalculus

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open MeasureTheory MeasureTheory.Measure Set
open scoped ContDiff RealInnerProductSpace
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable (μ : Measure V) [IsAddHaarMeasure μ]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι] in
lemma integrable_inner_compact_left {f g : V → W} (hf : Continuous f) (hg : Continuous g)
    (hc : HasCompactSupport f) : Integrable (fun x => ⟪f x,g x⟫) μ := by
  apply (hf.inner hg).integrable_of_hasCompactSupport
  exact hc.mono (fun x hx => by
    change f x ≠ 0
    intro hz
    exact hx (by simp [hz]))

omit [CompleteSpace W] [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι] in
lemma integral_inner_fderiv {u v : V → W} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hc : HasCompactSupport u) (e : V) :
    (∫ x, ⟪u x,fderiv ℝ v x e⟫ ∂μ) = -(∫ x, ⟪fderiv ℝ u x e,v x⟫ ∂μ) := by
  apply integral_bilinear_fderiv_right_eq_neg_left_of_integrable (B := innerSL ℝ)
  · exact integrable_inner_compact_left μ
      ((hu.continuous_fderiv (by simp)).clm_apply continuous_const) hv.continuous (hc.fderiv_apply ℝ e)
  · exact integrable_inner_compact_left μ hu.continuous
      ((hv.continuous_fderiv (by simp)).clm_apply continuous_const) hc
  · exact integrable_inner_compact_left μ hu.continuous hv.continuous hc
  · exact fun x _ => hu.differentiable (by simp) x
  · exact fun x _ => hv.differentiable (by simp) x

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma weightedAdjoint_pairing (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (ρ : V → ℝ) (u : V → W) (v : V → Q)
    (x : V) (hρ : u x ≠ 0 → ρ x ≠ 0) :
    ρ x * ⟪u x,weightedAdjoint e a b ρ v x⟫ =
      -(∑ i, ⟪u x,fderiv ℝ (fun y => (ρ y • a i y).adjoint (v y)) x (e i)⟫) +
        ρ x * ⟪b x (u x),v x⟫ := by
  by_cases hu : u x = 0
  · simp [hu]
  · have hp := hρ hu
    simp only [weightedAdjoint,inner_add_right,inner_smul_right,inner_sum,
      ContinuousLinearMap.adjoint_inner_right]
    rw [mul_add,← mul_assoc,show ρ x * -(ρ x)⁻¹ = -1 by simp [hp]]
    ring

lemma integral_weightedAdjoint (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (ρ : V → ℝ) (u : V → W) (v : V → Q)
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (hb : ContDiff ℝ ∞ b)
    (hρ : ContDiff ℝ ∞ ρ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hc : HasCompactSupport u) (hρ0 : ∀ x, u x ≠ 0 → ρ x ≠ 0) :
    (∫ x, ρ x * ⟪u x,weightedAdjoint e a b ρ v x⟫ ∂μ) =
      ∫ x, ρ x * ⟪differential e a b u x,v x⟫ ∂μ := by
  classical
  let F : ι → V → W := fun i x => (ρ x • a i x).adjoint (v x)
  let Adj : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hF (i : ι) : ContDiff ℝ ∞ (F i) :=
    (Adj.contDiff.comp (hρ.smul (ha i))).clm_apply hv
  have hi (i : ι) : Integrable (fun x => ⟪u x,fderiv ℝ (F i) x (e i)⟫) μ :=
    integrable_inner_compact_left μ hu.continuous
      (((hF i).continuous_fderiv (by simp)).clm_apply continuous_const) hc
  have hj (i : ι) : Integrable (fun x => ⟪fderiv ℝ u x (e i),F i x⟫) μ :=
    integrable_inner_compact_left μ
      ((hu.continuous_fderiv (by simp)).clm_apply continuous_const) (hF i).continuous (hc.fderiv_apply ℝ (e i))
  have hbu : HasCompactSupport (fun x => ρ x • b x (u x)) := hc.mono (by
    intro x hx
    change u x ≠ 0
    intro hz
    exact hx (by simp [hz]))
  have hbi : Integrable (fun x => ρ x * ⟪b x (u x),v x⟫) μ := by
    have hh := integrable_inner_compact_left μ
      (hρ.continuous.smul (hb.continuous.clm_apply hu.continuous)) hv.continuous hbu
    change Integrable (fun x => ⟪ρ x • b x (u x), v x⟫) μ at hh
    simpa only [inner_smul_left,conj_trivial] using hh
  have he (x : V) : ρ x * ⟪differential e a b u x,v x⟫ =
      (∑ i, ⟪fderiv ℝ u x (e i),F i x⟫) + ρ x * ⟪b x (u x),v x⟫ := by
    simp only [differential,inner_add_left,sum_inner,mul_add,Finset.mul_sum,F,
      ContinuousLinearMap.adjoint_inner_right,_root_.smul_apply,inner_smul_left,conj_trivial]
  simp_rw [weightedAdjoint_pairing e a b ρ u v _ (hρ0 _),he]
  change (∫ x, -(∑ i, ⟪u x,fderiv ℝ (F i) x (e i)⟫) + ρ x * ⟪b x (u x),v x⟫ ∂μ) = _
  have hsumi := integrable_finsetSum Finset.univ (fun i _ => hi i)
  have hsumj := integrable_finsetSum Finset.univ (fun i _ => hj i)
  have hneg : Integrable (fun x => -(∑ i, ⟪u x,fderiv ℝ (F i) x (e i)⟫)) μ := hsumi.neg
  rw [integral_add hneg hbi, integral_neg,integral_finsetSum _ (fun i _ => hi i),
    integral_add hsumj hbi,integral_finsetSum _ (fun i _ => hj i)]
  congr 1
  simp_rw [integral_inner_fderiv μ hu (hF _) hc]
  simp

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [MeasurableSpace V] [BorelSpace V] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι] in
lemma exists_smooth_extension_compact {U K : Set V} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {f : V → W} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : V → W, ContDiff ℝ ∞ g ∧ ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  obtain ⟨O,hO,hKO,hOU,hOc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  have hKi : K ⊆ interior (closure O) := by
    intro x hx
    exact mem_interior_iff_mem_nhds.mpr (mem_of_superset (hO.mem_nhds (hKO hx)) subset_closure)
  obtain ⟨φ,hφone,hφzero,_⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,V)) hK.isClosed hKi (n := ⊤)
  have hφsupp : tsupport (φ : V → ℝ) ⊆ closure O := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hn
    exact hx (hφzero x hn)
  refine ⟨fun x => φ x • f x,SchwartzCutoff.smooth hU hf
    (contMDiff_iff_contDiff.mp φ.contMDiff) (hφsupp.trans hOU),?_⟩
  intro x hx
  filter_upwards [hφone.filter_mono (nhds_le_nhdsSet hx)] with y hy
  simp [hy]

variable (μ : Measure V) [IsAddHaarMeasure μ]
omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι] in
lemma integrable_inner_compact_local {u v : V → W} (hu : Continuous u)
    (hv : ∀ x ∈ tsupport u, ContinuousAt v x) (hc : HasCompactSupport u) :
    Integrable (fun x => ⟪u x,v x⟫) μ := by
  have hcont : Continuous (fun x => ⟪u x,v x⟫) := continuous_iff_continuousAt.mpr (fun x => by
    by_cases hx : x ∈ tsupport u
    · exact hu.continuousAt.inner (hv x hx)
    · apply (continuousAt_const : ContinuousAt (fun _ : V => (0 : ℝ)) x).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hx] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy])
  apply hcont.integrable_of_hasCompactSupport
  exact hc.mono (fun x hx => by
    change u x ≠ 0
    intro hz
    exact hx (by simp [hz]))

omit [CompleteSpace W] [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι] in
lemma integral_inner_fderiv_on {U : Set V} (hU : IsOpen U) {u v : V → W}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiffOn ℝ ∞ v U)
    (hc : HasCompactSupport u) (hsub : tsupport u ⊆ U) (e : V) :
    (∫ x, ⟪u x,fderiv ℝ v x e⟫ ∂μ) = -(∫ x, ⟪fderiv ℝ u x e,v x⟫ ∂μ) := by
  obtain ⟨w,hw,hvw⟩ := exists_smooth_extension_compact hU hc hsub hv
  have hl (x : V) : ⟪u x,fderiv ℝ v x e⟫ = ⟪u x,fderiv ℝ w x e⟫ := by
    by_cases hx : x ∈ tsupport u
    · rw [(hvw x hx).fderiv_eq]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hr (x : V) : ⟪fderiv ℝ u x e,v x⟫ = ⟪fderiv ℝ u x e,w x⟫ := by
    by_cases hx : x ∈ tsupport u
    · rw [(hvw x hx).eq_of_nhds]
    · rw [fderiv_of_notMem_tsupport ℝ hx]
      simp
  simp_rw [hl,hr]
  exact integral_inner_fderiv μ hu hw hc e

lemma integral_weightedAdjoint_on {U : Set V} (hU : IsOpen U)
    (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (ρ : V → ℝ) (u : V → W) (v : V → Q)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (hb : ContDiffOn ℝ ∞ b U)
    (hρ : ContDiffOn ℝ ∞ ρ U) (hu : ContDiff ℝ ∞ u) (hv : ContDiffOn ℝ ∞ v U)
    (hc : HasCompactSupport u) (hsub : tsupport u ⊆ U)
    (hρ0 : ∀ x, u x ≠ 0 → ρ x ≠ 0) :
    (∫ x, ρ x * ⟪u x,weightedAdjoint e a b ρ v x⟫ ∂μ) =
      ∫ x, ρ x * ⟪differential e a b u x,v x⟫ ∂μ := by
  classical
  let F : ι → V → W := fun i x => (ρ x • a i x).adjoint (v x)
  let Adj : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hF (i : ι) : ContDiffOn ℝ ∞ (F i) U :=
    (Adj.contDiff.comp_contDiffOn (hρ.smul (ha i))).clm_apply hv
  have hFat (i : ι) (x : V) (hx : x ∈ U) : ContDiffAt ℝ ∞ (F i) x :=
    (hF i x hx).contDiffAt (hU.mem_nhds hx)
  have hi (i : ι) : Integrable (fun x => ⟪u x,fderiv ℝ (F i) x (e i)⟫) μ :=
    integrable_inner_compact_local μ hu.continuous (fun x hx =>
      ((hFat i x (hsub hx)).continuousAt_fderiv (by simp)).clm_apply continuousAt_const) hc
  have hj (i : ι) : Integrable (fun x => ⟪fderiv ℝ u x (e i),F i x⟫) μ :=
    integrable_inner_compact_local μ
      ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)
      (fun x hx => (hFat i x (hsub (tsupport_fderiv_apply_subset ℝ (e i) hx))).continuousAt)
      (hc.fderiv_apply ℝ (e i))
  have hbF : ContDiffOn ℝ ∞ (fun x => (ρ x • b x).adjoint (v x)) U :=
    (Adj.contDiff.comp_contDiffOn (hρ.smul hb)).clm_apply hv
  have hbi : Integrable (fun x => ρ x * ⟪b x (u x),v x⟫) μ := by
    have hh := integrable_inner_compact_local μ hu.continuous (fun x hx =>
      ((hbF x (hsub hx)).contDiffAt (hU.mem_nhds (hsub hx))).continuousAt) hc
    convert hh using 1
    funext x
    simp only [ContinuousLinearMap.adjoint_inner_right,_root_.smul_apply,inner_smul_left,conj_trivial]
  have he (x : V) : ρ x * ⟪differential e a b u x,v x⟫ =
      (∑ i, ⟪fderiv ℝ u x (e i),F i x⟫) + ρ x * ⟪b x (u x),v x⟫ := by
    simp only [differential,inner_add_left,sum_inner,mul_add,Finset.mul_sum,F,
      ContinuousLinearMap.adjoint_inner_right,_root_.smul_apply,inner_smul_left,conj_trivial]
  simp_rw [weightedAdjoint_pairing e a b ρ u v _ (hρ0 _),he]
  change (∫ x, -(∑ i, ⟪u x,fderiv ℝ (F i) x (e i)⟫) + ρ x * ⟪b x (u x),v x⟫ ∂μ) = _
  have hsumi := integrable_finsetSum Finset.univ (fun i _ => hi i)
  have hsumj := integrable_finsetSum Finset.univ (fun i _ => hj i)
  have hneg : Integrable (fun x => -(∑ i, ⟪u x,fderiv ℝ (F i) x (e i)⟫)) μ := hsumi.neg
  rw [integral_add hneg hbi, integral_neg,integral_finsetSum _ (fun i _ => hi i),
    integral_add hsumj hbi,integral_finsetSum _ (fun i _ => hj i)]
  congr 1
  simp_rw [integral_inner_fderiv_on μ hU hu (hF _) hc hsub]
  simp

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

end

end OAI
