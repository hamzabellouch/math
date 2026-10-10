import OAI.Geometry.SurfaceImmersion.Correction.C1ManifoldSmoothing
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! Weighted first jets detect immersion on the region where a partition
weight is nonzero. They depend continuously on the localized C1 data. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def weightedJet (w : Base → ℝ) (l : Base → V) (x : Base) : Base →L[ℝ] V :=
  w x • fderiv ℝ l x - (fderiv ℝ w x).smulRight (l x)

lemma continuous_weightedJet {w : Base → ℝ} {l : Base → V}
    (hw : ContDiff ℝ 1 w) (hl : ContDiff ℝ 1 l) : Continuous (weightedJet w l) := by
  exact (hw.continuous.smul (hl.continuous_fderiv one_ne_zero)).sub
    ((ContinuousLinearMap.smulRightL ℝ Base V).continuous₂.comp
      ((hw.continuous_fderiv one_ne_zero).prodMk hl.continuous))

lemma weightedJet_eq_smul {w : Base → ℝ} {l h : Base → V} {x : Base}
    (hw : DifferentiableAt ℝ w x) (hh : DifferentiableAt ℝ h x)
    (he : l =ᶠ[𝓝 x] fun y => w y • h y) :
    weightedJet w l x = (w x)^2 • fderiv ℝ h x := by
  unfold weightedJet
  rw [he.fderiv_eq, fderiv_fun_smul hw hh, he.self_of_nhds]
  ext v
  simp only [sub_apply,smul_apply,add_apply,ContinuousLinearMap.smulRight_apply]
  simp only [smul_add,smul_smul,pow_two,mul_comm (w x) ((fderiv ℝ w x) v)]
  abel

lemma weightedJet_sub {w : Base → ℝ} {f g : Base → V} {x : Base}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    weightedJet w (g-f) x = weightedJet w g x-weightedJet w f x := by
  unfold weightedJet
  rw [fderiv_sub hg hf]
  ext v
  simp only [sub_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,Pi.sub_apply,smul_sub]
  abel

lemma norm_weightedJet_le {w : Base → ℝ} {l : Base → V} {x : Base} {C : ℝ}
    (hl : ‖l x‖ ≤ C) (hd : ‖fderiv ℝ l x‖ ≤ C) :
    ‖weightedJet w l x‖ ≤ (‖w x‖+‖fderiv ℝ w x‖)*C := by
  calc
    _ ≤ ‖w x • fderiv ℝ l x‖+‖(fderiv ℝ w x).smulRight (l x)‖ := norm_sub_le _ _
    _ = ‖w x‖*‖fderiv ℝ l x‖+‖fderiv ℝ w x‖*‖l x‖ := by
      rw [norm_smul,ContinuousLinearMap.norm_smulRight_apply]
    _ ≤ ‖w x‖*C+‖fderiv ℝ w x‖*C := by gcongr
    _ = _ := by ring

theorem compact_injective_stability {K : Set (Base →L[ℝ] V)}
    (hK : IsCompact K) (hI : ∀ L ∈ K, Function.Injective L) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ L ∈ K, ∀ H : Base →L[ℝ] V,
      ‖H-L‖ < ε → Function.Injective H := by
  obtain ⟨ε,hε,he⟩ := hK.exists_thickening_subset_open
    ContinuousLinearMap.isOpen_injective hI
  exact ⟨ε,hε,fun L hL H hH => he
    (Metric.mem_thickening_iff.mpr ⟨L,hL,by simpa only [dist_eq_norm] using hH⟩)⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

def localizedWeight (p : M) (ψ : M → ℝ) : Base → ℝ := localize p ψ (fun _ => 1)

lemma localizedWeight_smooth (p : M) {ψ : M → ℝ}
    (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ) (hs : tsupport ψ ⊆ (chart p).source) :
    ContDiff ℝ ∞ (localizedWeight p ψ) := localize_smooth p hψ hs contMDiff_const

omit [CompactSpace M] in
lemma chart_mdifferentiable (p : M) : (chart p).MDifferentiable planeModel 𝓘(ℝ,Base) :=
  ⟨(chart_smooth p).mdifferentiableOn (by simp),
    (chart_symm_smooth p).mdifferentiableOn (by simp)⟩

omit [CompactSpace M] in
lemma fderiv_comp_chart_symm {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f) (p : M) {x : Base}
    (hx : x ∈ (chart p).target) :
    fderiv ℝ (f ∘ (chart p).symm) x =
      (mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)).comp
        (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x) := by
  rw [← mfderiv_eq_fderiv]
  exact mfderiv_comp x (hf.mdifferentiable one_ne_zero).mdifferentiableAt
    ((chart_mdifferentiable p).mdifferentiableAt_symm hx)

lemma localized_weightedJet {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f) (p : M) {ψ : M → ℝ}
    (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ) (hs : tsupport ψ ⊆ (chart p).source)
    {x : Base} (hx : x ∈ (chart p).target) :
    weightedJet (localizedWeight p ψ) (localize p ψ f) x =
      (ψ ((chart p).symm x))^4 •
        ((mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)).comp
          (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x)) := by
  have hh : DifferentiableAt ℝ (f ∘ (chart p).symm) x :=
    ((hf.mdifferentiable one_ne_zero).mdifferentiableAt.comp x
      ((chart_mdifferentiable p).mdifferentiableAt_symm hx)).differentiableAt
  have he : localize p ψ f =ᶠ[𝓝 x]
      fun y => localizedWeight p ψ y • (f ∘ (chart p).symm) y := by
    filter_upwards [(chart p).open_target.mem_nhds hx] with y hy
    simp only [localizedWeight,localize,indicator_of_mem hy,smul_eq_mul,mul_one,
      Function.comp_apply]
  rw [weightedJet_eq_smul ((localizedWeight_smooth p hψ hs).differentiable (by simp) x) hh he,
    fderiv_comp_chart_symm hf p hx]
  have hw : localizedWeight p ψ x = (ψ ((chart p).symm x))^2 := by
    simp only [localizedWeight,localize,indicator_of_mem hx,smul_eq_mul,mul_one]
  rw [hw,← pow_mul]
  norm_num
  rfl

/-- The weighted jet loses no immersion information wherever its weight is
nonzero; the chart differential is an isomorphism there. -/
lemma localized_weightedJet_injective_iff {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f) (p : M) {ψ : M → ℝ}
    (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ) (hs : tsupport ψ ⊆ (chart p).source)
    {x : Base} (hx : x ∈ (chart p).target) (hw : ψ ((chart p).symm x) ≠ 0) :
    Function.Injective (weightedJet (localizedWeight p ψ) (localize p ψ f) x) ↔
      Function.Injective (mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)) := by
  rw [localized_weightedJet hf p hψ hs hx]
  constructor
  · intro hi
    have hcomp : Function.Injective
        ((mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)).comp
          (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x)) := by
      intro v u h
      apply hi
      change (ψ ((chart p).symm x))^4 •
          ((mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)).comp
            (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x)) v = _
      exact congrArg ((ψ ((chart p).symm x))^4 • ·) h
    change Function.Injective
      ((mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)) ∘
        (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x)) at hcomp
    exact hcomp.of_comp_right ((chart_mdifferentiable p).symm.mfderiv_surjective hx)
  · intro hi
    exact (smul_right_injective V (pow_ne_zero 4 hw)).comp
      (hi.comp ((chart_mdifferentiable p).symm.mfderiv_injective hx))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
