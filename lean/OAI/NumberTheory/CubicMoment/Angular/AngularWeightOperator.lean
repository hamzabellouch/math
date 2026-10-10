import OAI.NumberTheory.CubicMoment.Angular.AngularLogCutoff
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticUniformWeights

namespace OAI

/-! A fixed continuous operator from logarithmic test functions to plane
annuli. It makes the angular lattice bounds uniform over the given weights. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology SchwartzMap
namespace CubicFirstMoment

def angularComplexCutoff (a b : ℝ) (x : ℝ) : ℂ := angularPositiveCutoff a b x

lemma angularComplexCutoff_compact {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasCompactSupport (angularComplexCutoff a b) :=
  (angularPositiveCutoff_compact ha hb).comp_left Complex.ofReal_zero

lemma angularComplexCutoff_smooth (a b : ℝ) :
    ContDiff ℝ ∞ (angularComplexCutoff a b) :=
  Complex.ofRealCLM.contDiff.comp (angularPositiveCutoff_smooth a b)

lemma angularComplexCutoff_positive {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    tsupport (angularComplexCutoff a b) ⊆ Ioi 0 := by
  have he : Function.support (angularComplexCutoff a b) =
      Function.support (angularPositiveCutoff a b) := by
    ext x
    simp only [Function.mem_support,angularComplexCutoff,ne_eq,Complex.ofReal_eq_zero]
  change closure (Function.support _) ⊆ _
  rw [he]
  exact angularPositiveCutoff_positive ha hb

lemma angularNormSq_temperate : Function.HasTemperateGrowth Complex.normSq := by
  have he : (Complex.normSq : ℂ → ℝ) = fun z => ‖z‖^2 :=
    funext Complex.normSq_eq_norm_sq
  rw [he]
  exact Function.hasTemperateGrowth_norm_sq ℂ

lemma angularNormSq_growth :
    ∃ (k : ℕ) (C : ℝ), ∀ z : ℂ, ‖z‖ ≤ C*(1+‖Complex.normSq z‖)^k := by
  refine ⟨1,1,?_⟩
  intro z
  rw [pow_one,one_mul,Real.norm_eq_abs,abs_of_nonneg (Complex.normSq_nonneg z),
    Complex.normSq_eq_norm_sq]
  nlinarith [sq_nonneg (‖z‖-1)]

def angularWeightOperator (ℓ : ℤ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℂ,ℂ) :=
  ((SchwartzMap.smulLeftCLM ℂ (angularAnnulus ℓ (angularComplexCutoff a b))).restrictScalars ℝ).comp
    ((SchwartzMap.compCLM ℝ angularNormSq_temperate angularNormSq_growth).comp
      (SchwartzMap.compCLM ℝ (angularLogExtension_temperate (by positivity : 0 < a/2)
        (by positivity : 0 < 2*b)) (angularLogExtension_growth (by positivity : 0 < a/2)
        (by positivity : 0 < 2*b))))

lemma angularWeightOperator_apply (ℓ : ℤ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (F : 𝓢(ℝ,ℂ)) (z : ℂ) :
    angularWeightOperator ℓ a b ha hb F z =
      angularAnnulus ℓ (angularComplexCutoff a b) z *
        F (angularLogExtension (a/2) (2*b) (Complex.normSq z)) := by
  have hq := (angularAnnulus_compact ℓ (angularComplexCutoff_compact ha hb)).hasTemperateGrowth
    (angularAnnulus_smooth ℓ (angularComplexCutoff_positive ha hb) (angularComplexCutoff_smooth a b))
  change (SchwartzMap.smulLeftCLM ℂ (angularAnnulus ℓ (angularComplexCutoff a b))) _ z = _
  rw [SchwartzMap.smulLeftCLM_apply_apply hq]
  rfl

lemma UniformLogWeights.annular_support {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (i : ι) :
    tsupport (W i) ⊆ Icc (Real.exp (-h.radius)) (Real.exp h.radius) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hp : 0 < x := h.positive i (subset_tsupport _ hx)
  have hu : -Real.log x ∈ tsupport (fun v => W i (Real.exp (-v))) := by
    apply subset_tsupport
    simpa only [Function.mem_support,neg_neg,Real.exp_log hp] using hx
  have he := abs_le.mp (h.support_bound i (-Real.log x) hu)
  constructor
  · have ht := Real.exp_le_exp.mpr (show -h.radius ≤ Real.log x by linarith)
    simpa only [Real.exp_log hp] using ht
  · have ht := Real.exp_le_exp.mpr (show Real.log x ≤ h.radius by linarith)
    simpa only [Real.exp_log hp] using ht

lemma angularWeightOperator_log_apply (ℓ : ℤ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (hsupp : tsupport W ⊆ Icc a b) :
    angularWeightOperator ℓ a b ha hb (mellinLogSchwartz W hW hpos hsm 0) =
      angularAnnulusSchwartz ℓ W hW hpos hsm := by
  ext z
  rw [angularWeightOperator_apply]
  let x := Complex.normSq z
  by_cases hk : angularPositiveCutoff a b x = 0
  · have hw : W x = 0 := by
      by_contra hn
      have hix := hsupp (subset_tsupport _ hn)
      have ho := angularPositiveCutoff_one ha hb hix
      exact zero_ne_one (hk.symm.trans ho)
    change (angularPlanePhase ℓ z*(angularPositiveCutoff a b x:ℂ))*
      mellinLogSchwartz W hW hpos hsm 0 (angularLogExtension (a/2) (2*b) x) =
        angularPlanePhase ℓ z*W x
    simp only [hk,Complex.ofReal_zero,mul_zero,zero_mul,hw]
  · have hx := angularPositiveCutoff_tsupport ha hb (subset_tsupport _ hk)
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx.1
    have hg := angularLogExtension_eq_log (by positivity : 0 < a/2)
      (by positivity : 0 < 2*b) hx
    have hc : (angularPositiveCutoff a b x:ℂ)*W x = W x := by
      by_cases hw : W x = 0
      · simp only [hw,mul_zero]
      · rw [angularPositiveCutoff_one ha hb (hsupp (subset_tsupport _ hw)),
          Complex.ofReal_one,one_mul]
    change (angularPlanePhase ℓ z*(angularPositiveCutoff a b x:ℂ))*
      mellinLogSchwartz W hW hpos hsm 0 (angularLogExtension (a/2) (2*b) x) =
        angularPlanePhase ℓ z*W x
    rw [hg]
    simp only [mellinLogSchwartz_apply,neg_zero,zero_mul,Real.exp_zero,one_smul,neg_neg,Real.exp_log hx0]
    rw [mul_assoc,hc]

theorem UniformLogWeights.angularAnnulus_bounded {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (ℓ : ℤ) :
    Bornology.IsVonNBounded ℝ
      ((fun i => angularAnnulusSchwartz ℓ (W i) (h.compact i) (h.positive i) (h.smooth i)) '' Set.univ) := by
  let f : ι → 𝓢(ℝ,ℂ) := fun i => mellinLogSchwartz (W i) (h.compact i) (h.positive i) (h.smooth i) 0
  have hb : Bornology.IsVonNBounded ℝ (f '' Set.univ) := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded f |>.2
    intro kn
    obtain ⟨C,hC,hbound⟩ := h.log_seminorms 0 kn.1 kn.2
    refine ⟨C+1,by linarith,?_⟩
    intro i _
    exact (hbound i 0 (by simp)).trans_lt (by linarith)
  let L := angularWeightOperator ℓ (Real.exp (-h.radius)) (Real.exp h.radius)
    (Real.exp_pos _) (Real.exp_pos _)
  have he : L '' (f '' Set.univ) =
      ((fun i => angularAnnulusSchwartz ℓ (W i) (h.compact i) (h.positive i) (h.smooth i)) '' Set.univ) := by
    rw [←Set.image_comp]
    congr 1
    funext i
    exact angularWeightOperator_log_apply ℓ (Real.exp_pos _) (Real.exp_pos _)
      (W i) (h.compact i) (h.positive i) (h.smooth i) (h.annular_support i)
  rw [←he]
  exact hb.image L

def angularTraceFourierCLM : 𝓢(ℂ,ℂ) →L[ℝ] 𝓢(ℂ,ℂ) :=
  ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (Complex.conjCLE.trans (complexMulEquiv 2 (by norm_num)))).comp
      (SchwartzMap.fourierTransformCLM ℂ)).restrictScalars ℝ

lemma angularTraceFourierCLM_apply (F : 𝓢(ℂ,ℂ)) :
    angularTraceFourierCLM F = traceFourierSchwartz F := rfl

theorem UniformLogWeights.angularFourier_seminorm {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (ℓ : ℤ) (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i,
      SchwartzMap.seminorm ℝ k n (traceFourierSchwartz
        (angularAnnulusSchwartz ℓ (W i) (h.compact i) (h.positive i) (h.smooth i))) ≤ C := by
  let f : ι → 𝓢(ℂ,ℂ) := fun i =>
    angularAnnulusSchwartz ℓ (W i) (h.compact i) (h.positive i) (h.smooth i)
  have hb := (h.angularAnnulus_bounded ℓ).image angularTraceFourierCLM
  rw [←Set.image_comp] at hb
  obtain ⟨C,hC,hbound⟩ :=
    (schwartz_withSeminorms ℝ ℂ ℂ).image_isVonNBounded_iff_seminorm_bounded
      (angularTraceFourierCLM ∘ f) |>.mp hb (k,n)
  exact ⟨C,hC,fun i => (hbound i (Set.mem_univ i)).le⟩

end CubicFirstMoment

end

end OAI
