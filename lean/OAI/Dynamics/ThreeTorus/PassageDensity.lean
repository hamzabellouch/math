import OAI.Dynamics.ThreeTorus.PassageMass

namespace OAI

/-! Unfolded and folded retained densities, branch kernels, residue sampling, and spectral limits. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ThreeTorus

/-- The usual interval representative of a circle weight, with zero extension. -/
def circleDensityLift (o : ℝ) (q : UnitAddCircle → ℝ) : ℝ → ℝ :=
  (Ioc o (o+1)).indicator (fun x => q (x : UnitAddCircle))

lemma circle_integral_lift (o : ℝ) (q : UnitAddCircle → ℝ) :
    (∫ x, circleDensityLift o q x) = ∫ a, q a ∂AddCircle.haarAddCircle := by
  rw [circleDensityLift,integral_indicator measurableSet_Ioc]
  have h := AddCircle.integral_preimage 1 o q
  simpa [AddCircle.volume_eq_smul_haarAddCircle] using h

lemma integrable_circleDensityLift {q : UnitAddCircle → ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (o : ℝ) :
    Integrable (circleDensityLift o q) := by
  have hmp : MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
      (volume.restrict (Ioc o (o+1))) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 o
  have hi : IntegrableOn (fun x : ℝ => q (x : UnitAddCircle)) (Ioc o (o+1)) :=
    (hmp.integrable_comp hq.aestronglyMeasurable).2 hq
  exact hi.integrable_indicator measurableSet_Ioc

/-- Lifting a circle density on one period commutes with every measurable
spectral pushforward. This includes the actual jitter, not just polynomial tests. -/
lemma circleDensityLift_pushforward {Y : Type*} [MeasurableSpace Y]
    {q : UnitAddCircle → ℝ} (hq : Integrable q AddCircle.haarAddCircle)
    {T : UnitAddCircle → Y} (hT : Measurable T) (o : ℝ) :
    ((volume : Measure ℝ).withDensityᵥ (circleDensityLift o q)).map
      (fun x : ℝ => T (x : UnitAddCircle)) =
    (AddCircle.haarAddCircle.withDensityᵥ q).map T := by
  have hTm : Measurable (fun x : ℝ => T (x : UnitAddCircle)) := hT.comp AddCircle.measurable_mk'
  ext s hs
  rw [VectorMeasure.map_apply _ hTm hs,VectorMeasure.map_apply _ hT hs,
    withDensityᵥ_apply (integrable_circleDensityLift hq o) (hTm hs),
    withDensityᵥ_apply hq (hT hs)]
  rw [← integral_indicator (hTm hs),← integral_indicator (hT hs)]
  rw [← circle_integral_lift o ((T ⁻¹' s).indicator q)]
  congr 1
  funext x
  by_cases hx : x ∈ Ioc o (o+1) <;> by_cases hxs : T (x : UnitAddCircle) ∈ s <;>
    simp [circleDensityLift,hx,hxs]

lemma circleDensityLift_eq {q : UnitAddCircle → ℝ} {q₀ : ℝ → ℝ} {o : ℝ}
    (he : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hs : Function.support q₀ ⊆ Ioc o (o+1)) : circleDensityLift o q = q₀ := by
  funext x
  by_cases hx : x ∈ Ioc o (o+1)
  · simp [circleDensityLift,hx,he x hx]
  · have hzero : q₀ x = 0 := by by_contra hn; exact hx (hs hn)
    simp [circleDensityLift,hx,hzero]

lemma integrable_branchDensity {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : IntegrableOn q I) : Integrable (branchDensity I J g D q) := by
  have he : IntegrableOn (branchDensity I J g D q) (J '' I) := by
    rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hI hJ hinj]
    apply hq.congr (ae_restrict_of_forall_mem hI (fun x hx => ?_))
    rw [smul_eq_mul,branchDensity_on hg hx]
    field_simp [abs_ne_zero.mpr (hD x hx)]
  have hs : (J '' I).indicator (branchDensity I J g D q) = branchDensity I J g D q := by
    funext y
    by_cases hy : y ∈ J '' I
    · exact indicator_of_mem hy _
    · simp [hy,branchDensity]
  simpa only [hs] using he.integrable_indicator himage

/-- Exact pushforward of the old squared coefficient on a branch. The only
inverse assumptions are the ordinary left-inverse identities on that branch. -/
lemma branchDensity_pushforward {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I)) (hJm : Measurable J)
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : Integrable q) (hqs : Function.support q ⊆ I) :
    ((volume : Measure ℝ).withDensityᵥ q).map J =
      (volume : Measure ℝ).withDensityᵥ (branchDensity I J g D q) := by
  have hK := integrable_branchDensity hI himage hJ hinj hg hD hq.integrableOn
  ext s hs
  rw [VectorMeasure.map_apply _ hJm hs,withDensityᵥ_apply hq (hJm hs),withDensityᵥ_apply hK hs]
  rw [← integral_indicator (hJm hs),← integral_indicator hs]
  have hleft : (∫ x, (J ⁻¹' s).indicator q x) = ∫ x in I, (J ⁻¹' s).indicator q x := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hqx : q x = 0 := by
      by_contra hh
      exact hx (hqs hh)
    by_cases hxs : x ∈ J ⁻¹' s <;> simp [hxs,hqx]
  have hright : (∫ y, s.indicator (branchDensity I J g D q) y) =
      ∫ y in J '' I, s.indicator (branchDensity I J g D q) y := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    by_cases hys : y ∈ s <;> simp [hys,branchDensity,hy]
  rw [hleft,hright,integral_image_eq_integral_abs_deriv_smul hI hJ hinj]
  apply setIntegral_congr_fun hI
  intro x hx
  dsimp only
  rw [smul_eq_mul]
  by_cases hxs : J x ∈ s
  · rw [indicator_of_mem (show x ∈ J ⁻¹' s from hxs),indicator_of_mem hxs,branchDensity_on hg hx]
    field_simp [abs_ne_zero.mpr (hD x hx)]
  · rw [indicator_of_notMem (show x ∉ J ⁻¹' s from hxs),indicator_of_notMem hxs,mul_zero]

lemma density_map_congr_support {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {f : X → ℝ} (hf : Integrable f μ)
    {T₁ T₂ : X → Y} (h₁ : Measurable T₁) (h₂ : Measurable T₂)
    (he : ∀ x, f x ≠ 0 → T₁ x = T₂ x) :
    (μ.withDensityᵥ f).map T₁ = (μ.withDensityᵥ f).map T₂ := by
  classical
  ext s hs
  rw [VectorMeasure.map_apply _ h₁ hs,VectorMeasure.map_apply _ h₂ hs,
    withDensityᵥ_apply hf (h₁ hs),withDensityᵥ_apply hf (h₂ hs),
    ← integral_indicator (h₁ hs),← integral_indicator (h₂ hs)]
  congr 1
  funext x
  change (if T₁ x ∈ s then f x else 0) = (if T₂ x ∈ s then f x else 0)
  by_cases hx : f x = 0
  · simp [hx]
  · rw [he x hx]

/-- The branch-Jacobian formula on the actual circle. The global periodic
jitter need not be injective; only the good arc bearing the weight is used. -/
lemma circle_branch_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : Function.support q₀ ⊆ Ioc o (o+1)) (hqs : Function.support q₀ ⊆ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0) :
    (AddCircle.haarAddCircle.withDensityᵥ q).map J =
      (volume : Measure ℝ).withDensityᵥ (branchDensity I J₀ g D q₀) := by
  have hlift := circleDensityLift_eq hq₀ hq₀s
  have hi : Integrable q₀ := by rw [← hlift]; exact integrable_circleDensityLift hq o
  rw [← circleDensityLift_pushforward hq hj o,hlift]
  rw [density_map_congr_support (T₁ := fun x : ℝ => J (x : UnitAddCircle)) hi (hj.comp AddCircle.measurable_mk') hj₀
    (fun x hx => hJe x (hqs hx))]
  exact branchDensity_pushforward hI himage hj₀ hJ hinj hg hD hi hqs

/-- Total variation contracts under the actual temporal-frequency pushforward.
The real L¹ normalization has no factor 1/2. -/
lemma l1_pushforward_contraction {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → ℝ} {g : Y → ℝ} {T : X → Y}
    (hf : Integrable f μ) (hg : Integrable g ν) (hT : Measurable T)
    (hmap : (μ.withDensityᵥ f).map T = ν.withDensityᵥ g) :
    (∫ y, |g y| ∂ν) ≤ ∫ x, |f x| ∂μ := by
  have hv := MeasureTheory.VectorMeasure.variation_map_le (μ := μ.withDensityᵥ f) (φ := T)
  rw [hmap,Measure.variation_withDensityᵥ hg,Measure.variation_withDensityᵥ hf] at hv
  have hh := hv univ
  rw [Measure.map_apply hT MeasurableSet.univ] at hh
  simp only [preimage_univ,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at hh
  have he (z : ℝ) : ‖z‖ₑ = ENNReal.ofReal |z| := Real.enorm_eq_ofReal_abs z
  simp_rw [he] at hh
  rw [← ofReal_integral_eq_lintegral_ofReal hg.abs (Filter.Eventually.of_forall (fun _ => abs_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hf.abs (Filter.Eventually.of_forall (fun _ => abs_nonneg _))] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ => abs_nonneg _))).mp hh

lemma l1_pushforward_difference {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f₁ f₂ : X → ℝ} {g₁ g₂ : Y → ℝ} {T : X → Y}
    (hf₁ : Integrable f₁ μ) (hf₂ : Integrable f₂ μ)
    (hg₁ : Integrable g₁ ν) (hg₂ : Integrable g₂ ν) (hT : Measurable T)
    (h₁ : (μ.withDensityᵥ f₁).map T = ν.withDensityᵥ g₁)
    (h₂ : (μ.withDensityᵥ f₂).map T = ν.withDensityᵥ g₂) :
    (∫ y, |g₁ y-g₂ y| ∂ν) ≤ ∫ x, |f₁ x-f₂ x| ∂μ := by
  apply l1_pushforward_contraction (hf₁.sub hf₂) (hg₁.sub hg₂) hT
  rw [withDensityᵥ_sub hf₁ hf₂,withDensityᵥ_sub hg₁ hg₂]
  have he := map_sub (MeasureTheory.VectorMeasure.mapGm T) (μ.withDensityᵥ f₁) (μ.withDensityᵥ f₂)
  change (μ.withDensityᵥ f₁-μ.withDensityᵥ f₂).map T =
    (μ.withDensityᵥ f₁).map T-(μ.withDensityᵥ f₂).map T at he
  rw [he,h₁,h₂]

/-- Exact Jacobian cancellation in the unfolded output frequency t=(j+y)/N. -/
lemma temporalFrequency_pushforward {q : ℝ → ℝ} (hq : Integrable q)
    {n : ℝ} (hn : 0 < n) (j : ℝ) :
    ((volume : Measure ℝ).withDensityᵥ (fun y => n⁻¹*q y)).map (fun y => (j+y)/n) =
      (volume : Measure ℝ).withDensityᵥ (fun t => q (n*t-j)) := by
  have hmap : Measurable (fun y : ℝ => (j+y)/n) := by fun_prop
  have hq' : Integrable (fun t => q (n*t-j)) := by
    simpa only [sub_eq_add_neg] using
      (integrable_comp_mul_left_iff (fun x => q (x+ -j)) hn.ne').2 (hq.comp_add_right (-j))
  ext s hs
  rw [VectorMeasure.map_apply _ hmap hs,withDensityᵥ_apply (hq.const_mul n⁻¹) (hmap hs),
    withDensityᵥ_apply hq' hs,integral_const_mul]
  let F : ℝ → ℝ := ((fun y : ℝ => (j+y)/n) ⁻¹' s).indicator q
  have he : (fun t => F (n*t-j)) = s.indicator (fun t => q (n*t-j)) := by
    funext t
    by_cases ht : t ∈ s <;> simp [F,ht,hn.ne']
  rw [← integral_indicator (hmap hs),← integral_indicator hs,← he]
  change n⁻¹*(∫ y, F y) = ∫ t, F (n*t-j)
  rw [Measure.integral_comp_mul_left (fun x => F (x-j)) n,integral_sub_right_eq_self]
  simp only [smul_eq_mul,abs_of_pos (inv_pos.mpr hn)]

/-- Pushforward through a fixed smooth jitter followed by the output affine frequency.
This is the exact (not weak or asymptotic) density appearing in the passage. -/
lemma temporalFrequency_pushforward_comp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {W : X → ℝ} {q : ℝ → ℝ} {J : X → ℝ}
    (hW : Integrable W μ) (hq : Integrable q) (hJ : Measurable J)
    (hpush : (μ.withDensityᵥ W).map J = (volume : Measure ℝ).withDensityᵥ q)
    {n : ℝ} (hn : 0 < n) (j : ℝ) :
    (μ.withDensityᵥ (fun a => n⁻¹*W a)).map (fun a => (j+J a)/n) =
      (volume : Measure ℝ).withDensityᵥ (fun t => q (n*t-j)) := by
  have haf : Measurable (fun y : ℝ => (j+y)/n) := by fun_prop
  have hcomp (v : VectorMeasure X ℝ) :
      v.map (fun a => (j+J a)/n) = (v.map J).map (fun y : ℝ => (j+y)/n) := by
    ext s hs
    have hcompm : Measurable (fun a => (j+J a)/n) := haf.comp hJ
    rw [VectorMeasure.map_apply _ hcompm hs,
      VectorMeasure.map_apply _ haf hs,VectorMeasure.map_apply _ hJ (haf hs)]
    rfl
  rw [hcomp]
  have he : μ.withDensityᵥ (fun a => n⁻¹*W a) = n⁻¹ • μ.withDensityᵥ W := by
    ext s hs
    rw [withDensityᵥ_apply (hW.const_mul _) hs,smul_apply,withDensityᵥ_apply hW hs,
      integral_const_mul,smul_eq_mul]
  have heq : (volume : Measure ℝ).withDensityᵥ (fun y => n⁻¹*q y) =
      n⁻¹ • (volume : Measure ℝ).withDensityᵥ q := by
    ext s hs
    rw [withDensityᵥ_apply (hq.const_mul _) hs,smul_apply,withDensityᵥ_apply hq hs,
      integral_const_mul,smul_eq_mul]
  rw [he,VectorMeasure.map_smul,hpush,← heq]
  exact temporalFrequency_pushforward hq hn j

/-- The manuscript kernel K(s,y), including both signs of s. -/
def scaledBranchKernel (I : Set ℝ) (J g D q : ℝ → ℝ) (s y : ℝ) : ℝ :=
  |s|⁻¹*branchDensity I J g D q (y/s)

lemma scaledBranchKernel_eq {I : Set ℝ} (J g D q : ℝ → ℝ) {s : ℝ} (hs : s ≠ 0) (y : ℝ) :
    branchDensity I (fun x => s*J x) (fun y => g (y/s)) (fun x => s*D x) q y =
      scaledBranchKernel I J g D q s y := by
  classical
  have he : y ∈ (fun x => s*J x) '' I ↔ y/s ∈ J '' I := by
    constructor
    · rintro ⟨x,hx,hxy⟩
      exact ⟨x,hx,by rw [← hxy]; field_simp⟩
    · rintro ⟨x,hx,hxy⟩
      exact ⟨x,hx,by change s*J x = y; rw [hxy]; field_simp⟩
  by_cases hy : y/s ∈ J '' I
  · simp only [branchDensity,scaledBranchKernel,indicator_of_mem hy,
      indicator_of_mem (he.mpr hy),abs_mul]
    ring
  · simp only [branchDensity,scaledBranchKernel,indicator_of_notMem hy,
      indicator_of_notMem (fun h => hy (he.mp h)),mul_zero]

lemma integrable_scaledBranchKernel {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hq : Integrable (branchDensity I J g D q)) {s : ℝ} (hs : s ≠ 0) :
    Integrable (scaledBranchKernel I J g D q s) :=
  ((integrable_comp_div_iff _ hs).2 hq).const_mul _

/-- The exact branch kernel in the new temporal coordinate, on the torus.
Only the good arc need be injective, as in the geometric passage. -/
lemma circle_mode_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : Function.support q₀ ⊆ Ioc o (o+1)) (hqs : Function.support q₀ ⊆ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    {s n : ℝ} (hs : s ≠ 0) (hn : 0 < n) (j : ℝ) :
    (AddCircle.haarAddCircle.withDensityᵥ (fun a => n⁻¹*q a)).map
        (fun a => (j+s*J a)/n) =
      (volume : Measure ℝ).withDensityᵥ
        (fun t => scaledBranchKernel I J₀ g D q₀ s (n*t-j)) := by
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hK := integrable_branchDensity hI himage hJ hinj hg hD hqi.integrableOn
  have hsim : MeasurableSet ((fun x => s*J₀ x) '' I) := by
    have he : (fun x => s*J₀ x) '' I = (fun y : ℝ => s*y) '' (J₀ '' I) := by
      rw [image_image]
    rw [he]
    exact (Homeomorph.mulLeft₀ s hs).measurableEmbedding.measurableSet_image.mpr himage
  have hp := circle_branch_pushforward (g := fun y => g (y/s)) hq hq₀ hq₀s hqs
    (measurable_const.mul hj) (measurable_const.mul hj₀)
    (fun x hx => congrArg (fun y => s*y) (hJe x hx)) hI hsim
    (fun x hx => (hJ x hx).const_mul s)
    (fun x hx y hy he => hinj hx hy (mul_left_cancel₀ hs he))
    (fun x hx => show g (s*J₀ x/s) = x by simpa [hs] using hg x hx)
    (fun x hx => mul_ne_zero hs (hD x hx))
  have he : branchDensity I (fun x => s*J₀ x) (fun y => g (y/s)) (fun x => s*D x) q₀ =
      scaledBranchKernel I J₀ g D q₀ s := funext (scaledBranchKernel_eq _ _ _ _ hs)
  change (AddCircle.haarAddCircle.withDensityᵥ q).map (fun a => s*J a) =
    (volume : Measure ℝ).withDensityᵥ
      (branchDensity I (fun x => s*J₀ x) (fun y => g (y/s)) (fun x => s*D x) q₀) at hp
  rw [he] at hp
  exact temporalFrequency_pushforward_comp hq (integrable_scaledBranchKernel hK hs)
    (measurable_const.mul hj) hp hn j

lemma integral_abs_finset_sum_le {Y ι : Type*} [MeasurableSpace Y] {ν : Measure Y}
    (S : Finset ι) {f : ι → Y → ℝ} (hf : ∀ i ∈ S, Integrable (f i) ν) :
    (∫ y, |∑ i ∈ S, f i y| ∂ν) ≤ ∑ i ∈ S, ∫ y, |f i y| ∂ν := by
  calc
    _ ≤ ∫ y, ∑ i ∈ S, |f i y| ∂ν := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => abs_nonneg _)
      · exact integrable_finsetSum _ (fun i hi => (hf i hi).abs)
      · exact Filter.Eventually.of_forall (fun y => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := integral_finsetSum _ (fun i hi => (hf i hi).abs)

/-- Summed coefficient mass error controls the full density error, not merely
its moments. The maps may vary with the angular index. -/
lemma finite_density_sum_error {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {q w : ι → X → ℝ} {g h : ι → Y → ℝ}
    {T : ι → X → Y} (S : Finset ι)
    (hq : ∀ i ∈ S, Integrable (q i) μ) (hw : ∀ i ∈ S, Integrable (w i) μ)
    (hg : ∀ i ∈ S, Integrable (g i) ν) (hh : ∀ i ∈ S, Integrable (h i) ν)
    (hT : ∀ i ∈ S, Measurable (T i))
    (hqp : ∀ i ∈ S, (μ.withDensityᵥ (q i)).map (T i) = ν.withDensityᵥ (g i))
    (hwp : ∀ i ∈ S, (μ.withDensityᵥ (w i)).map (T i) = ν.withDensityᵥ (h i)) :
    (∫ y, |(∑ i ∈ S, g i y)-(∑ i ∈ S, h i y)| ∂ν) ≤
      ∑ i ∈ S, ∫ x, |q i x-w i x| ∂μ := by
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ S, ∫ y, |g i y-h i y| ∂ν :=
      integral_abs_finset_sum_le S (fun i hi => (hg i hi).sub (hh i hi))
    _ ≤ _ := Finset.sum_le_sum (fun i hi =>
      l1_pushforward_difference (hq i hi) (hw i hi) (hg i hi) (hh i hi)
        (hT i hi) (hqp i hi) (hwp i hi))

lemma cutoff_mass_pointwise {q w χ ψ : ℝ} (hq : 0 ≤ q)
    (hχ : 0 ≤ χ ∧ χ ≤ 1) (hχw : w ≠ 0 → χ = 1)
    (hψ : 0 ≤ ψ ∧ ψ ≤ 1) :
    |ψ^2*χ^2*q-ψ^2*w| ≤ |q-w| := by
  have hχ2 : χ^2 ≤ 1 := by nlinarith [hχ.1,hχ.2]
  have hψ2 : ψ^2 ≤ 1 := by nlinarith [hψ.1,hψ.2]
  have hh : |χ^2*q-w| ≤ |q-w| := by
    by_cases hw : w = 0
    · rw [hw,sub_zero,sub_zero,abs_of_nonneg hq,abs_of_nonneg (mul_nonneg (sq_nonneg _) hq)]
      exact mul_le_of_le_one_left hq hχ2
    · simp [hχw hw]
  calc
    _ = ψ^2*|χ^2*q-w| := by rw [mul_assoc,← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg _)]
    _ ≤ |χ^2*q-w| := mul_le_of_le_one_left (abs_nonneg _) hψ2
    _ ≤ _ := hh

/-- The actual retained cutoffs cost no additional error in the stationary mass
estimate. The coefficient array may have both positive and negative indices. -/
lemma retained_density_sum_error {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {c : ℤ → X → ℂ} {w χ : ℤ → X → ℝ}
    {ψ : X → ℝ} {g h : ℤ → Y → ℝ} {T : ℤ → X → Y} (S : Finset ℤ)
    (hq : ∀ i ∈ S, Integrable (fun x => ψ x^2*χ i x^2*‖c i x‖^2) μ)
    (hw : ∀ i ∈ S, Integrable (fun x => ψ x^2*w i x) μ)
    (hE : ∀ i, Integrable (fun x => |‖c i x‖^2-w i x|) μ)
    (hEs : Summable (fun i => ∫ x, |‖c i x‖^2-w i x| ∂μ))
    (hχ : ∀ i x, 0 ≤ χ i x ∧ χ i x ≤ 1) (hχw : ∀ i x, w i x ≠ 0 → χ i x = 1)
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (hg : ∀ i ∈ S, Integrable (g i) ν) (hh : ∀ i ∈ S, Integrable (h i) ν)
    (hT : ∀ i ∈ S, Measurable (T i))
    (hqp : ∀ i ∈ S, (μ.withDensityᵥ (fun x => ψ x^2*χ i x^2*‖c i x‖^2)).map (T i) =
      ν.withDensityᵥ (g i))
    (hwp : ∀ i ∈ S, (μ.withDensityᵥ (fun x => ψ x^2*w i x)).map (T i) =
      ν.withDensityᵥ (h i)) :
    (∫ y, |(∑ i ∈ S, g i y)-(∑ i ∈ S, h i y)| ∂ν) ≤
      ∑' i : ℤ, ∫ x, |‖c i x‖^2-w i x| ∂μ := by
  calc
    _ ≤ ∑ i ∈ S, ∫ x, |ψ x^2*χ i x^2*‖c i x‖^2-ψ x^2*w i x| ∂μ :=
      finite_density_sum_error S hq hw hg hh hT hqp hwp
    _ ≤ ∑ i ∈ S, ∫ x, |‖c i x‖^2-w i x| ∂μ := by
      apply Finset.sum_le_sum
      intro i _hi
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) (hE i)
      exact Filter.Eventually.of_forall (fun x =>
        cutoff_mass_pointwise (sq_nonneg _) (hχ i x) (hχw i x) (hψ x))
    _ ≤ _ := Summable.sum_le_tsum S (fun _ _ => integral_nonneg (fun _ => abs_nonneg _)) hEs

/-- The actual unfolded spectral density of a retained angular mode, of mass q da.
The argument q₀ is its zero-extended representative in the jitter good arc. -/
def unfoldedModeDensity (I : Set ℝ) (J g D q₀ : ℝ → ℝ) (n j t : ℝ) : ℝ :=
  scaledBranchKernel I J g D (fun a => n*q₀ a) (j/n) (n*t-j)

lemma integrable_unfoldedModeDensity {I : Set ℝ} {J g D q₀ : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : Integrable q₀) {n j : ℝ} (hn : 0 < n) (hj : j ≠ 0) :
    Integrable (unfoldedModeDensity I J g D q₀ n j) := by
  have hi := integrable_scaledBranchKernel
    (integrable_branchDensity hI himage hJ hinj hg hD (hq.const_mul n).integrableOn)
    (div_ne_zero hj hn.ne')
  change Integrable (fun t => scaledBranchKernel I J g D (fun a => n*q₀ a) (j/n) (n*t-j))
  simpa only [sub_eq_add_neg] using
    (integrable_comp_mul_left_iff (fun x =>
      scaledBranchKernel I J g D (fun a => n*q₀ a) (j/n) (x+ -j)) hn.ne').2
      (hi.comp_add_right (-j))

/-- Exact density of an actual circle mode before any stationary approximation. -/
lemma unfoldedModeDensity_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : Function.support q₀ ⊆ Ioc o (o+1)) (hqs : Function.support q₀ ⊆ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    {n j : ℝ} (hn : 0 < n) (hjn : j ≠ 0) :
    (AddCircle.haarAddCircle.withDensityᵥ q).map
        (fun a => (j+(j/n)*J a)/n) =
      (volume : Measure ℝ).withDensityᵥ (unfoldedModeDensity I J₀ g D q₀ n j) := by
  have hsupp (L : Set ℝ) (hh : Function.support q₀ ⊆ L) :
      Function.support (fun a => n*q₀ a) ⊆ L := by
    intro x hx
    apply hh
    intro hz
    exact hx (by simp only [hz,mul_zero])
  have hp := circle_mode_pushforward (q := fun a => n*q a) (q₀ := fun a => n*q₀ a)
    (s := j/n) (hq.const_mul n) (fun x hx => congrArg (fun y => n*y) (hq₀ x hx))
    (hsupp _ hq₀s) (hsupp _ hqs) hj hj₀ hJe hI himage hJ hinj hg hD
    (div_ne_zero hjn hn.ne') hn j
  change _ = (volume : Measure ℝ).withDensityᵥ
    (fun t => scaledBranchKernel I J₀ g D (fun a => n*q₀ a) (j/n) (n*t-j))
  simpa only [← mul_assoc,inv_mul_cancel₀ hn.ne',one_mul] using hp

/-- Finite actual retained mode density versus finite leading sampled mass.
Every density here is explicit; none of the pushforward identities is assumed. -/
lemma finite_unfolded_density_error {I : Set ℝ} {J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o n : ℝ} (hn : 0 < n)
    (S : Finset ℤ) (hS : ∀ j ∈ S, j ≠ 0)
    {q w : ℤ → UnitAddCircle → ℝ} {q₀ w₀ : ℤ → ℝ → ℝ}
    (hq : ∀ j ∈ S, Integrable (q j) AddCircle.haarAddCircle)
    (hw : ∀ j ∈ S, Integrable (w j) AddCircle.haarAddCircle)
    (hq₀ : ∀ j ∈ S, ∀ x ∈ Ioc o (o+1), q j (x : UnitAddCircle) = q₀ j x)
    (hw₀ : ∀ j ∈ S, ∀ x ∈ Ioc o (o+1), w j (x : UnitAddCircle) = w₀ j x)
    (hqs : ∀ j ∈ S, Function.support (q₀ j) ⊆ Ioc o (o+1) ∩ I)
    (hws : ∀ j ∈ S, Function.support (w₀ j) ⊆ Ioc o (o+1) ∩ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0) :
    (∫ t, |(∑ j ∈ S, unfoldedModeDensity I J₀ g D (q₀ j) n j t)-
      (∑ j ∈ S, unfoldedModeDensity I J₀ g D (w₀ j) n j t)|) ≤
       ∑ j ∈ S, ∫ a, |q j a-w j a| ∂AddCircle.haarAddCircle := by
  have hqI (j : ℤ) (hjs : j ∈ S) : Integrable (q₀ j) := by
    rw [← circleDensityLift_eq (hq₀ j hjs) ((hqs j hjs).trans inter_subset_left)]
    exact integrable_circleDensityLift (hq j hjs) o
  have hwI (j : ℤ) (hjs : j ∈ S) : Integrable (w₀ j) := by
    rw [← circleDensityLift_eq (hw₀ j hjs) ((hws j hjs).trans inter_subset_left)]
    exact integrable_circleDensityLift (hw j hjs) o
  have hjn (j : ℤ) (hjs : j ∈ S) : (j:ℝ) ≠ 0 := by exact_mod_cast hS j hjs
  apply finite_density_sum_error (g := fun j : ℤ => unfoldedModeDensity I J₀ g D (q₀ j) n j)
    (h := fun j : ℤ => unfoldedModeDensity I J₀ g D (w₀ j) n j) S hq hw
    (fun j hj => integrable_unfoldedModeDensity hI himage hJ hinj hg hD (hqI j hj) hn (hjn j hj))
    (fun j hj => integrable_unfoldedModeDensity hI himage hJ hinj hg hD (hwI j hj) hn (hjn j hj))
    (T := fun j a => ((j:ℝ)+((j:ℝ)/n)*J a)/n)
  · intro j _hj
    fun_prop
  · intro j hjs
    exact unfoldedModeDensity_pushforward (hq j hjs) (hq₀ j hjs)
      ((hqs j hjs).trans inter_subset_left) ((hqs j hjs).trans inter_subset_right)
      hj hj₀ hJe hI himage hJ hinj hg hD hn (hjn j hjs)
  · intro j hjs
    exact unfoldedModeDensity_pushforward (hw j hjs) (hw₀ j hjs)
      ((hws j hjs).trans inter_subset_left) ((hws j hjs).trans inter_subset_right)
      hj hj₀ hJe hI himage hJ hinj hg hD hn (hjn j hjs)

end ThreeTorus

noncomputable section
open Set Function Filter
open scoped Topology NNReal
namespace ThreeTorus

/-- Parametrized old-frequency Jacobian density, extended by zero off its branch. -/
def branchKernel (I : Set ℝ) (J : ℝ → ℝ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := by
  classical
  exact if p.1 ∈ J '' I then F (invFunOn J I p.1,p.2) / |deriv J (invFunOn J I p.1)| else 0

lemma support_branchKernel_subset {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ} :
    support (branchKernel I J F) ⊆ (fun p : ℝ × ℝ => (J p.1,p.2)) '' tsupport F := by
  rintro ⟨s,a⟩ hh
  have hs : s ∈ J '' I := by
    by_contra hn
    exact hh (by simp [branchKernel,hn])
  have hp := invFunOn_pos hs
  refine ⟨(invFunOn J I s,a),subset_tsupport F ?_,?_⟩
  · intro hz
    exact hh (by simp [branchKernel,hs,hz])
  · simp only [hp.2]

lemma branchKernel_compact {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : Continuous J) (hc : HasCompactSupport F) : HasCompactSupport (branchKernel I J F) := by
  apply HasCompactSupport.intro (hc.image (by fun_prop : Continuous (fun p : ℝ × ℝ => (J p.1,p.2))))
  intro p hp
  by_contra hn
  exact hp (support_branchKernel_subset hn)

lemma branchKernel_smooth {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ I ×ˢ univ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (branchKernel I J F) := by
  classical
  let g := invFunOn J I
  let M := (fun p : ℝ × ℝ => (J p.1,p.2)) '' tsupport F
  have hM : IsCompact M := hc.image (by fun_prop)
  have hzero {p : ℝ × ℝ} (hp : p ∉ M) : branchKernel I J F p = 0 :=
    notMem_support.mp (fun hn => hp (support_branchKernel_subset hn))
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := by
    exact hJ.deriv' 
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ M
  · rcases hp with ⟨⟨x,a⟩,hx,rfl⟩
    have hxI : x ∈ I := (hs hx).1
    have hy : J x ∈ J '' I := mem_image_of_mem J hxI
    have hgi := contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hxI
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hxI)
    have hge : g (J x) = x := by
      exact hinj (invFunOn_pos hy).1 hxI (invFunOn_pos hy).2
    have hin : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (g p.1,p.2)) (J x,a) :=
      (hgi.comp (J x,a) contDiffAt_fst).prodMk contDiffAt_snd
    have hDen : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => |deriv J (g p.1)|) (J x,a) := by
      have hh : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × ℝ => deriv J (g p.1)) (J x,a) :=
        hD.contDiffAt.comp (J x,a) (hgi.comp (J x,a) contDiffAt_fst)
      exact (contDiffAt_abs (by simpa only [hge] using hd x hxI)).comp (J x,a) hh
    have hquot : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => F (g p.1,p.2) / |deriv J (g p.1)|) (J x,a) := by
      apply (hF.contDiffAt.comp _ hin).div hDen
      simpa only [hge] using abs_ne_zero.mpr (hd x hxI)
    apply hquot.congr_of_eventuallyEq
    have hnear : ∀ᶠ p : ℝ × ℝ in 𝓝 (J x,a), p.1 ∈ J '' I :=
      continuous_fst.continuousAt.eventually ((isOpen_image_of_deriv_ne_zero hJ hIo hd).mem_nhds hy)
    filter_upwards [hnear] with p hp
    simp only [branchKernel,ite_eq_left hp,g]
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hM.isClosed.isOpen_compl.mem_nhds hp] with q hq
    exact hzero hq

lemma branchKernel_bounds {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : Continuous J) (hc : HasCompactSupport F) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      (∀ s a, A < |s| → branchKernel I J F (s,a) = 0) ∧
      (∀ s a, D < |a| → branchKernel I J F (s,a) = 0) := by
  have hC := branchKernel_compact (I := I) hJ hc
  obtain ⟨R,hR⟩ := hC.isBounded.subset_closedBall (0 : ℝ × ℝ)
  refine ⟨max R 0,max R 0,le_max_right _ _,le_max_right _ _,?_,?_⟩
  · intro s a hs
    by_contra hn
    have hh := hR (subset_tsupport _ hn)
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def] at hh
    have hab : |s| ≤ R := by simpa only [Real.norm_eq_abs] using (le_max_left ‖s‖ ‖a‖).trans hh
    exact (not_lt_of_ge (hab.trans (le_max_left _ _))) hs
  · intro s a hs
    by_contra hn
    have hh := hR (subset_tsupport _ hn)
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def] at hh
    have hab : |a| ≤ R := by simpa only [Real.norm_eq_abs] using (le_max_right ‖s‖ ‖a‖).trans hh
    exact (not_lt_of_ge (hab.trans (le_max_left _ _))) hs

/-- The exact Jacobian kernel for the affine-on-the-good-arc neutral jitter. -/
def affineKernel (F : ℝ × ℝ → ℝ) (L β s y : ℝ) : ℝ :=
  (|s| * L)⁻¹ * F (s,(y/s-β)/L)

lemma affineKernel_eq_zero_s {F : ℝ × ℝ → ℝ} {L β A s y : ℝ}
    (hF : ∀ s a, A < |s| → F (s,a) = 0) (hs : A < |s|) :
    affineKernel F L β s y = 0 := by simp [affineKernel,hF _ _ hs]

lemma affineKernel_eq_zero_y {F : ℝ × ℝ → ℝ} {L β A D s y : ℝ}
    (hL : 0 < L) (_hA : 0 ≤ A) (hD : 0 ≤ D)
    (hFs : ∀ s a, A < |s| → F (s,a) = 0)
    (hFa : ∀ s a, D < |a| → F (s,a) = 0)
    (hy : A*(L*D+|β|) < |y|) : affineKernel F L β s y = 0 := by
  by_cases hs : s = 0
  · simp [affineKernel,hs]
  by_cases hsA : A < |s|
  · exact affineKernel_eq_zero_s hFs hsA
  have hsA' : |s| ≤ A := le_of_not_gt hsA
  have hh : D < |(y/s-β)/L| := by
    by_contra hn
    have hn' := le_of_not_gt hn
    rw [abs_div,abs_of_pos hL,div_le_iff₀ hL] at hn'
    have hb := abs_add_le (y/s-β) β
    rw [sub_add_cancel] at hb
    have hx : |y/s| ≤ L*D+|β| := by linarith
    rw [abs_div,div_le_iff₀ (abs_pos.mpr hs)] at hx
    have hright : (L*D+|β|)*|s| ≤ (L*D+|β|)*A :=
      mul_le_mul_of_nonneg_left hsA' (by positivity)
    nlinarith
  simp [affineKernel,hFa _ _ hh]

lemma affineKernel_hasCompactSupport {F : ℝ × ℝ → ℝ} {L β A D : ℝ}
    (hL : 0 < L) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hFs : ∀ s a, A < |s| → F (s,a) = 0)
    (hFa : ∀ s a, D < |a| → F (s,a) = 0) :
    HasCompactSupport (Function.uncurry (affineKernel F L β)) := by
  apply HasCompactSupport.intro
    ((isCompact_Icc (a := -A) (b := A)).prod
      (isCompact_Icc (a := -(A*(L*D+|β|))) (b := A*(L*D+|β|))))
  rintro ⟨s,y⟩ hp
  simp only [mem_prod,mem_Icc,← abs_le,not_and_or,not_le] at hp
  rcases hp with hs | hy
  · exact affineKernel_eq_zero_s hFs hs
  · exact affineKernel_eq_zero_y hL hA hD hFs hFa hy

lemma affineKernel_smooth {F : ℝ × ℝ → ℝ} {L β ε : ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hε : 0 < ε)
    (hz : ∀ s a, |s| < ε → F (s,a) = 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (affineKernel F L β)) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨s,y⟩
  by_cases hs : s = 0
  · have he : ∀ᶠ p : ℝ × ℝ in 𝓝 (s,y), |p.1| < ε := by
      have hc : Continuous (fun p : ℝ × ℝ => |p.1|) := by fun_prop
      apply hc.continuousAt.eventually (gt_mem_nhds ?_)
      simpa [hs] using hε
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with p hp
    simp [Function.uncurry,affineKernel,hz _ _ hp]
  · have ha : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => |p.1|) (s,y) := by
      exact (contDiffAt_abs hs).comp (s,y) contDiffAt_fst
    have hin : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (p.1,(p.2/p.1-β)/L)) (s,y) := by
      exact contDiffAt_fst.prodMk (((contDiffAt_snd.div contDiffAt_fst hs).sub contDiffAt_const).div_const L)
    by_cases hL : L = 0
    · have he : Function.uncurry (affineKernel F L β) = fun _ => (0:ℝ) := by
        funext p; simp [Function.uncurry,affineKernel,hL]
      rw [he]
      exact contDiffAt_const
    · exact ((ha.mul contDiffAt_const).inv (mul_ne_zero (abs_ne_zero.mpr hs) hL)).mul
        (hF.contDiffAt.comp (s,y) hin)

/-- A compact smooth kernel has a single global Lipschitz bound. -/
lemma compact_smooth_lipschitz {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hc : HasCompactSupport F) : ∃ C : ℝ≥0, LipschitzWith C F := by
  obtain ⟨C,hC⟩ := (hc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hF.continuous_fderiv (by simp))
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (hF.differentiable (by simp))
  intro p
  exact (hC p).trans (le_max_left _ _)

lemma compact_smooth_kernel_lipschitz {K : ℝ → ℝ → ℝ}
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry K))
    (hc : HasCompactSupport (Function.uncurry K)) :
    ∃ C : ℝ≥0, ∀ y, LipschitzWith C (fun s => K s y) := by
  obtain ⟨C,hC⟩ := compact_smooth_lipschitz hK hc
  refine ⟨C, fun y => ?_⟩
  have hp : LipschitzWith 1 (fun s : ℝ => (s,y)) := by
    simpa using (LipschitzWith.id.prodMk (LipschitzWith.const y))
  simpa only [mul_one, Function.comp_def, Function.uncurry] using hC.comp hp

end ThreeTorus
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace ThreeTorus

private def samplingWindow (x : ℝ) (M : ℕ) : Finset ℤ :=
  Finset.Icc (⌊x⌋-(M:ℤ)-1) (⌊x⌋+(M:ℤ)+1)

private lemma mem_samplingWindow {x : ℝ} {M : ℕ} {j : ℤ}
    (hj : |x-j| ≤ M) : j ∈ samplingWindow x M := by
  have hf := Int.floor_le x
  have hf' := Int.lt_floor_add_one x
  have ha := abs_le.mp hj
  simp only [samplingWindow, Finset.mem_Icc]
  constructor
  · have : (⌊x⌋:ℝ)-(M:ℝ)-1 ≤ j := by linarith
    exact_mod_cast this
  · have : (j:ℝ) ≤ (⌊x⌋:ℝ)+(M:ℝ)+1 := by linarith
    exact_mod_cast this

private lemma samplingWindow_card (x : ℝ) (M : ℕ) :
    (samplingWindow x M).card = 2*M+3 := by
  rw [samplingWindow, Int.card_Icc]
  have he : ⌊x⌋+(M:ℤ)+1+1-(⌊x⌋-(M:ℤ)-1) = ((2*M+3:ℕ):ℤ) := by push_cast; ring
  rw [he, Int.toNat_natCast]

/-- Before freezing the slow coordinate, the exact rescaled kernel density. -/
def sampledKernel (K : ℝ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∑' j : ℤ, K (j/(n:ℝ)) ((n:ℝ)*t-j)

/-- The fine density has the same fast argument and the slow argument frozen at t. -/
def fineKernel (K : ℝ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∑' j : ℤ, K t ((n:ℝ)*t-j)

lemma sampledKernel_error {K : ℝ → ℝ → ℝ} {C : ℝ≥0} {M n : ℕ}
    (hK : ∀ y, LipschitzWith C (fun s => K s y))
    (hKy : ∀ s y, (M:ℝ) < |y| → K s y = 0)
    (hn : 0 < n) (t : ℝ) :
    |sampledKernel K n t-fineKernel K n t| ≤ (2*(M:ℝ)+3)*C*M/n := by
  classical
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  let S := samplingWindow ((n:ℝ)*t) M
  have hc (j : ℤ) (hj : j ∉ S) : (M:ℝ) < |(n:ℝ)*t-j| := by
    by_contra hh
    exact hj (mem_samplingWindow (not_lt.mp hh))
  have hs : sampledKernel K n t = ∑ j ∈ S, K (j/(n:ℝ)) ((n:ℝ)*t-j) := by
    exact tsum_eq_sum (fun j hj => hKy _ _ (hc j hj))
  have hf : fineKernel K n t = ∑ j ∈ S, K t ((n:ℝ)*t-j) := by
    exact tsum_eq_sum (fun j hj => hKy _ _ (hc j hj))
  rw [hs,hf,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ S, |K (j/(n:ℝ)) ((n:ℝ)*t-j)-K t ((n:ℝ)*t-j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ S, (C:ℝ)*M/n := by
      apply Finset.sum_le_sum
      intro j _hj
      by_cases hj : |(n:ℝ)*t-j| ≤ M
      · have hdist : |(j:ℝ)/(n:ℝ)-t| ≤ (M:ℝ)/n := by
          rw [show (j:ℝ)/(n:ℝ)-t = -((n:ℝ)*t-j)/(n:ℝ) by field_simp; ring,
            abs_div, abs_neg, abs_of_pos hn']
          exact div_le_div_of_nonneg_right hj hn'.le
        calc
          _ ≤ (C:ℝ)*|(j:ℝ)/(n:ℝ)-t| := by
            simpa only [Real.dist_eq] using (hK ((n:ℝ)*t-j)).dist_le_mul (j/(n:ℝ)) t
          _ ≤ (C:ℝ)*((M:ℝ)/n) := mul_le_mul_of_nonneg_left hdist C.coe_nonneg
          _ = _ := by ring
      · rw [hKy _ _ (lt_of_not_ge hj), hKy _ _ (lt_of_not_ge hj), sub_self, abs_zero]
        positivity
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, samplingWindow_card]; push_cast; ring

lemma fineKernel_eq_zero {K : ℝ → ℝ → ℝ} {A : ℝ}
    (hKs : ∀ s y, A < |s| → K s y = 0) {t : ℝ} (ht : A < |t|) (n : ℕ) :
    fineKernel K n t = 0 := by
  unfold fineKernel
  simp only [hKs _ _ ht, tsum_zero]

lemma sampledKernel_eq_zero {K : ℝ → ℝ → ℝ} {A : ℝ} {M n : ℕ}
    (hKs : ∀ s y, A < |s| → K s y = 0)
    (hKy : ∀ s y, (M:ℝ) < |y| → K s y = 0)
    (hn : 0 < n) {t : ℝ} (ht : A+M < |t|) : sampledKernel K n t = 0 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  unfold sampledKernel
  suffices he : ∀ j : ℤ, K (j/(n:ℝ)) ((n:ℝ)*t-j) = 0 by simp only [he, tsum_zero]
  intro j
  by_cases hs : A < |(j:ℝ)/(n:ℝ)|
  · exact hKs _ _ hs
  apply hKy
  by_contra hh
  have hj : |(n:ℝ)*t-j| ≤ M := not_lt.mp hh
  have ht' : |t| ≤ |(j:ℝ)/(n:ℝ)|+|(n:ℝ)*t-j|/(n:ℝ) := by
    calc
      _ = |(j:ℝ)/(n:ℝ)+((n:ℝ)*t-j)/(n:ℝ)| := by congr 1; field_simp; ring
      _ ≤ _ := by simpa only [abs_div,abs_of_pos hn'] using abs_add_le ((j:ℝ)/(n:ℝ)) (((n:ℝ)*t-j)/(n:ℝ))
  have hdiv : |(n:ℝ)*t-j|/(n:ℝ) ≤ (M:ℝ) := by
    apply (div_le_iff₀ hn').mpr
    exact hj.trans (by nlinarith)
  linarith [not_lt.mp hs]

/-- Strong L¹ replacement of the slow variable, rather than weak convergence. -/
lemma sampledKernel_integral_error {K : ℝ → ℝ → ℝ} {C : ℝ≥0} {A : ℝ} {M n : ℕ}
    (hA : 0 ≤ A) (hK : ∀ y, LipschitzWith C (fun s => K s y))
    (hKs : ∀ s y, A < |s| → K s y = 0)
    (hKy : ∀ s y, (M:ℝ) < |y| → K s y = 0)
    (hn : 0 < n)
    (hi : Integrable (fun t => |sampledKernel K n t-fineKernel K n t|)) :
    (∫ t, |sampledKernel K n t-fineKernel K n t|) ≤
      (2*(A+M))*((2*(M:ℝ)+3)*C*M/n) := by
  let B := A+M
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hs : Function.support (fun t => |sampledKernel K n t-fineKernel K n t|) ⊆ Icc (-B) B := by
    intro t ht
    by_contra hh
    have hab : B < |t| := lt_of_not_ge (by simpa only [abs_le,mem_Icc,not_and_or] using hh)
    have htA : A < |t| := lt_of_le_of_lt (by dsimp [B]; exact le_add_of_nonneg_right (Nat.cast_nonneg M)) hab
    exact ht (by dsimp only; rw [sampledKernel_eq_zero hKs hKy hn hab, fineKernel_eq_zero hKs htA, sub_self,abs_zero])
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-B) B)
    (f := fun t => |sampledKernel K n t-fineKernel K n t|) (fun x hx => by
      by_contra he
      exact hx (hs he))]
  calc
    _ ≤ ∫ _ in Icc (-B) B, (2*(M:ℝ)+3)*C*M/n :=
      setIntegral_mono_on hi.integrableOn (integrableOn_const (by simp)) measurableSet_Icc
        (fun t _ => sampledKernel_error hK hKy hn t)
    _ = _ := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith : -B ≤ B)]
      simp only [smul_eq_mul]
      dsimp [B]
      ring

lemma continuous_sampledKernel {K : ℝ → ℝ → ℝ} {A : ℝ} {n : ℕ}
    (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (hKs : ∀ s y, A < |s| → K s y = 0) (hn : 0 < n) :
    Continuous (sampledKernel K n) := by
  classical
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  obtain ⟨B, hB⟩ := exists_nat_gt ((n:ℝ)*A)
  let S := samplingWindow 0 B
  have he (t : ℝ) : sampledKernel K n t = ∑ j ∈ S, K (j/(n:ℝ)) ((n:ℝ)*t-j) := by
    apply tsum_eq_sum
    intro j hj
    apply hKs
    by_contra hh
    have hj' : |(j:ℝ)| < B := by
      have : |(j:ℝ)|/(n:ℝ) ≤ A := by simpa only [abs_div, abs_of_pos hn'] using not_lt.mp hh
      have := (div_le_iff₀ hn').mp this
      nlinarith
    exact hj (mem_samplingWindow (by simpa only [zero_sub,abs_neg] using hj'.le))
  rw [show sampledKernel K n = fun t => ∑ j ∈ S, K (j/(n:ℝ)) ((n:ℝ)*t-j) from funext he]
  apply continuous_finsetSum
  intro j _
  exact hK.comp (show Continuous (fun t : ℝ => ((j:ℝ)/(n:ℝ), (n:ℝ)*t-j)) by fun_prop)

lemma continuous_fineKernel {K : ℝ → ℝ → ℝ} {A : ℝ} {M n : ℕ}
    (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (hKs : ∀ s y, A < |s| → K s y = 0)
    (hKy : ∀ s y, (M:ℝ) < |y| → K s y = 0) : Continuous (fineKernel K n) := by
  classical
  obtain ⟨B,hB⟩ := exists_nat_gt ((n:ℝ)*A+M)
  let S := samplingWindow 0 B
  have he (t : ℝ) : fineKernel K n t = ∑ j ∈ S, K t ((n:ℝ)*t-j) := by
    apply tsum_eq_sum
    intro j hj
    by_cases hs : A < |t|
    · exact hKs _ _ hs
    apply hKy
    by_contra hh
    have hj' : |(j:ℝ)| < B := by
      have hab : |(j:ℝ)| ≤ (n:ℝ)*|t|+|(n:ℝ)*t-j| := by
        calc
          _ = |(n:ℝ)*t-((n:ℝ)*t-j)| := by ring_nf
          _ ≤ |(n:ℝ)*t|+|(n:ℝ)*t-j| := abs_sub _ _
          _ = _ := by rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
      have := mul_le_mul_of_nonneg_left (not_lt.mp hs) (Nat.cast_nonneg n : (0:ℝ) ≤ n)
      linarith [not_lt.mp hh]
    exact hj (mem_samplingWindow (by simpa only [zero_sub,abs_neg] using hj'.le))
  rw [show fineKernel K n = fun t => ∑ j ∈ S, K t ((n:ℝ)*t-j) from funext he]
  apply continuous_finsetSum
  intro j _
  exact hK.comp (show Continuous (fun t : ℝ => (t, (n:ℝ)*t-j)) by fun_prop)

lemma integrable_sampledKernel_error {K : ℝ → ℝ → ℝ} {A : ℝ} {M n : ℕ}
    (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (hKs : ∀ s y, A < |s| → K s y = 0)
    (hKy : ∀ s y, (M:ℝ) < |y| → K s y = 0) (hn : 0 < n) :
    Integrable (fun t => |sampledKernel K n t-fineKernel K n t|) := by
  apply ((continuous_sampledKernel hK hKs hn).sub (continuous_fineKernel hK hKs hKy)).abs.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Icc (-(A+M)) (A+M)) isCompact_Icc
  intro t ht
  have hab : A+M < |t| := lt_of_not_ge (by simpa only [abs_le, mem_Icc,not_and_or] using ht)
  have htA : A < |t| := lt_of_le_of_lt (le_add_of_nonneg_right (Nat.cast_nonneg M)) hab
  change |sampledKernel K n t-fineKernel K n t| = 0
  rw [sampledKernel_eq_zero hKs hKy hn hab, fineKernel_eq_zero hKs htA,sub_self,abs_zero]

lemma tendsto_sampledKernel_error {K : ℝ → ℝ → ℝ} {C : ℝ≥0} {A : ℝ} {M : ℕ}
    (hA : 0 ≤ A) (hK : ∀ y, LipschitzWith C (fun s => K s y))
    (hCont : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (hKs : ∀ s y, A < |s| → K s y = 0)
    (hKy : ∀ s y, (M:ℝ) < |y| → K s y = 0) :
    Tendsto (fun n : ℕ => ∫ t, |sampledKernel K n t-fineKernel K n t|) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _)))
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    exact sampledKernel_integral_error hA hK hKs hKy hn (integrable_sampledKernel_error hCont hKs hKy hn)
  · simpa only [mul_zero] using (tendsto_const_nhds.mul
      (tendsto_const_div_atTop_nhds_zero_nat ((2*(M:ℝ)+3)*C*M)))

end ThreeTorus

namespace ThreeTorus

/-- Exact progression j=h+kP; no divisibility restriction on the passage integer. -/
def sampledResidueKernel (K : ℝ → ℝ → ℝ) (P : ℕ) (h : ℤ) (n : ℕ) (t : ℝ) : ℝ :=
  ∑' k : ℤ, K (((h:ℝ)+(k:ℝ)*P)/(n:ℝ)) ((n:ℝ)*t-h-k*P)

def fineResidueKernel (K : ℝ → ℝ → ℝ) (P : ℕ) (h : ℤ) (n : ℕ) (t : ℝ) : ℝ :=
  ∑' k : ℤ, K t ((n:ℝ)*t-h-k*P)

lemma residue_window_mem {P M n : ℕ} {h k : ℤ} {t : ℝ}
    (hP : 0 < P) (hy : |(n:ℝ)*t-h-k*P| ≤ M) :
    k ∈ samplingWindow (((n:ℝ)*t-h)/P) M := by
  have hP' : (0:ℝ) < P := by exact_mod_cast hP
  have hP1 : (1:ℝ) ≤ P := by exact_mod_cast hP
  apply mem_samplingWindow
  rw [show ((n:ℝ)*t-h)/P-k = ((n:ℝ)*t-h-k*P)/P by field_simp,
    abs_div,abs_of_pos hP']
  apply (div_le_iff₀ hP').mpr
  exact hy.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) M])

lemma sampledResidueKernel_error {K : ℝ → ℝ → ℝ} {C : ℝ≥0} {P M n : ℕ} {h : ℤ}
    (hK : ∀ y, LipschitzWith C (fun s => K s y))
    (hKy : ∀ s y, (M:ℝ) < |y| → K s y = 0)
    (hP : 0 < P) (hn : 0 < n) (t : ℝ) :
    |sampledResidueKernel K P h n t-fineResidueKernel K P h n t| ≤
      (2*(M:ℝ)+3)*C*M/n := by
  classical
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  let S := samplingWindow (((n:ℝ)*t-h)/P) M
  have hc (k : ℤ) (hk : k ∉ S) : (M:ℝ) < |(n:ℝ)*t-h-k*P| := by
    by_contra hh
    exact hk (residue_window_mem hP (not_lt.mp hh))
  have hs : sampledResidueKernel K P h n t =
      ∑ k ∈ S, K (((h:ℝ)+(k:ℝ)*P)/(n:ℝ)) ((n:ℝ)*t-h-k*P) :=
    tsum_eq_sum (fun k hk => hKy _ _ (hc k hk))
  have hf : fineResidueKernel K P h n t =
      ∑ k ∈ S, K t ((n:ℝ)*t-h-k*P) :=
    tsum_eq_sum (fun k hk => hKy _ _ (hc k hk))
  rw [hs,hf,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ S, |K (((h:ℝ)+(k:ℝ)*P)/(n:ℝ)) ((n:ℝ)*t-h-k*P)-
      K t ((n:ℝ)*t-h-k*P)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ S, (C:ℝ)*M/n := by
      apply Finset.sum_le_sum
      intro k _hk
      by_cases hk : |(n:ℝ)*t-h-k*P| ≤ M
      · have hd : |((h:ℝ)+(k:ℝ)*P)/(n:ℝ)-t| ≤ (M:ℝ)/n := by
          rw [show ((h:ℝ)+(k:ℝ)*P)/(n:ℝ)-t = -((n:ℝ)*t-h-k*P)/n by field_simp; ring,
            abs_div,abs_neg,abs_of_pos hn']
          exact div_le_div_of_nonneg_right hk hn'.le
        calc
          _ ≤ (C:ℝ)*|((h:ℝ)+(k:ℝ)*P)/n-t| := by
            simpa only [Real.dist_eq] using (hK ((n:ℝ)*t-h-k*P)).dist_le_mul (((h:ℝ)+(k:ℝ)*P)/n) t
          _ ≤ (C:ℝ)*((M:ℝ)/n) := mul_le_mul_of_nonneg_left hd C.coe_nonneg
          _ = _ := by ring
      · rw [hKy _ _ (lt_of_not_ge hk),hKy _ _ (lt_of_not_ge hk),sub_self,abs_zero]
        positivity
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,samplingWindow_card]; push_cast; ring

lemma fineResidueKernel_eq_zero {K : ℝ → ℝ → ℝ} {A t : ℝ}
    (hKs : ∀ s y, A < |s| → K s y = 0) (ht : A < |t|) (P n : ℕ) (h : ℤ) :
    fineResidueKernel K P h n t = 0 := by
  unfold fineResidueKernel
  simp only [hKs _ _ ht,tsum_zero]

lemma sampledResidueKernel_eq_zero {K : ℝ → ℝ → ℝ} {A t : ℝ} {M n : ℕ}
    (hKs : ∀ s y, A < |s| → K s y = 0)
    (hKy : ∀ s y, (M:ℝ) < |y| → K s y = 0)
    (hn : 0 < n) (ht : A+M < |t|) (P : ℕ) (h : ℤ) :
    sampledResidueKernel K P h n t = 0 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  unfold sampledResidueKernel
  suffices he : ∀ k : ℤ, K (((h:ℝ)+(k:ℝ)*P)/(n:ℝ)) ((n:ℝ)*t-h-k*P) = 0 by
    simp only [he,tsum_zero]
  intro k
  by_cases hs : A < |((h:ℝ)+(k:ℝ)*P)/(n:ℝ)|
  · exact hKs _ _ hs
  apply hKy
  by_contra hh
  have hk : |(n:ℝ)*t-h-k*P| ≤ M := not_lt.mp hh
  have ht' : |t| ≤ |((h:ℝ)+(k:ℝ)*P)/(n:ℝ)|+|(n:ℝ)*t-h-k*P|/(n:ℝ) := by
    calc
      _ = |((h:ℝ)+(k:ℝ)*P)/(n:ℝ)+((n:ℝ)*t-h-k*P)/(n:ℝ)| := by congr 1; field_simp; ring
      _ ≤ _ := by simpa only [abs_div,abs_of_pos hn'] using
        abs_add_le (((h:ℝ)+(k:ℝ)*P)/(n:ℝ)) (((n:ℝ)*t-h-k*P)/(n:ℝ))
  have hdiv : |(n:ℝ)*t-h-k*P|/(n:ℝ) ≤ (M:ℝ) := by
    apply (div_le_iff₀ hn').mpr
    exact hk.trans (by nlinarith)
  linarith [not_lt.mp hs]

end ThreeTorus

namespace ThreeTorus

private lemma residue_abs_bound {P : ℕ} (hP : 0 < P) (h k : ℤ) :
    |(k:ℝ)| ≤ |(h:ℝ)+k*P|+|(h:ℝ)| := by
  have hP1 : (1:ℝ) ≤ P := by exact_mod_cast hP
  calc
    _ ≤ |(k:ℝ)| * P := by nlinarith [abs_nonneg (k:ℝ)]
    _ = |(h:ℝ)+k*P-h| := by rw [show (h:ℝ)+k*P-h = k*P by ring,abs_mul,abs_of_nonneg (show (0:ℝ) ≤ P from Nat.cast_nonneg P)]
    _ ≤ _ := abs_sub _ _

lemma continuous_sampledResidueKernel {K : ℝ → ℝ → ℝ} {A : ℝ} {n P : ℕ} (h : ℤ)
    (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (hKs : ∀ s y, A < |s| → K s y = 0) (hn : 0 < n) (hP : 0 < P) :
    Continuous (sampledResidueKernel K P h n) := by
  classical
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  obtain ⟨B,hB⟩ := exists_nat_gt ((n:ℝ)*A+|(h:ℝ)|)
  let S := samplingWindow 0 B
  have he (t : ℝ) : sampledResidueKernel K P h n t =
      ∑ k ∈ S, K (((h:ℝ)+(k:ℝ)*P)/(n:ℝ)) ((n:ℝ)*t-h-k*P) := by
    apply tsum_eq_sum
    intro k hk
    apply hKs
    by_contra hh
    have ha : |(h:ℝ)+k*P| ≤ (n:ℝ)*A := by
      have hh' : |(h:ℝ)+k*P|/(n:ℝ) ≤ A := by simpa only [abs_div,abs_of_pos hn'] using not_lt.mp hh
      have := (div_le_iff₀ hn').mp hh'
      nlinarith
    have hk' : |(k:ℝ)| < B := lt_of_le_of_lt (residue_abs_bound hP h k) (by linarith)
    exact hk (mem_samplingWindow (by simpa only [zero_sub,abs_neg] using hk'.le))
  rw [show sampledResidueKernel K P h n = fun t =>
      ∑ k ∈ S, K (((h:ℝ)+(k:ℝ)*P)/(n:ℝ)) ((n:ℝ)*t-h-k*P) from funext he]
  apply continuous_finsetSum
  intro k _
  exact hK.comp (show Continuous (fun t : ℝ => (((h:ℝ)+(k:ℝ)*P)/(n:ℝ), (n:ℝ)*t-h-k*P)) by fun_prop)

lemma continuous_fineResidueKernel {K : ℝ → ℝ → ℝ} {A : ℝ} {M n P : ℕ} (h : ℤ)
    (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (hKs : ∀ s y, A < |s| → K s y = 0)
    (hKy : ∀ s y, (M:ℝ) < |y| → K s y = 0) (hP : 0 < P) :
    Continuous (fineResidueKernel K P h n) := by
  classical
  obtain ⟨B,hB⟩ := exists_nat_gt ((n:ℝ)*A+M+|(h:ℝ)|)
  let S := samplingWindow 0 B
  have he (t : ℝ) : fineResidueKernel K P h n t =
      ∑ k ∈ S, K t ((n:ℝ)*t-h-k*P) := by
    apply tsum_eq_sum
    intro k hk
    by_cases hs : A < |t|
    · exact hKs _ _ hs
    apply hKy
    by_contra hh
    have ha : |(h:ℝ)+k*P| ≤ (n:ℝ)*A+M := by
      calc
        _ = |(n:ℝ)*t-((n:ℝ)*t-h-k*P)| := by congr 1; ring
        _ ≤ |(n:ℝ)*t|+|(n:ℝ)*t-h-k*P| := abs_sub _ _
        _ ≤ _ := by
          rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n)]
          exact add_le_add (mul_le_mul_of_nonneg_left (not_lt.mp hs) (Nat.cast_nonneg n)) (not_lt.mp hh)
    have hk' : |(k:ℝ)| < B := lt_of_le_of_lt (residue_abs_bound hP h k) (by linarith)
    exact hk (mem_samplingWindow (by simpa only [zero_sub,abs_neg] using hk'.le))
  rw [show fineResidueKernel K P h n = fun t => ∑ k ∈ S, K t ((n:ℝ)*t-h-k*P) from funext he]
  apply continuous_finsetSum
  intro k _
  exact hK.comp (show Continuous (fun t : ℝ => (t, (n:ℝ)*t-h-k*P)) by fun_prop)

lemma integrable_sampledResidueKernel_error {K : ℝ → ℝ → ℝ} {A : ℝ} {M n P : ℕ} (h : ℤ)
    (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (hKs : ∀ s y, A < |s| → K s y = 0)
    (hKy : ∀ s y, (M:ℝ) < |y| → K s y = 0) (hn : 0 < n) (hP : 0 < P) :
    Integrable (fun t => |sampledResidueKernel K P h n t-fineResidueKernel K P h n t|) := by
  apply ((continuous_sampledResidueKernel h hK hKs hn hP).sub
    (continuous_fineResidueKernel h hK hKs hKy hP)).abs.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Icc (-(A+M)) (A+M)) isCompact_Icc
  intro t ht
  have hab : A+M < |t| := lt_of_not_ge (by simpa only [abs_le,mem_Icc,not_and_or] using ht)
  have htA : A < |t| := lt_of_le_of_lt (le_add_of_nonneg_right (Nat.cast_nonneg M)) hab
  change |sampledResidueKernel K P h n t-fineResidueKernel K P h n t| = 0
  rw [sampledResidueKernel_eq_zero hKs hKy hn hab, fineResidueKernel_eq_zero hKs htA,sub_self,abs_zero]

lemma sampledResidueKernel_integral_error {K : ℝ → ℝ → ℝ} {C : ℝ≥0} {A : ℝ} {M n P : ℕ} (h : ℤ)
    (hA : 0 ≤ A) (hK : ∀ y, LipschitzWith C (fun s => K s y))
    (hCont : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (hKs : ∀ s y, A < |s| → K s y = 0)
    (hKy : ∀ s y, (M:ℝ) < |y| → K s y = 0)
    (hn : 0 < n) (hP : 0 < P) :
    (∫ t, |sampledResidueKernel K P h n t-fineResidueKernel K P h n t|) ≤
      (2*(A+M))*((2*(M:ℝ)+3)*C*M/n) := by
  let B := A+M
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hi := integrable_sampledResidueKernel_error h hCont hKs hKy hn hP
  have hs : Function.support (fun t => |sampledResidueKernel K P h n t-fineResidueKernel K P h n t|) ⊆ Icc (-B) B := by
    intro t ht
    by_contra hh
    have hab : B < |t| := lt_of_not_ge (by simpa only [abs_le,mem_Icc,not_and_or] using hh)
    have htA : A < |t| := lt_of_le_of_lt (by dsimp [B]; exact le_add_of_nonneg_right (Nat.cast_nonneg M)) hab
    exact ht (by dsimp only; rw [sampledResidueKernel_eq_zero hKs hKy hn hab,
      fineResidueKernel_eq_zero hKs htA,sub_self,abs_zero])
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-B) B)
    (f := fun t => |sampledResidueKernel K P h n t-fineResidueKernel K P h n t|) (fun x hx => by
      by_contra he
      exact hx (hs he))]
  calc
    _ ≤ ∫ _ in Icc (-B) B, (2*(M:ℝ)+3)*C*M/n :=
      setIntegral_mono_on hi.integrableOn (integrableOn_const (by simp)) measurableSet_Icc
        (fun t _ => sampledResidueKernel_error hK hKy hP hn t)
    _ = _ := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith : -B ≤ B)]
      simp only [smul_eq_mul]
      dsimp [B]
      ring

lemma tendsto_sampledResidueKernel_error {K : ℝ → ℝ → ℝ} {C : ℝ≥0} {A : ℝ} {M P : ℕ} (h : ℤ)
    (hA : 0 ≤ A) (hK : ∀ y, LipschitzWith C (fun s => K s y))
    (hCont : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (hKs : ∀ s y, A < |s| → K s y = 0)
    (hKy : ∀ s y, (M:ℝ) < |y| → K s y = 0) (hP : 0 < P) :
    Tendsto (fun n : ℕ => ∫ t, |sampledResidueKernel K P h n t-fineResidueKernel K P h n t|) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _)))
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    exact sampledResidueKernel_integral_error h hA hK hCont hKs hKy hn hP
  · simpa only [mul_zero] using (tendsto_const_nhds.mul
      (tendsto_const_div_atTop_nhds_zero_nat ((2*(M:ℝ)+3)*C*M)))

end ThreeTorus

namespace ThreeTorus

/-- Fine-density freezing for the actual neutral affine jitter kernel. All
regularity hypotheses are derived from the smooth compact old coefficient. -/
lemma affineKernel_fine_density {F : ℝ × ℝ → ℝ} {L β A D ε : ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hL : 0 < L) (hA : 0 ≤ A) (hD : 0 ≤ D) (hε : 0 < ε)
    (hz : ∀ s a, |s| < ε → F (s,a) = 0)
    (hFs : ∀ s a, A < |s| → F (s,a) = 0)
    (hFa : ∀ s a, D < |a| → F (s,a) = 0)
    {P : ℕ} (hP : 0 < P) (h : ℤ) :
    Tendsto (fun n : ℕ => ∫ t,
      |sampledResidueKernel (affineKernel F L β) P h n t -
        fineResidueKernel (affineKernel F L β) P h n t|) atTop (𝓝 0) := by
  have hSm := affineKernel_smooth (L := L) (β := β) hF hε hz
  have hCp := affineKernel_hasCompactSupport (β := β) hL hA hD hFs hFa
  obtain ⟨C,hC⟩ := compact_smooth_kernel_lipschitz hSm hCp
  obtain ⟨M,hM⟩ := exists_nat_ge (A*(L*D+|β|))
  apply tendsto_sampledResidueKernel_error h hA hC hSm.continuous
    (fun s y hs => affineKernel_eq_zero_s hFs hs) (M := M) _ hP
  intro s y hy
  exact affineKernel_eq_zero_y hL hA hD hFs hFa (lt_of_le_of_lt hM hy)

/-- The transmitting kernel when the old coefficient modulus is independent
of the spare coordinate and its jitter law has density rho. -/
def signalKernel (W ρ : ℝ → ℝ) (s y : ℝ) : ℝ := W s / |s| * ρ (y/s)

lemma signalKernel_as_affine (W ρ : ℝ → ℝ) :
    signalKernel W ρ = affineKernel (fun p => W p.1*ρ p.2) 1 0 := by
  funext s y
  simp only [signalKernel,affineKernel,mul_one,sub_zero,div_one]
  ring

lemma signalKernel_fine_density {W ρ : ℝ → ℝ} {A D ε : ℝ}
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hε : 0 < ε)
    (hz : ∀ s, |s| < ε → W s = 0)
    (hWs : ∀ s, A < |s| → W s = 0)
    (hρs : ∀ a, D < |a| → ρ a = 0)
    {P : ℕ} (hP : 0 < P) (h : ℤ) :
    Tendsto (fun n : ℕ => ∫ t,
      |sampledResidueKernel (signalKernel W ρ) P h n t -
        fineResidueKernel (signalKernel W ρ) P h n t|) atTop (𝓝 0) := by
  rw [signalKernel_as_affine]
  exact affineKernel_fine_density
    ((hW.comp contDiff_fst).mul (hρ.comp contDiff_snd)) (by norm_num) hA hD hε
    (fun s a hs => by change W s*ρ a = 0; rw [hz s hs,zero_mul])
    (fun s a hs => by change W s*ρ a = 0; rw [hWs s hs,zero_mul])
    (fun s a ha => by change W s*ρ a = 0; rw [hρs a ha,mul_zero]) hP h

/-- General smooth jitter kernel. The source's old-frequency variable is the
second coordinate of F; the first is the new slow-coordinate good arc. -/
def passageBranchKernel (I : Set ℝ) (J : ℝ → ℝ) (F : ℝ × ℝ → ℝ) : ℝ → ℝ → ℝ :=
  affineKernel (fun p => branchKernel I J F (p.2,p.1)) 1 0

lemma passageBranchKernel_formula (I : Set ℝ) (J : ℝ → ℝ) (F : ℝ × ℝ → ℝ) (s y : ℝ) :
    passageBranchKernel I J F s y = |s|⁻¹*branchKernel I J F (y/s,s) := by
  simp [passageBranchKernel,affineKernel]

/-- Fine temporal sampling on any smooth monotone good arc, both signs,
all residue classes and all positive passage integers; no divisibility pin. -/
lemma passageBranchKernel_fine_density {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ I ×ˢ univ) {ε : ℝ} (hε : 0 < ε)
    (hz : ∀ a s, |s| < ε → F (a,s) = 0) {P : ℕ} (hP : 0 < P) (h : ℤ) :
    Tendsto (fun n : ℕ => ∫ t,
      |sampledResidueKernel (passageBranchKernel I J F) P h n t-
        fineResidueKernel (passageBranchKernel I J F) P h n t|) atTop (𝓝 0) := by
  have hSm := branchKernel_smooth hJ hIo hinj hd hF hc hs
  obtain ⟨D,A,hD,hA,hx,ha⟩ := branchKernel_bounds (I := I) hJ.continuous hc
  apply affineKernel_fine_density (hSm.comp (contDiff_snd.prodMk contDiff_fst)) (by norm_num) hA hD hε _
    (fun s a hs => ha a s hs) (fun s a hs => hx a s hs) hP h
  intro s a hs
  change branchKernel I J F (a,s) = 0
  simp [branchKernel,hz _ _ hs]

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

/-- The exact sampled leading density is the good-arc Jacobian kernel.
This identifies the coefficient-level approximation with the fine-density
calculation; it is an equality, not a new spectral hypothesis. -/
lemma unfoldedModeDensity_stationary (I : Set ℝ) (J : ℝ → ℝ)
    (F : ℝ × ℝ → ℝ) {n : ℝ} (hn : n ≠ 0) (j t : ℝ) :
    unfoldedModeDensity I J (invFunOn J I) (deriv J)
      (fun a => n⁻¹*F (a,j/n)) n j t =
      passageBranchKernel I J F (j/n) (n*t-j) := by
  classical
  rw [passageBranchKernel_formula]
  unfold unfoldedModeDensity scaledBranchKernel branchDensity branchKernel
  by_cases hy : (n*t-j)/(j/n) ∈ J '' I
  · simp only [hy, ite_eq_left, indicator_of_mem, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  · simp [hy]

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma finite_unfolded_index_error {ι : Type*} {I : Set ℝ} {J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o n : ℝ} (hn : 0 < n)
    (S : Finset ι) (index : ι → ℤ) (hS : ∀ i ∈ S, index i ≠ 0)
    {q w : ι → UnitAddCircle → ℝ} {q₀ w₀ : ι → ℝ → ℝ}
    (hq : ∀ i ∈ S, Integrable (q i) AddCircle.haarAddCircle)
    (hw : ∀ i ∈ S, Integrable (w i) AddCircle.haarAddCircle)
    (hq₀ : ∀ i ∈ S, ∀ x ∈ Ioc o (o+1), q i (x : UnitAddCircle) = q₀ i x)
    (hw₀ : ∀ i ∈ S, ∀ x ∈ Ioc o (o+1), w i (x : UnitAddCircle) = w₀ i x)
    (hqs : ∀ i ∈ S, Function.support (q₀ i) ⊆ Ioc o (o+1) ∩ I)
    (hws : ∀ i ∈ S, Function.support (w₀ i) ⊆ Ioc o (o+1) ∩ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0) :
    (∫ t, |(∑ i ∈ S, unfoldedModeDensity I J₀ g D (q₀ i) n (index i) t)-
      (∑ i ∈ S, unfoldedModeDensity I J₀ g D (w₀ i) n (index i) t)|) ≤
       ∑ i ∈ S, ∫ a, |q i a-w i a| ∂AddCircle.haarAddCircle := by
  have hqI (i : ι) (his : i ∈ S) : Integrable (q₀ i) := by
    rw [← circleDensityLift_eq (hq₀ i his) ((hqs i his).trans inter_subset_left)]
    exact integrable_circleDensityLift (hq i his) o
  have hwI (i : ι) (his : i ∈ S) : Integrable (w₀ i) := by
    rw [← circleDensityLift_eq (hw₀ i his) ((hws i his).trans inter_subset_left)]
    exact integrable_circleDensityLift (hw i his) o
  have hjn (i : ι) (his : i ∈ S) : (index i:ℝ) ≠ 0 := by exact_mod_cast hS i his
  apply finite_density_sum_error
    (g := fun i => unfoldedModeDensity I J₀ g D (q₀ i) n (index i))
    (h := fun i => unfoldedModeDensity I J₀ g D (w₀ i) n (index i)) S hq hw
    (fun i hi => integrable_unfoldedModeDensity hI himage hJ hinj hg hD (hqI i hi) hn (hjn i hi))
    (fun i hi => integrable_unfoldedModeDensity hI himage hJ hinj hg hD (hwI i hi) hn (hjn i hi))
    (T := fun i a => ((index i:ℝ)+((index i:ℝ)/n)*J a)/n)
  · intro i _hi
    fun_prop
  · intro i his
    exact unfoldedModeDensity_pushforward (hq i his) (hq₀ i his)
      ((hqs i his).trans inter_subset_left) ((hqs i his).trans inter_subset_right)
      hj hj₀ hJe hI himage hJ hinj hg hD hn (hjn i his)
  · intro i his
    exact unfoldedModeDensity_pushforward (hw i his) (hw₀ i his)
      ((hws i his).trans inter_subset_left) ((hws i his).trans inter_subset_right)
      hj hj₀ hJe hI himage hJ hinj hg hD hn (hjn i his)

lemma leading_unfolded_residue_eq_sampled
    (I : Set ℝ) (J : ℝ → ℝ) (F : ℝ × ℝ → ℝ)
    {n : ℕ} (hn : 0 < n) (P : ℕ) (h : ℤ) (S : Finset ℤ)
    (hS : ∀ k ∉ S, ∀ a, F (a,((h+k*(P:ℤ):ℤ):ℝ)/n) = 0) (t : ℝ) :
    (∑ k ∈ S, unfoldedModeDensity I J (invFunOn J I) (deriv J)
      (fun a => (n:ℝ)⁻¹*F (a,((h+k*(P:ℤ):ℤ):ℝ)/n)) n ((h+k*(P:ℤ):ℤ):ℝ) t) =
      sampledResidueKernel (passageBranchKernel I J F) P h n t := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp_rw [unfoldedModeDensity_stationary I J F hn']
  unfold sampledResidueKernel
  have he (k : ℤ) : (n:ℝ)*t-((h+k*(P:ℤ):ℤ):ℝ) = (n:ℝ)*t-h-k*P := by push_cast; ring
  simp_rw [he,Int.cast_add,Int.cast_mul,Int.cast_natCast]
  symm
  apply tsum_eq_sum
  intro k hk
  rw [passageBranchKernel_formula]
  have hz (a : ℝ) : F (a,((h:ℝ)+k*P)/n) = 0 := by
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast] using hS k hk a
  simp [branchKernel,hz]

lemma integral_abs_triangle {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g h : X → ℝ} (hfg : Integrable (fun x => |f x-g x|) μ)
    (hgh : Integrable (fun x => |g x-h x|) μ) :
    (∫ x, |f x-h x| ∂μ) ≤ (∫ x, |f x-g x| ∂μ)+(∫ x, |g x-h x| ∂μ) := by
  calc
    _ ≤ ∫ x, |f x-g x|+|g x-h x| ∂μ := integral_mono_of_nonneg
      (Eventually.of_forall (fun _ => abs_nonneg _)) (hfg.add hgh)
      (Eventually.of_forall (fun x => by
        calc
          |f x-h x| = |(f x-g x)+(g x-h x)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _))
    _ = _ := integral_add hfg hgh

lemma passageBranchKernel_integrable_error {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ I ×ˢ univ) {ε : ℝ} (hε : 0 < ε)
    (hz : ∀ a s, |s| < ε → F (a,s) = 0) {P n : ℕ} (hP : 0 < P)
    (hn : 0 < n) (h : ℤ) :
    Integrable (fun t =>
      |sampledResidueKernel (passageBranchKernel I J F) P h n t-
        fineResidueKernel (passageBranchKernel I J F) P h n t|) := by
  have hSm := branchKernel_smooth hJ hIo hinj hd hF hc hs
  obtain ⟨D,A,hD,hA,hx,ha⟩ := branchKernel_bounds (I := I) hJ.continuous hc
  have hsmooth := affineKernel_smooth (L := (1:ℝ)) (β := (0:ℝ))
    (hSm.comp (contDiff_snd.prodMk contDiff_fst)) hε (show
      ∀ s a, |s| < ε → branchKernel I J F (a,s) = 0 from fun s a hh => by
        simp [branchKernel,hz _ _ hh])
  obtain ⟨M,hM⟩ := exists_nat_ge (A*((1:ℝ)*D+|(0:ℝ)|))
  apply integrable_sampledResidueKernel_error h hsmooth.continuous
    (fun s y hh => affineKernel_eq_zero_s (fun s a hh => ha a s hh) hh)
    (M := M) _ hn hP
  intro s y hy
  exact affineKernel_eq_zero_y (by norm_num) hA hD
    (fun s a hh => ha a s hh) (fun s a hh => hx a s hh) (lt_of_le_of_lt hM hy)

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma sum_residue_le_tsum {E : ℤ → ℝ} (hE : Summable E) (hE0 : ∀ j, 0 ≤ E j)
    {P : ℕ} (hP : 0 < P) (h : ℤ) (S : Finset ℤ) :
    (∑ k ∈ S, E (h+k*(P:ℤ))) ≤ ∑' j : ℤ, E j := by
  have hinj : Injective (fun k : ℤ => h+k*(P:ℤ)) := by
    intro k l he
    exact mul_right_cancel₀ (show (P:ℤ) ≠ 0 by exact_mod_cast hP.ne')
      (add_left_cancel he)
  rw [← Finset.sum_image (fun k _ l _ he => hinj he)]
  exact Summable.sum_le_tsum _ (fun j _ => hE0 j) hE

/-- Full finite retained residue density estimate, at the actual spectral
pushforwards. The right-hand side consists only of coefficient mass error and
the already proved explicit slow-variable freezing error. -/
lemma unfolded_residue_density_error
    {I : Set ℝ} {J₀ : ℝ → ℝ} {J : UnitAddCircle → ℝ} {o : ℝ}
    {F : ℝ × ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀) (hIo : IsOpen I)
    (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ I ×ˢ univ) {ε : ℝ} (hε : 0 < ε)
    (hz : ∀ a s, |s| < ε → F (a,s) = 0)
    (hj : Measurable J) (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    {n P : ℕ} (hn : 0 < n) (hP : 0 < P) (h : ℤ) (S : Finset ℤ)
    (hSN : ∀ k ∈ S, h+k*(P:ℤ) ≠ 0)
    (hST : ∀ k ∉ S, ∀ a, F (a,((h+k*(P:ℤ):ℤ):ℝ)/n) = 0)
    {q w : ℤ → UnitAddCircle → ℝ} {q₀ : ℤ → ℝ → ℝ}
    (hq : ∀ k ∈ S, Integrable (q (h+k*(P:ℤ))) AddCircle.haarAddCircle)
    (hw : ∀ k ∈ S, Integrable (w (h+k*(P:ℤ))) AddCircle.haarAddCircle)
    (hq₀ : ∀ k ∈ S, ∀ x ∈ Ioc o (o+1), q (h+k*(P:ℤ)) (x : UnitAddCircle) = q₀ (h+k*(P:ℤ)) x)
    (hw₀ : ∀ k ∈ S, ∀ x ∈ Ioc o (o+1), w (h+k*(P:ℤ)) (x : UnitAddCircle) =
      (n:ℝ)⁻¹*F (x,((h+k*(P:ℤ):ℤ):ℝ)/n))
    (hqs : ∀ k ∈ S, support (q₀ (h+k*(P:ℤ))) ⊆ Ioc o (o+1) ∩ I)
    (hws : ∀ k ∈ S, support (fun a => (n:ℝ)⁻¹*F (a,((h+k*(P:ℤ):ℤ):ℝ)/n)) ⊆ Ioc o (o+1) ∩ I)
    {E : ℤ → ℝ} (hE : Summable E) (hE0 : ∀ j, 0 ≤ E j)
    (hEB : ∀ k ∈ S, (∫ a, |q (h+k*(P:ℤ)) a-w (h+k*(P:ℤ)) a|
      ∂AddCircle.haarAddCircle) ≤ E (h+k*(P:ℤ))) :
    (∫ t, |(∑ k ∈ S, unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
        (q₀ (h+k*(P:ℤ))) n ((h+k*(P:ℤ):ℤ):ℝ) t)-
      fineResidueKernel (passageBranchKernel I J₀ F) P h n t|) ≤
    (∑' j : ℤ, E j) +
      ∫ t, |sampledResidueKernel (passageBranchKernel I J₀ F) P h n t-
        fineResidueKernel (passageBranchKernel I J₀ F) P h n t| := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hJs (x : ℝ) (hx : x ∈ I) : HasDerivWithinAt J₀ (deriv J₀ x) I x :=
    ((hJ.differentiable (by simp)) x).hasDerivAt.hasDerivWithinAt
  have hg (x : ℝ) (hx : x ∈ I) : invFunOn J₀ I (J₀ x) = x := hinj.leftInvOn_invFunOn hx
  have him : MeasurableSet (J₀ '' I) := (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet
  let index : ℤ → ℤ := fun k => h+k*(P:ℤ)
  let w₀ : ℤ → ℝ → ℝ := fun j a => (n:ℝ)⁻¹*F (a,(j:ℝ)/n)
  have hLead (t : ℝ) := leading_unfolded_residue_eq_sampled I J₀ F hn P h S hST t
  have he : (∫ t, |(∑ k ∈ S, unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
        (q₀ (index k)) n (index k) t)-
      sampledResidueKernel (passageBranchKernel I J₀ F) P h n t|) ≤
      ∑ k ∈ S, ∫ a, |q (index k) a-w (index k) a| ∂AddCircle.haarAddCircle := by
    simp_rw [← hLead]
    exact finite_unfolded_index_error hn' S index hSN hq hw hq₀ hw₀ hqs hws
      hj hJ.continuous.measurable hJe hIo.measurableSet him hJs hinj hg hd
  have hqI (k : ℤ) (hk : k ∈ S) : Integrable (q₀ (index k)) := by
    rw [← circleDensityLift_eq (hq₀ k hk) ((hqs k hk).trans inter_subset_left)]
    exact integrable_circleDensityLift (hq k hk) o
  have hwI (k : ℤ) (hk : k ∈ S) : Integrable (w₀ (index k)) := by
    dsimp only [w₀, index]
    rw [← circleDensityLift_eq (hw₀ k hk) ((hws k hk).trans inter_subset_left)]
    exact integrable_circleDensityLift (hw k hk) o
  have hfg : Integrable (fun t => |(∑ k ∈ S,
      unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀) (q₀ (index k)) n (index k) t)-
      sampledResidueKernel (passageBranchKernel I J₀ F) P h n t|) := by
    simp_rw [← hLead]
    apply Integrable.abs
    apply Integrable.sub
    · apply integrable_finsetSum
      intro k hk
      exact integrable_unfoldedModeDensity hIo.measurableSet him hJs hinj hg hd (hqI k hk) hn'
        (by exact_mod_cast hSN k hk)
    · apply integrable_finsetSum
      intro k hk
      exact integrable_unfoldedModeDensity hIo.measurableSet him hJs hinj hg hd (hwI k hk) hn'
        (by exact_mod_cast hSN k hk)
  have hsamp := passageBranchKernel_integrable_error hJ hIo hinj hd hF hc hs hε hz hP hn h
  apply (integral_abs_triangle hfg hsamp).trans
  apply add_le_add _ le_rfl
  apply he.trans
  calc
    _ ≤ ∑ k ∈ S, E (index k) := Finset.sum_le_sum hEB
    _ ≤ _ := sum_residue_le_tsum hE hE0 hP h S

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma stationaryWeight_family_of_branch {Ω : Type*} {C I : Set ℝ}
    {J : ℝ → ℝ} {A : Ω → ℝ → ℂ}
    (hIC : I ⊆ C) (hi : InjOn J C) (hs : ∀ a, support (A a) ⊆ I) :
    (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily I J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
  have he (C : Set ℝ) :
      (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily C J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
    funext p
    simp only [stationaryWeight,branchDensity,branchFamily]
    split_ifs with h <;> simp [h]
  rw [he]
  apply branchFamily_congr_branch hIC hi
  intro p hp
  refine ⟨hs p.2 ?_,mem_univ _⟩
  intro hz
  apply hp
  simp [hz]

lemma stationaryWeight_signed_compact_continuous {J : ℝ → ℝ}
    {A : UnitAddCircle → ℝ → ℂ} {l u R : ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hA : Continuous A.uncurry) (hs : ∀ a, support (A a) ⊆ Icc l u)
    (hR : 0 < R) (hi : InjOn J (Icc (l-R) (u+R)))
    (hd : ∀ x ∈ Ioo (l-R) (u+R), deriv J x ≠ 0) :
    Continuous (fun p : ℝ × UnitAddCircle => stationaryWeight (Icc (l-R) (u+R)) J (A p.2) p.1) ∧
    HasCompactSupport (fun p : ℝ × UnitAddCircle => stationaryWeight (Icc (l-R) (u+R)) J (A p.2) p.1) := by
  let F : ℝ × UnitAddCircle → ℝ := fun p => ‖A p.2 p.1‖^2
  have hF : Continuous F := (hA.comp (continuous_snd.prodMk continuous_fst)).norm.pow 2
  have hFs : support F ⊆ Icc l u ×ˢ (univ : Set UnitAddCircle) := by
    intro p hp
    refine ⟨hs p.2 ?_,mem_univ _⟩
    intro hz
    exact hp (by simp [F,show A p.2 p.1 = 0 from hz])
  have hFt : tsupport F ⊆ Icc l u ×ˢ (univ : Set UnitAddCircle) :=
    closure_minimal hFs (isClosed_Icc.prod isClosed_univ)
  have hc : HasCompactSupport F :=
    (isCompact_Icc.prod isCompact_univ).of_isClosed_subset (isClosed_tsupport F) hFt
  have hsub : Icc l u ⊆ Ioo (l-R) (u+R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  rw [stationaryWeight_family_of_branch Ioo_subset_Icc_self hi (fun a => (hs a).trans hsub)]
  exact ⟨branchFamily_continuous hJ isOpen_Ioo (hi.mono Ioo_subset_Icc_self) hd hF hc
    (fun p hp => ⟨hsub (hFt hp).1,mem_univ _⟩),branchFamily_compact hJ.continuous hc⟩

/-- Smoothness of the actual old-frequency Jacobian, with a compactly
supported real lift of the old amplitude (including the new good-arc cutoff).
Both positive and negative angular indices are allowed by the injective branch. -/
lemma stationaryWeight_smooth_lift {C I : Set ℝ} {J : ℝ → ℝ} {B : ℝ × ℝ → ℂ}
    (hIC : I ⊆ C) (hi : InjOn J C)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B) (hc : HasCompactSupport B)
    (hs : tsupport B ⊆ I ×ˢ univ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => stationaryWeight C J (fun x => B (x,p.2)) p.1) ∧
    HasCompactSupport (fun p : ℝ × ℝ => stationaryWeight C J (fun x => B (x,p.2)) p.1) := by
  let F : ℝ × ℝ → ℝ := fun p => ‖B p‖^2
  have hFt : tsupport F ⊆ tsupport B := by
    apply closure_mono
    intro p hp hz
    exact hp (by simp [F,show B p = 0 from hz])
  have hFc : HasCompactSupport F := hc.of_isClosed_subset (isClosed_tsupport F) hFt
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := hB.norm_sq (𝕜 := ℂ)
  have hA (a : ℝ) : support (fun x => B (x,a)) ⊆ I := by
    intro x hx
    exact (hs (subset_tsupport B hx)).1
  have he := stationaryWeight_family_of_branch (A := fun a x => B (x,a)) hIC hi hA
  rw [he]
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (branchKernel I J F) ∧
    HasCompactSupport (branchKernel I J F)
  exact ⟨branchKernel_smooth hJ hIo (hi.mono hIC) hd hF hFc (hFt.trans hs),
    branchKernel_compact hJ.continuous hFc⟩

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

/-- A finite retained residue index set exists for every positive passage
integer. Its zero mode is excluded by the cutoff support, not by a limit. -/
lemma exists_retained_residue_indices {χ : ℝ → UnitAddCircle → ℝ}
    (hc : HasCompactSupport χ.uncurry) (hz : ∀ a, χ 0 a = 0)
    {n P : ℕ} (hn : 0 < n) (hP : 0 < P) (h : ℤ) :
    ∃ S : Finset ℤ, (∀ k ∈ S, h+k*(P:ℤ) ≠ 0) ∧
      ∀ k ∉ S, ∀ a, χ (((h+k*(P:ℤ):ℤ):ℝ)/n) a = 0 := by
  classical
  obtain ⟨T,hT⟩ := compact_lattice_support hc hn 0
  have hinj : Injective (fun k : ℤ => h+k*(P:ℤ)) := by
    intro k l he
    exact mul_right_cancel₀ (show (P:ℤ) ≠ 0 by exact_mod_cast hP.ne') (add_left_cancel he)
  have hf := T.finite_toSet.preimage hinj.injOn
  refine ⟨hf.toFinset.filter (fun k => h+k*(P:ℤ) ≠ 0),?_,?_⟩
  · intro k hk
    exact (Finset.mem_filter.mp hk).2
  · intro k hk a
    by_cases hj : h+k*(P:ℤ) = 0
    · simp [hj,hz]
    · have hk' : h+k*(P:ℤ) ∉ T := by
        intro hkT
        exact hk (Finset.mem_filter.mpr ⟨hf.mem_toFinset.mpr hkT,hj⟩)
      simpa using hT (h+k*(P:ℤ)) hk' a

/-- The exact circle weights of one retained passage mode. -/
noncomputable def retainedCircleWeight (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (c : ℕ → ℤ → UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) (a : UnitAddCircle) : ℝ :=
  ψ a^2*χ ((j:ℝ)/n) a^2*‖c n j a‖^2

lemma retainedCircleWeight_integrable {ψ : UnitAddCircle → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry) (hc : ∀ n j, Continuous (c n j))
    (n : ℕ) (j : ℤ) :
    Integrable (retainedCircleWeight ψ χ c n j) AddCircle.haarAddCircle := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  exact ((hψ.pow 2).mul ((hχ.comp (continuous_const.prodMk continuous_id)).pow 2)).mul
    ((hc n j).norm.pow 2)

lemma retainedCircleWeight_error {ψ : UnitAddCircle → ℝ}
    {χ W : ℝ → UnitAddCircle → ℝ} {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1) (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, W s a ≠ 0 → χ s a = 1)
    (hW : Continuous W.uncurry) (hc : ∀ n j, Continuous (c n j))
    (n : ℕ) (j : ℤ) :
    (∫ a, |retainedCircleWeight ψ χ c n j a-ψ a^2*((n:ℝ)⁻¹*W ((j:ℝ)/n) a)|
      ∂AddCircle.haarAddCircle) ≤
    ∫ a, |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle := by
  apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => abs_nonneg _))
  · exact ((((hc n j).norm.pow 2).sub (continuous_const.mul
      (hW.comp (continuous_const.prodMk continuous_id)))).abs).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · filter_upwards [] with a
    exact cutoff_mass_pointwise (sq_nonneg _) (hχ _ a)
      (fun hh => hχW _ a (fun hw => hh (by rw [hw,mul_zero]))) (hψ a)

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

/-- Full L1 unfolded fine-density convergence for actual retained mode weights.
The only asymptotic input is the summed Fourier coefficient mass theorem;
all pushforward identities, integrability, cutoffs and residue freezing are
proved here, for both signs and without any divisibility constraint on n. -/
lemma retained_unfolded_residue_error
    {I : Set ℝ} {J₀ : ℝ → ℝ} {J : UnitAddCircle → ℝ} {o : ℝ}
    {F : ℝ × ℝ → ℝ} {W χ : ℝ → UnitAddCircle → ℝ}
    {ψ : UnitAddCircle → ℝ} {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀) (hIo : IsOpen I)
    (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hcF : HasCompactSupport F)
    (hsF : tsupport F ⊆ (Ioc o (o+1) ∩ I) ×ˢ univ)
    {ε : ℝ} (hε : 0 < ε) (hz : ∀ a s, |s| < ε → F (a,s) = 0)
    (hj : Measurable J) (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hW : Continuous W.uncurry) (hcW : HasCompactSupport W.uncurry)
    (hcc : ∀ n j, Continuous (c n j))
    (hcs : ∀ n, Summable (fun j => ∫ a, ‖c n j a‖^2 ∂AddCircle.haarAddCircle))
    (hψc : Continuous ψ) (hχc : Continuous χ.uncurry)
    (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1) (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, W s a ≠ 0 → χ s a = 1)
    (hψS : ∀ x ∈ Ioc o (o+1), ψ (x : UnitAddCircle) ≠ 0 → x ∈ I)
    (hFlift : ∀ x ∈ Ioc o (o+1), ∀ s,
      F (x,s) = ψ (x : UnitAddCircle)^2*W s (x : UnitAddCircle))
    {n P : ℕ} (hn : 0 < n) (hP : 0 < P) (h : ℤ) (S : Finset ℤ)
    (hSN : ∀ k ∈ S, h+k*(P:ℤ) ≠ 0)
    (hST : ∀ k ∉ S, ∀ a, χ (((h+k*(P:ℤ):ℤ):ℝ)/n) a = 0) :
    (∫ t, |(∑ k ∈ S,
      unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
        (circleDensityLift o (retainedCircleWeight ψ χ c n (h+k*(P:ℤ))))
        n ((h+k*(P:ℤ):ℤ):ℝ) t)-
      fineResidueKernel (passageBranchKernel I J₀ F) P h n t|) ≤
    (∑' j : ℤ, ∫ a, |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) +
      ∫ t, |sampledResidueKernel (passageBranchKernel I J₀ F) P h n t-
        fineResidueKernel (passageBranchKernel I J₀ F) P h n t| := by
  have hsFI : tsupport F ⊆ I ×ˢ univ := fun p hp => ⟨(hsF hp).1.2,mem_univ _⟩
  let q : ℤ → UnitAddCircle → ℝ := retainedCircleWeight ψ χ c n
  let w : ℤ → UnitAddCircle → ℝ := fun j a => ψ a^2*((n:ℝ)⁻¹*W ((j:ℝ)/n) a)
  let E : ℤ → ℝ := fun j => ∫ a, |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a|
    ∂AddCircle.haarAddCircle
  have hEi : Summable E := by
    simpa [E] using integrated_array_mass_error_summable hW hcW (hcc n) (hcs n) hn 0
  have hq (j : ℤ) : Integrable (q j) AddCircle.haarAddCircle :=
    retainedCircleWeight_integrable hψc hχc hcc n j
  have hw (j : ℤ) : Integrable (w j) AddCircle.haarAddCircle :=
    ((hψc.pow 2).mul (continuous_const.mul
      (hW.comp (continuous_const.prodMk continuous_id)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hq₀ (j : ℤ) (x : ℝ) (hx : x ∈ Ioc o (o+1)) :
      q j (x : UnitAddCircle) = circleDensityLift o (q j) x := by
    simp only [circleDensityLift,indicator_of_mem hx]
  have hw₀ (j : ℤ) (x : ℝ) (hx : x ∈ Ioc o (o+1)) :
      w j (x : UnitAddCircle) = (n:ℝ)⁻¹*F (x,(j:ℝ)/n) := by
    rw [hFlift x hx]; dsimp [w]; ring
  have hqs (j : ℤ) : support (circleDensityLift o (q j)) ⊆ Ioc o (o+1) ∩ I := by
    intro x hx
    have hxI : x ∈ Ioc o (o+1) := by
      by_contra hh
      exact hx (by simp [circleDensityLift,hh])
    refine ⟨hxI,hψS x hxI ?_⟩
    intro hz
    exact hx (by simp [circleDensityLift,hxI,q,retainedCircleWeight,hz])
  have hws (j : ℤ) : support (fun a => (n:ℝ)⁻¹*F (a,(j:ℝ)/n)) ⊆ Ioc o (o+1) ∩ I := by
    intro a ha
    have hf : F (a,(j:ℝ)/n) ≠ 0 := fun hh => ha (by simp [hh])
    exact (hsF (subset_tsupport F hf)).1
  have hSTF (k : ℤ) (hk : k ∉ S) (a : ℝ) :
      F (a,((h+k*(P:ℤ):ℤ):ℝ)/n) = 0 := by
    by_contra hh
    have ha := (hsF (subset_tsupport F hh)).1.1
    rw [hFlift a ha] at hh
    have hw' : W (((h+k*(P:ℤ):ℤ):ℝ)/n) (a : UnitAddCircle) ≠ 0 :=
      fun hw' => hh (by rw [hw',mul_zero])
    have h1 := hχW _ _ hw'
    rw [hST k hk] at h1
    norm_num at h1
  exact unfolded_residue_density_error (o := o) (n := n) (q := q) (w := w)
    (q₀ := fun j => circleDensityLift o (q j)) (E := E)
    hJ hIo hinj hd hF hcF hsFI hε hz hj hJe hn hP h S
    (hSN) hSTF (fun k _ => hq _) (fun k _ => hw _) (fun k _ => hq₀ _)
    (fun k _ => hw₀ _) (fun k _ => hqs _) (fun k _ => hws _)
    hEi (fun j => integral_nonneg (fun a => abs_nonneg _))
    (fun k _ => retainedCircleWeight_error hψ hχ hχW hW hcc n _)

lemma retained_unfolded_residue_tendsto
    {I : Set ℝ} {J₀ : ℝ → ℝ} {J : UnitAddCircle → ℝ} {o : ℝ}
    {F : ℝ × ℝ → ℝ} {W χ : ℝ → UnitAddCircle → ℝ}
    {ψ : UnitAddCircle → ℝ} {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀) (hIo : IsOpen I)
    (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hcF : HasCompactSupport F)
    (hsF : tsupport F ⊆ (Ioc o (o+1) ∩ I) ×ˢ univ)
    {ε : ℝ} (hε : 0 < ε) (hz : ∀ a s, |s| < ε → F (a,s) = 0)
    (hj : Measurable J) (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hW : Continuous W.uncurry) (hcW : HasCompactSupport W.uncurry)
    (hcc : ∀ n j, Continuous (c n j))
    (hcs : ∀ n, Summable (fun j => ∫ a, ‖c n j a‖^2 ∂AddCircle.haarAddCircle))
    (hmass : Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ a,
      |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) atTop (𝓝 0))
    (hψc : Continuous ψ) (hχc : Continuous χ.uncurry)
    (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1) (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, W s a ≠ 0 → χ s a = 1)
    (hψS : ∀ x ∈ Ioc o (o+1), ψ (x : UnitAddCircle) ≠ 0 → x ∈ I)
    (hFlift : ∀ x ∈ Ioc o (o+1), ∀ s,
      F (x,s) = ψ (x : UnitAddCircle)^2*W s (x : UnitAddCircle))
    {P : ℕ} (hP : 0 < P) (h : ℤ) (S : ℕ → Finset ℤ)
    (hSN : ∀ n, 0 < n → ∀ k ∈ S n, h+k*(P:ℤ) ≠ 0)
    (hST : ∀ n, 0 < n → ∀ k ∉ S n, ∀ a,
      χ (((h+k*(P:ℤ):ℤ):ℝ)/n) a = 0) :
    Tendsto (fun n : ℕ => ∫ t, |(∑ k ∈ S n,
      unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
        (circleDensityLift o (retainedCircleWeight ψ χ c n (h+k*(P:ℤ))))
        n ((h+k*(P:ℤ):ℤ):ℝ) t)-
      fineResidueKernel (passageBranchKernel I J₀ F) P h n t|) atTop (𝓝 0) := by
  have hsFI : tsupport F ⊆ I ×ˢ univ := fun p hp => ⟨(hsF hp).1.2,mem_univ _⟩
  have hfreeze := passageBranchKernel_fine_density hJ hIo hinj hd hF hcF hsFI hε hz hP h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [zero_add] using hmass.add hfreeze)
  · exact Eventually.of_forall (fun n => integral_nonneg (fun t => abs_nonneg _))
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact retained_unfolded_residue_error hJ hIo hinj hd hF hcF hsF hε hz hj hJe hW hcW
    hcc hcs hψc hχc hψ hχ hχW hψS hFlift hn hP h (S n) (hSN n hn) (hST n hn)

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma scaled_speed_good_branch {V : ℝ → ℝ} {m : ℤ} {l u R : ℝ}
    (hm : m ≠ 0) (hR : 0 < R)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x) :
    InjOn (fun x => (m:ℝ)*V x) (Icc (l-R) (u+R)) ∧
      ∀ x ∈ Ioo (l-R) (u+R), deriv (fun x => (m:ℝ)*V x) x ≠ 0 := by
  have hsub : Icc (l-R) (u+R) ⊆ Icc (l-2*R) (u+2*R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hi : InjOn V (Icc (l-R) (u+R)) :=
    (strictMonoOn_of_deriv_pos (convex_Icc _ _) hV.continuous.continuousOn
      (fun x hx => hd x (hsub (interior_subset hx)))).injOn
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm
  refine ⟨?_,?_⟩
  · intro x hx y hy he
    exact hi hx hy (mul_left_cancel₀ hm' he)
  · intro x hx
    rw [deriv_const_mul _ (hV.differentiable (by simp) x)]
    exact mul_ne_zero hm' (hd x (hsub (Ioo_subset_Icc_self hx))).ne'

/-- The fine temporal density assertion of the Passage Lemma for one actual
old packet. There are no asymptotic or numerical stationary-phase estimates
among the hypotheses: the exact signed Fourier mass theorem supplies them.
The smooth real lift F is the cutoff old-frequency Jacobian, with its precise
identity stated below. -/
lemma exact_retained_unfolded_residue_tendsto
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {Pr V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(Pr x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hsupp : ∀ a, support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pr)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv Pr = V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0))
    {I : Set ℝ} {J₀ : ℝ → ℝ} {J : UnitAddCircle → ℝ} {o' : ℝ}
    {F : ℝ × ℝ → ℝ} {χ : ℝ → UnitAddCircle → ℝ} {ψ : UnitAddCircle → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀) (hIo : IsOpen I)
    (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hcF : HasCompactSupport F)
    (hsF : tsupport F ⊆ (Ioc o' (o'+1) ∩ I) ×ˢ univ)
    {ε : ℝ} (hε : 0 < ε) (hz : ∀ a s, |s| < ε → F (a,s) = 0)
    (hj : Measurable J) (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hψc : Continuous ψ) (hχc : Continuous χ.uncurry)
    (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1) (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1)
    (hψS : ∀ x ∈ Ioc o' (o'+1), ψ (x : UnitAddCircle) ≠ 0 → x ∈ I)
    (hFlift : ∀ x ∈ Ioc o' (o'+1), ∀ s,
      F (x,s) = ψ (x : UnitAddCircle)^2*
        stationaryWeight (Icc (l-R) (u+R)) (fun u => (m:ℝ)*V u) (A₀ (x : UnitAddCircle)) s)
    {Q : ℕ} (hQ : 0 < Q) (h : ℤ) (S : ℕ → Finset ℤ)
    (hSN : ∀ n, 0 < n → ∀ k ∈ S n, h+k*(Q:ℤ) ≠ 0)
    (hST : ∀ n, 0 < n → ∀ k ∉ S n, ∀ a,
      χ (((h+k*(Q:ℤ):ℤ):ℝ)/n) a = 0) :
    Tendsto (fun n : ℕ => ∫ t, |(∑ k ∈ S n,
      unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
        (circleDensityLift o' (retainedCircleWeight ψ χ
          (fun n j => exactPassageCoeff m (H n) A j) n (h+k*(Q:ℤ))))
        n ((h+k*(Q:ℤ):ℤ):ℝ) t)-
      fineResidueKernel (passageBranchKernel I J₀ F) Q h n t|) atTop (𝓝 0) := by
  have hbranch := scaled_speed_good_branch hm hR hV hdV
  have hW := stationaryWeight_signed_compact_continuous (contDiff_const.mul hV) hAc
    (fun a => (hsupp a).trans Ioc_subset_Icc_self) hR hbranch.1 hbranch.2
  have hmass := exactPassageCoeff_summed hm hH hA hA₀ hAc hAd hsupp hlo huo hlu hR
    hPr hV hPV hdV hHc hAcont hδt
  exact retained_unfolded_residue_tendsto
    (W := fun s a => stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s)
    (c := fun n j => exactPassageCoeff m (H n) A j)
    hJ hIo hinj hd hF hcF hsF hε hz hj hJe hW.1 hW.2
    (fun n j => continuous_exactPassageCoeff (hHc n) hAcont j)
    (fun n => exactPassageCoeff_summable (hHc n) hAcont) hmass hψc hχc hψ hχ hχW hψS hFlift
    hQ h S hSN hST

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma stationaryWeight_mul (C : Set ℝ) (J : ℝ → ℝ) (A : ℝ → ℂ) (c : ℂ) (s : ℝ) :
    stationaryWeight C J (fun x => c*A x) s = ‖c‖^2*stationaryWeight C J A s := by
  classical
  unfold stationaryWeight branchDensity
  simp only [Set.indicator_apply]
  split_ifs <;> simp [mul_pow,mul_div_assoc]

/-- The actual cutoff old-frequency Jacobian in real coordinates. The first
coordinate is the new slow coordinate; the second is the old frequency. -/
noncomputable def stationaryCutoffLift (C : Set ℝ) (J : ℝ → ℝ)
    (A : ℝ × ℝ → ℂ) (ψ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ψ p.1^2*stationaryWeight C J (fun x => A (x,p.1)) p.2

lemma stationaryCutoffLift_eq {C : Set ℝ} {J : ℝ → ℝ}
    {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ} :
    stationaryCutoffLift C J A ψ = fun p : ℝ × ℝ =>
      stationaryWeight C J (fun x => (ψ p.1 : ℂ)*A (x,p.1)) p.2 := by
  funext p
  rw [stationaryWeight_mul]
  simp [stationaryCutoffLift,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma cutoff_amplitude_regular {K : Set ℝ} {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ}
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hKA : ∀ p, A p ≠ 0 → p.1 ∈ K) (hK : IsCompact K)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcψ : HasCompactSupport ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => (ψ p.2 : ℂ)*A p) ∧
      HasCompactSupport (fun p : ℝ × ℝ => (ψ p.2 : ℂ)*A p) ∧
      tsupport (fun p : ℝ × ℝ => (ψ p.2 : ℂ)*A p) ⊆ K ×ˢ tsupport ψ := by
  let B : ℝ × ℝ → ℂ := fun p => (ψ p.2 : ℂ)*A p
  have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B :=
    (Complex.ofRealCLM.contDiff.comp (hψ.comp contDiff_snd)).mul hA
  have hsB : tsupport B ⊆ K ×ˢ tsupport ψ := by
    apply closure_minimal _ (hK.isClosed.prod (isClosed_tsupport ψ))
    intro p hp
    have ha : A p ≠ 0 := fun hz => hp (by simp [B,hz])
    have hψn : ψ p.2 ≠ 0 := fun hz => hp (by simp [B,hz])
    exact ⟨hKA p ha,subset_tsupport ψ hψn⟩
  have hcB : HasCompactSupport B :=
    (hK.prod hcψ).of_isClosed_subset (isClosed_tsupport B) hsB
  exact ⟨hB,hcB,hsB⟩

lemma stationaryCutoffLift_regular {C I K : Set ℝ} {J : ℝ → ℝ}
    {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ}
    (hIC : I ⊆ C) (hi : InjOn J C)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hKA : ∀ p, A p ≠ 0 → p.1 ∈ K) (hK : IsCompact K) (hKI : K ⊆ I)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcψ : HasCompactSupport ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (stationaryCutoffLift C J A ψ) ∧
      HasCompactSupport (stationaryCutoffLift C J A ψ) := by
  let B : ℝ × ℝ → ℂ := fun p => (ψ p.2 : ℂ)*A p
  obtain ⟨hB,hcB,hsB⟩ := cutoff_amplitude_regular hA hKA hK hψ hcψ
  have hsBI : tsupport B ⊆ I ×ˢ univ := fun p hp => ⟨hKI (hsB hp).1,mem_univ _⟩
  have h := stationaryWeight_smooth_lift (C := C) (I := I) (J := J) (B := B)
    hIC hi hJ hIo hd hB hcB hsBI
  let G : ℝ × ℝ → ℝ := fun p => stationaryWeight C J (fun x => B (x,p.2)) p.1
  have hswap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
    contDiff_snd.prodMk contDiff_fst
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G ∘ Prod.swap) := h.1.comp hswap
  have hc : HasCompactSupport (G ∘ Prod.swap) :=
    h.2.comp_homeomorph (Homeomorph.prodComm ℝ ℝ)
  have he : stationaryCutoffLift C J A ψ = G ∘ Prod.swap := stationaryCutoffLift_eq
  rw [he]
  exact ⟨hs,hc⟩

lemma stationaryWeight_support_subset {C K : Set ℝ} {J : ℝ → ℝ} {A : ℝ → ℂ}
    (hA : support A ⊆ K) : support (stationaryWeight C J A) ⊆ J '' K := by
  classical
  intro s hs
  have hsC : s ∈ J '' C := by
    by_contra hn
    exact hs (by simp [stationaryWeight,branchDensity,hn])
  have hp := invFunOn_pos hsC
  refine ⟨invFunOn J C s,hA ?_,hp.2⟩
  intro hz
  exact hs (by simp [stationaryWeight,branchDensity,hsC,show A (invFunOn J C s) = 0 from hz])

lemma stationaryCutoffLift_support {C K : Set ℝ} {J : ℝ → ℝ}
    {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ}
    (hJ : Continuous J) (hK : IsCompact K) (hKA : ∀ p, A p ≠ 0 → p.1 ∈ K) :
    tsupport (stationaryCutoffLift C J A ψ) ⊆ tsupport ψ ×ˢ (J '' K) := by
  apply closure_minimal _ ((isClosed_tsupport ψ).prod (hK.image hJ).isClosed)
  intro p hp
  have hψn : ψ p.1 ≠ 0 := fun hz => hp (by simp [stationaryCutoffLift,hz])
  have hWn : stationaryWeight C J (fun x => A (x,p.1)) p.2 ≠ 0 :=
    fun hz => hp (by simp [stationaryCutoffLift,hz])
  exact ⟨subset_tsupport ψ hψn,
    stationaryWeight_support_subset (fun x hx => hKA (x,p.1) hx) hWn⟩

lemma stationaryCutoffLift_zero_near_zero {C K : Set ℝ} {J : ℝ → ℝ}
    {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ}
    (hJ : Continuous J) (hK : IsCompact K) (hKA : ∀ p, A p ≠ 0 → p.1 ∈ K)
    (h0 : 0 ∉ J '' K) :
    ∃ ε > 0, ∀ a s, |s| < ε → stationaryCutoffLift C J A ψ (a,s) = 0 := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp ((hK.image hJ).isClosed.isOpen_compl.mem_nhds h0)
  refine ⟨ε,hε,?_⟩
  intro a s hs
  by_contra hh
  have hh' := stationaryCutoffLift_support hJ hK hKA (subset_tsupport _ hh)
  exact hball (by simpa [Metric.mem_ball,Real.dist_eq] using hs) hh'.2

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma exists_retained_residue_sequence {χ : ℝ → UnitAddCircle → ℝ}
    (hc : HasCompactSupport χ.uncurry) (hz : ∀ a, χ 0 a = 0)
    {P : ℕ} (hP : 0 < P) (h : ℤ) :
    ∃ S : ℕ → Finset ℤ,
      (∀ n, 0 < n → ∀ k ∈ S n, h+k*(P:ℤ) ≠ 0) ∧
      ∀ n, 0 < n → ∀ k ∉ S n, ∀ a, χ (((h+k*(P:ℤ):ℤ):ℝ)/n) a = 0 := by
  classical
  have hs (n : ℕ) : ∃ S : Finset ℤ,
      (0 < n → ∀ k ∈ S, h+k*(P:ℤ) ≠ 0) ∧
      (0 < n → ∀ k ∉ S, ∀ a, χ (((h+k*(P:ℤ):ℤ):ℝ)/n) a = 0) := by
    by_cases hn : 0 < n
    · obtain ⟨S,hS,hT⟩ := exists_retained_residue_indices hc hz hn hP h
      exact ⟨S,fun _ => hS,fun _ => hT⟩
    · exact ⟨∅,fun hh => (hn hh).elim,fun hh => (hn hh).elim⟩
  choose S hN hT using hs
  exact ⟨S,hN,hT⟩

/-- The cutoff old-frequency Jacobian used in the Passage Lemma has all
required regularity, including the frequency gap. These conclusions are
derived from the actual smooth amplitude and compact cutoffs. -/
lemma exact_cutoff_weight_regular
    {V : ℝ → ℝ} {m : ℤ} {l u R : ℝ} {A₀ : UnitAddCircle → ℝ → ℂ} {ψ₀ : ℝ → ℝ}
    (hm : m ≠ 0) (hR : 0 < R)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (hAr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ a, support (A₀ a) ⊆ Icc l u)
    (hψ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hcψ₀ : HasCompactSupport ψ₀)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u) :
    let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1) ψ₀
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧ HasCompactSupport F ∧
      ∃ ε > 0, ∀ a s, |s| < ε → F (a,s) = 0 := by
  dsimp only
  have hb := scaled_speed_good_branch hm hR hV hdV
  have hKI : Icc l u ⊆ Ioo (l-R) (u+R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hKA : ∀ p : ℝ × ℝ, A₀ (p.2 : UnitAddCircle) p.1 ≠ 0 → p.1 ∈ Icc l u :=
    fun p hp => hsupp _ hp
  have h := stationaryCutoffLift_regular Ioo_subset_Icc_self hb.1 (contDiff_const.mul hV)
    isOpen_Ioo hb.2 hAr hKA isCompact_Icc hKI hψ₀ hcψ₀
  exact ⟨h.1,h.2,stationaryCutoffLift_zero_near_zero
    (continuous_const.mul hV.continuous) isCompact_Icc hKA h0⟩

/-- Source Passage Lemma, exact unfolded spectral conclusion for any residue
of one signed packet. The Fourier coefficients, cutoff weight and fine kernel
are all the displayed source objects. Smooth compact lift, finite retention
and frequency-gap obligations are produced here, not postulated as analytic
estimates. Geometry and physical Fourier transport are separate proved lemmas. -/
lemma exact_passage_unfolded_spectral_limit
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {Pr V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(Pr x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hAr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ a, support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pr)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv Pr = V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0))
    {I : Set ℝ} {J₀ : ℝ → ℝ} {J : UnitAddCircle → ℝ} {o' : ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀) (hIo : IsOpen I)
    (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    (hj : Measurable J) (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hψ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hcψ₀ : HasCompactSupport ψ₀)
    (hsψ₀ : tsupport ψ₀ ⊆ Ioc o' (o'+1) ∩ I)
    (heψ : ∀ x ∈ Ioc o' (o'+1), ψ₀ x = ψ (x : UnitAddCircle))
    (hψc : Continuous ψ) (hχc : Continuous χ.uncurry) (hcχ : HasCompactSupport χ.uncurry)
    (hzχ : ∀ a, χ 0 a = 0)
    (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1) (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1)
    {Q : ℕ} (hQ : 0 < Q) (h : ℤ) :
    let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1) ψ₀
    ∃ S : ℕ → Finset ℤ,
      (∀ n, 0 < n → ∀ k ∈ S n, h+k*(Q:ℤ) ≠ 0) ∧
      (∀ n, 0 < n → ∀ k ∉ S n, ∀ a, χ (((h+k*(Q:ℤ):ℤ):ℝ)/n) a = 0) ∧
      Tendsto (fun n : ℕ => ∫ t, |(∑ k ∈ S n,
        unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
          (circleDensityLift o' (retainedCircleWeight ψ χ
            (fun n j => exactPassageCoeff m (H n) A j) n (h+k*(Q:ℤ))))
          n ((h+k*(Q:ℤ):ℤ):ℝ) t)-
        fineResidueKernel (passageBranchKernel I J₀ F) Q h n t|) atTop (𝓝 0) := by
  let B : ℝ × ℝ → ℂ := fun p => A₀ (p.2 : UnitAddCircle) p.1
  let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) B ψ₀
  change ∃ S, _
  obtain ⟨hF,hcF,ε,hε,hz⟩ := exact_cutoff_weight_regular hm hR hV hdV hAr
    (fun a => (hsupp a).trans Ioc_subset_Icc_self) hψ₀ hcψ₀ h0
  have hKA : ∀ p : ℝ × ℝ, B p ≠ 0 → p.1 ∈ Icc l u :=
    fun p hp => Ioc_subset_Icc_self (hsupp _ hp)
  have hsF : tsupport F ⊆ (Ioc o' (o'+1) ∩ I) ×ˢ univ := by
    intro p hp
    exact ⟨hsψ₀ (stationaryCutoffLift_support (continuous_const.mul hV.continuous)
      isCompact_Icc hKA hp).1,mem_univ _⟩
  have hψS : ∀ x ∈ Ioc o' (o'+1), ψ (x : UnitAddCircle) ≠ 0 → x ∈ I := by
    intro x hx hn
    exact (hsψ₀ (subset_tsupport ψ₀ (by simpa only [mem_support, heψ x hx] using hn))).2
  have hFlift : ∀ x ∈ Ioc o' (o'+1), ∀ s,
      F (x,s) = ψ (x : UnitAddCircle)^2*
        stationaryWeight (Icc (l-R) (u+R)) (fun u => (m:ℝ)*V u) (A₀ (x : UnitAddCircle)) s := by
    intro x hx s
    simp only [F,stationaryCutoffLift,heψ x hx,B]
  obtain ⟨S,hSN,hST⟩ := exists_retained_residue_sequence hcχ hzχ hQ h
  refine ⟨S,hSN,hST,?_⟩
  exact exact_retained_unfolded_residue_tendsto hm hH hA hA₀ hAc hAd hsupp hlo huo hlu hR
    hPr hV hPV hdV hHc hAcont hδt hJ hIo hinj hd hF hcF hsF hε hz hj hJe
    hψc hχc hψ hχ hχW hψS hFlift hQ h S hSN hST

end ThreeTorus

noncomputable section
open MeasureTheory Set Function
open scoped Topology ENNReal
namespace ThreeTorus

/-- The actual period-one lattice sum used to fold an unfolded temporal density. -/
def periodizedReal (q : ℝ → ℝ) (x : ℝ) : ℝ := ∑' k : ℤ, q (x+k)

def foldCircleDensity (q : ℝ → ℝ) : UnitAddCircle → ℝ :=
  AddCircle.liftIoc 1 0 (periodizedReal q)

lemma measurable_periodizedReal {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (periodizedReal q) := by
  exact Measurable.tsum (fun k => hq.comp (measurable_id.add_const (k:ℝ)))

lemma measurable_foldCircleDensity {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (foldCircleDensity q) := by
  exact ((measurable_periodizedReal hq).comp measurable_subtype_coe).comp
    (AddCircle.measurableEquivIoc 1 0).measurable

lemma foldCircleDensity_coe {q : ℝ → ℝ} {x : ℝ} (hx : x ∈ Ioc 0 1) :
    foldCircleDensity q (x : UnitAddCircle) = periodizedReal q x := by
  exact AddCircle.liftIoc_coe_apply (by simpa using hx)

private def intUnitEquiv : ℤ ≃ AddSubgroup.zmultiples (1:ℝ) :=
  Equiv.ofInjective (fun n : ℤ => n • (1:ℝ)) (zsmul_left_strictMono (by norm_num : 0 < (1:ℝ))).injective

lemma integral_real_eq_lattice (q : ℝ → ℝ) (hq : Integrable q) :
    (∫ x, q x) = ∑' k : ℤ, ∫ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).integral_eq_tsum'' q hq
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma lintegral_real_eq_lattice (q : ℝ → ℝ≥0∞) :
    (∫⁻ x, q x) = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).lintegral_eq_tsum'' q
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma integrableOn_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    IntegrableOn (periodizedReal q) (Ioc 0 1) := by
  refine ⟨(measurable_periodizedReal hm).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ x in Ioc (0:ℝ) 1, ‖periodizedReal q x‖ₑ) ≤
        ∫⁻ x in Ioc (0:ℝ) 1, ∑' k : ℤ, ‖q (x+k)‖ₑ :=
      lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)
    _ = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, ‖q (x+k)‖ₑ :=
      lintegral_tsum (fun k => (hm.comp (measurable_id.add_const (k:ℝ))).enorm.aemeasurable)
    _ = ∫⁻ x, ‖q x‖ₑ := (lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)).symm
    _ < ∞ := hq.hasFiniteIntegral

lemma integral_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ x in Ioc (0:ℝ) 1, periodizedReal q x) = ∫ x, q x := by
  change (∫ x in Ioc (0:ℝ) 1, ∑' k : ℤ, q (x+k)) = ∫ x, q x
  rw [integral_tsum]
  · exact (integral_real_eq_lattice q hq).symm
  · exact fun k => (hm.comp (measurable_id.add_const (k:ℝ))).aestronglyMeasurable
  · rw [← lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)]
    exact hq.hasFiniteIntegral.ne

lemma integrable_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    Integrable (foldCircleDensity q) AddCircle.haarAddCircle := by
  have hp : MeasurePreserving (fun x : ℝ => (x:UnitAddCircle))
      (volume.restrict (Ioc (0:ℝ) 1)) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 0
  apply (hp.integrable_comp (measurable_foldCircleDensity hm).aestronglyMeasurable).1
  exact (integrableOn_periodizedReal hm hq).congr
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => (foldCircleDensity_coe hx).symm))

lemma integral_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ a, foldCircleDensity q a ∂AddCircle.haarAddCircle) = ∫ x, q x := by
  have he := AddCircle.integral_preimage 1 0 (foldCircleDensity q)
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,
    one_smul] at he
  rw [← he]
  exact (setIntegral_congr_fun measurableSet_Ioc (fun x hx => foldCircleDensity_coe hx)).trans
    (integral_periodizedReal hm hq)

lemma quotient_add_int (x : ℝ) (k : ℤ) : ((x+k : ℝ):UnitAddCircle) = (x:UnitAddCircle) := by
  have h : ((k:ℝ):UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).2 ⟨k,by simp⟩
  rw [AddCircle.coe_add,h,add_zero]

lemma foldCircleDensity_indicator (q : ℝ → ℝ) (s : Set UnitAddCircle) :
    foldCircleDensity (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) =
      s.indicator (foldCircleDensity q) := by
  classical
  funext a
  let x : ℝ := (AddCircle.equivIoc 1 0 a).1
  have hx : x ∈ Ioc (0:ℝ) 1 := by simpa using (AddCircle.equivIoc 1 0 a).2
  have ha : (x:UnitAddCircle) = a := (AddCircle.equivIoc 1 0).symm_apply_apply a
  rw [← ha]
  by_cases hs : (x:UnitAddCircle) ∈ s
  · simp only [indicator_of_mem hs,foldCircleDensity_coe hx,periodizedReal]
    apply tsum_congr
    intro k
    exact indicator_of_mem (by simpa only [mem_preimage,quotient_add_int] using hs) q
  · simp only [indicator_of_notMem hs,foldCircleDensity_coe hx,periodizedReal]
    have hz (k : ℤ) : (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) (x+k) = 0 :=
      indicator_of_notMem (by simpa only [mem_preimage,quotient_add_int] using hs) q
    simp only [hz,tsum_zero]

/-- Folding is exactly pushforward under the quotient, not a replacement kernel. -/
lemma foldCircleDensity_pushforward {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    ((volume : Measure ℝ).withDensityᵥ q).map (fun x : ℝ => (x:UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensityᵥ (foldCircleDensity q) := by
  ext s hs
  rw [VectorMeasure.map_apply _ AddCircle.measurable_mk' hs,
    withDensityᵥ_apply hq (AddCircle.measurable_mk' hs),
    withDensityᵥ_apply (integrable_foldCircleDensity hm hq) hs,
    ← integral_indicator (AddCircle.measurable_mk' hs),← integral_indicator hs]
  rw [← foldCircleDensity_indicator]
  exact (integral_foldCircleDensity (hm.indicator (AddCircle.measurable_mk' hs))
    (hq.indicator (AddCircle.measurable_mk' hs))).symm

lemma foldCircleDensity_l1_difference {q r : ℝ → ℝ}
    (hqm : Measurable q) (hqi : Integrable q) (hrm : Measurable r) (hri : Integrable r) :
    (∫ a, |foldCircleDensity q a-foldCircleDensity r a| ∂AddCircle.haarAddCircle) ≤
      ∫ x, |q x-r x| := by
  exact l1_pushforward_difference hqi hri (integrable_foldCircleDensity hqm hqi)
    (integrable_foldCircleDensity hrm hri) AddCircle.measurable_mk'
    (foldCircleDensity_pushforward hqm hqi) (foldCircleDensity_pushforward hrm hri)

lemma foldCircleDensity_l1_tendsto {ι : Type*} {l : Filter ι} {q r : ι → ℝ → ℝ}
    (hqm : ∀ᶠ n in l, Measurable (q n)) (hqi : ∀ᶠ n in l, Integrable (q n))
    (hrm : ∀ᶠ n in l, Measurable (r n)) (hri : ∀ᶠ n in l, Integrable (r n))
    (ht : Filter.Tendsto (fun n => ∫ x, |q n x-r n x|) l (𝓝 0)) :
    Filter.Tendsto (fun n => ∫ a, |foldCircleDensity (q n) a-foldCircleDensity (r n) a|
      ∂AddCircle.haarAddCircle) l (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _))) ?_ ht
  filter_upwards [hqm,hqi,hrm,hri] with n hqm hqi hrm hri
  exact foldCircleDensity_l1_difference hqm hqi hrm hri

lemma periodizedReal_add_int (q : ℝ → ℝ) (x : ℝ) (j : ℤ) :
    periodizedReal q (x+j) = periodizedReal q x := by
  have h := (Equiv.addLeft j).tsum_eq (fun k : ℤ => q (x+k))
  change (∑' k : ℤ, q (x+(j:ℝ)+(k:ℝ))) = ∑' k : ℤ, q (x+(k:ℝ))
  rw [← h]
  apply tsum_congr
  intro k
  congr 1
  change x+(j:ℝ)+(k:ℝ) = x+((j+k:ℤ):ℝ)
  simp only [Int.cast_add,add_assoc]

/-- The displayed lattice formula holds for every real representative. -/
lemma foldCircleDensity_coe_all (q : ℝ → ℝ) (x : ℝ) :
    foldCircleDensity q (x:UnitAddCircle) = ∑' k : ℤ, q (x+k) := by
  let y : ℝ := (AddCircle.equivIoc 1 0 (x:UnitAddCircle)).1
  have hy : y ∈ Ioc (0:ℝ) 1 := by simpa using (AddCircle.equivIoc 1 0 (x:UnitAddCircle)).2
  have hxy : (y:UnitAddCircle) = (x:UnitAddCircle) :=
    (AddCircle.equivIoc 1 0).symm_apply_apply (x:UnitAddCircle)
  have hz : ((y-x:ℝ):UnitAddCircle) = 0 := by rw [AddCircle.coe_sub,hxy,sub_self]
  obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff 1).1 hz
  have he : y = x+(k:ℝ) := by simpa only [zsmul_eq_mul,mul_one] using eq_add_of_sub_eq' hk.symm
  rw [← hxy,foldCircleDensity_coe hy,he,periodizedReal_add_int]
  rfl

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma measurable_branchDensity_smooth {I : Set ℝ} {J q : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0) (hq : Measurable q) :
    Measurable (branchDensity I J (invFunOn J I) (deriv J) q) := by
  classical
  let S := J '' I
  let g := S.piecewise (invFunOn J I) (fun _ => 0)
  have hS : IsOpen S := isOpen_image_of_deriv_ne_zero hJ hIo hd
  have hgi : ContinuousOn (invFunOn J I) S := by
    rintro y ⟨x,hx,rfl⟩
    exact (contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hx
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hx)).continuousAt.continuousWithinAt
  have hg : Measurable g := hgi.measurable_piecewise continuous_const.continuousOn hS.measurableSet
  have he : branchDensity I J (invFunOn J I) (deriv J) q =
      S.indicator (fun y => q (g y)/|deriv J (g y)|) := by
    funext y
    by_cases hy : y ∈ S
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp [g,hy]
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp only [indicator_of_notMem hy]
  rw [he]
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := hJ.deriv'
  exact ((hq.comp hg).div ((hD.continuous.measurable.comp hg).abs)).indicator hS.measurableSet

lemma measurable_circleDensityLift {q : UnitAddCircle → ℝ} (hq : Measurable q) (o : ℝ) :
    Measurable (circleDensityLift o q) :=
  (hq.comp AddCircle.measurable_mk').indicator measurableSet_Ioc

lemma measurable_unfoldedModeDensity {I : Set ℝ} {J q : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0) (hq : Measurable q) (n j : ℝ) :
    Measurable (unfoldedModeDensity I J (invFunOn J I) (deriv J) q n j) := by
  have hm := measurable_branchDensity_smooth hJ hIo hinj hd (hq.const_mul n)
  unfold unfoldedModeDensity scaledBranchKernel
  exact (hm.comp ((measurable_const.mul measurable_id).sub_const j |>.div_const (j/n))).const_mul |j/n|⁻¹

lemma passageBranchKernel_regular {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ I ×ˢ univ) {ε : ℝ} (hε : 0 < ε)
    (hz : ∀ a s, |s| < ε → F (a,s) = 0) :
    Continuous (passageBranchKernel I J F).uncurry ∧
      ∃ A > 0, ∃ M : ℕ,
        (∀ s y, A < |s| → passageBranchKernel I J F s y = 0) ∧
        ∀ s y, (M:ℝ) < |y| → passageBranchKernel I J F s y = 0 := by
  have hSm := branchKernel_smooth hJ hIo hinj hd hF hc hs
  obtain ⟨D,A,hD,hA,hx,ha⟩ := branchKernel_bounds (I := I) hJ.continuous hc
  have hsmooth := affineKernel_smooth (L := (1:ℝ)) (β := (0:ℝ))
    (hSm.comp (contDiff_snd.prodMk contDiff_fst)) hε (show
      ∀ s a, |s| < ε → branchKernel I J F (a,s) = 0 from fun s a hh => by
        simp [branchKernel,hz _ _ hh])
  obtain ⟨M,hM⟩ := exists_nat_ge (A*((1:ℝ)*D+|(0:ℝ)|))
  refine ⟨hsmooth.continuous,max A 1,lt_max_of_lt_right zero_lt_one,M,?_,?_⟩
  · intro s y hh
    exact affineKernel_eq_zero_s (fun s a hh => ha a s hh) (lt_of_le_of_lt (le_max_left _ _) hh)
  · intro s y hy
    exact affineKernel_eq_zero_y (by norm_num) hA hD
      (fun s a hh => ha a s hh) (fun s a hh => hx a s hh) (lt_of_le_of_lt hM hy)

lemma fineResidueKernel_regular {K : ℝ → ℝ → ℝ} {A : ℝ} {M n P : ℕ}
    (hK : Continuous K.uncurry) (_hA : 0 < A)
    (hs : ∀ s y, A < |s| → K s y = 0)
    (hy : ∀ s y, (M:ℝ) < |y| → K s y = 0)
    ( _hn : 0 < n) (hP : 0 < P) (h : ℤ) :
    Continuous (fineResidueKernel K P h n) ∧ Integrable (fineResidueKernel K P h n) := by
  have hc := continuous_fineResidueKernel (n := n) h hK hs hy hP
  refine ⟨hc,hc.integrable_of_hasCompactSupport ?_⟩
  apply HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A))
  intro t ht
  apply fineResidueKernel_eq_zero hs
  by_contra hh
  exact ht ⟨(abs_le.mp (le_of_not_gt hh)).1,(abs_le.mp (le_of_not_gt hh)).2⟩

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma retained_unfolded_regular {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    {ψ : UnitAddCircle → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry) (hc : ∀ n j, Continuous (c n j))
    (o : ℝ) {n : ℕ} (hn : 0 < n) {j : ℤ} (hj : j ≠ 0) :
    Measurable (unfoldedModeDensity I J (invFunOn J I) (deriv J)
      (circleDensityLift o (retainedCircleWeight ψ χ c n j)) n j) ∧
    Integrable (unfoldedModeDensity I J (invFunOn J I) (deriv J)
      (circleDensityLift o (retainedCircleWeight ψ χ c n j)) n j) := by
  have hq : Continuous (retainedCircleWeight ψ χ c n j) :=
    ((hψ.pow 2).mul ((hχ.comp (continuous_const.prodMk continuous_id)).pow 2)).mul
      ((hc n j).norm.pow 2)
  exact ⟨measurable_unfoldedModeDensity hJ hIo hinj hd
      (measurable_circleDensityLift hq.measurable o) n j,
    integrable_unfoldedModeDensity hIo.measurableSet
      (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet
      (fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt) hinj
      (fun _ hx => hinj.leftInvOn_invFunOn hx) hd
      (integrable_circleDensityLift (retainedCircleWeight_integrable hψ hχ hc n j) o)
      (by exact_mod_cast hn) (by exact_mod_cast hj)⟩

/-- Exact contraction of the retained unfolded residue limit to the temporal
circle. In particular the quotient's offsets are not discarded. -/
lemma retained_circle_of_unfolded_limit
    {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hcF : HasCompactSupport F)
    (hsF : tsupport F ⊆ I ×ˢ univ) {ε : ℝ} (hε : 0 < ε)
    (hz : ∀ a s, |s| < ε → F (a,s) = 0)
    {ψ : UnitAddCircle → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry) (hc : ∀ n j, Continuous (c n j))
    (o : ℝ) {P : ℕ} (hP : 0 < P) (h : ℤ) (S : ℕ → Finset ℤ)
    (hSN : ∀ n, 0 < n → ∀ k ∈ S n, h+k*(P:ℤ) ≠ 0)
    (ht : Tendsto (fun n : ℕ => ∫ t, |(∑ k ∈ S n,
      unfoldedModeDensity I J (invFunOn J I) (deriv J)
        (circleDensityLift o (retainedCircleWeight ψ χ c n (h+k*(P:ℤ))))
        n ((h+k*(P:ℤ):ℤ):ℝ) t)-
      fineResidueKernel (passageBranchKernel I J F) P h n t|) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ a, |foldCircleDensity (fun t => ∑ k ∈ S n,
      unfoldedModeDensity I J (invFunOn J I) (deriv J)
        (circleDensityLift o (retainedCircleWeight ψ χ c n (h+k*(P:ℤ))))
        n ((h+k*(P:ℤ):ℤ):ℝ) t) a-
      foldCircleDensity (fineResidueKernel (passageBranchKernel I J F) P h n) a|
      ∂AddCircle.haarAddCircle) atTop (𝓝 0) := by
  obtain ⟨hK,A,hA,M,hsK,hyK⟩ := passageBranchKernel_regular hJ hIo hinj hd hF hcF hsF hε hz
  have hreg (n : ℕ) (hn : 0 < n) := fineResidueKernel_regular hK hA hsK hyK hn hP h
  apply foldCircleDensity_l1_tendsto (ht := ht)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (S n).measurable_fun_sum (fun k hk =>
      (retained_unfolded_regular hJ hIo hinj hd hψ hχ hc o hn (hSN n hn k hk)).1)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact integrable_finsetSum _ (fun k hk =>
      (retained_unfolded_regular hJ hIo hinj hd hψ hχ hc o hn (hSN n hn k hk)).2)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (hreg n hn).1.measurable
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (hreg n hn).2

lemma vectorMeasure_map_comp {X Y Z E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [AddCommMonoid E] [TopologicalSpace E]
    (ν : VectorMeasure X E) {f : X → Y} {g : Y → Z} (hf : Measurable f) (hg : Measurable g) :
    (ν.map f).map g = ν.map (g ∘ f) := by
  ext s hs
  rw [VectorMeasure.map_apply _ hg hs,VectorMeasure.map_apply _ hf (hg hs),
    VectorMeasure.map_apply _ (hg.comp hf) hs]
  rfl

/-- The folded expression is the density of the actual mode spectral map
j(1+J/n)/n modulo one. Thus the circle limit is a spectral-density statement. -/
lemma foldedModeDensity_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqm : Measurable q₀)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    {n j : ℝ} (hn : 0 < n) (hjn : j ≠ 0) :
    (AddCircle.haarAddCircle.withDensityᵥ q).map
        (fun a => (((j+(j/n)*J a)/n : ℝ) : UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensityᵥ
        (foldCircleDensity (unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀ n j)) := by
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hD : ∀ x ∈ I, HasDerivWithinAt J₀ (deriv J₀ x) I x :=
    fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt
  have hp := unfoldedModeDensity_pushforward hq hq₀ hq₀s hqs hj hJ.continuous.measurable hJe
    hIo.measurableSet (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet hD hinj
    (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hn hjn
  have h := congrArg (fun ν : VectorMeasure ℝ ℝ => ν.map (fun t : ℝ => (t:UnitAddCircle))) hp
  have hf : Measurable (fun a => (j+(j/n)*J a)/n) :=
    (measurable_const.add (hj.const_mul _)).div_const n
  have hg : Measurable (fun t : ℝ => (t:UnitAddCircle)) := AddCircle.measurable_mk'
  rw [vectorMeasure_map_comp _ hf hg] at h
  rw [foldCircleDensity_pushforward
    (measurable_unfoldedModeDensity hJ hIo hinj hd hqm n j)
    (integrable_unfoldedModeDensity hIo.measurableSet
      (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet hD hinj
      (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hqi hn hjn)] at h
  exact h

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology
/-- Source Passage Lemma, exact unfolded spectral conclusion for any residue
of one signed packet. The Fourier coefficients, cutoff weight and fine kernel
are all the displayed source objects. Smooth compact lift, finite retention
and frequency-gap obligations are produced here, not postulated as analytic
estimates. Geometry and physical Fourier transport are separate proved lemmas. -/
lemma exact_passage_circle_spectral_limit
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {Pr V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(Pr x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hAr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ a, support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pr)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv Pr = V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0))
    {I : Set ℝ} {J₀ : ℝ → ℝ} {J : UnitAddCircle → ℝ} {o' : ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀) (hIo : IsOpen I)
    (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    (hj : Measurable J) (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hψ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hcψ₀ : HasCompactSupport ψ₀)
    (hsψ₀ : tsupport ψ₀ ⊆ Ioc o' (o'+1) ∩ I)
    (heψ : ∀ x ∈ Ioc o' (o'+1), ψ₀ x = ψ (x : UnitAddCircle))
    (hψc : Continuous ψ) (hχc : Continuous χ.uncurry) (hcχ : HasCompactSupport χ.uncurry)
    (hzχ : ∀ a, χ 0 a = 0)
    (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1) (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1)
    {Q : ℕ} (hQ : 0 < Q) (h : ℤ) :
    let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1) ψ₀
    ∃ S : ℕ → Finset ℤ,
      (∀ n, 0 < n → ∀ k ∈ S n, h+k*(Q:ℤ) ≠ 0) ∧
      (∀ n, 0 < n → ∀ k ∉ S n, ∀ a, χ (((h+k*(Q:ℤ):ℤ):ℝ)/n) a = 0) ∧
      Tendsto (fun n : ℕ => ∫ a, |foldCircleDensity (fun t => ∑ k ∈ S n,
        unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
          (circleDensityLift o' (retainedCircleWeight ψ χ
            (fun n j => exactPassageCoeff m (H n) A j) n (h+k*(Q:ℤ))))
          n ((h+k*(Q:ℤ):ℤ):ℝ) t) a-
        foldCircleDensity (fineResidueKernel (passageBranchKernel I J₀ F) Q h n) a|
        ∂AddCircle.haarAddCircle) atTop (𝓝 0) := by
  let B : ℝ × ℝ → ℂ := fun p => A₀ (p.2 : UnitAddCircle) p.1
  let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) B ψ₀
  change ∃ S, _
  obtain ⟨hF,hcF,ε,hε,hz⟩ := exact_cutoff_weight_regular hm hR hV hdV hAr
    (fun a => (hsupp a).trans Ioc_subset_Icc_self) hψ₀ hcψ₀ h0
  have hKA : ∀ p : ℝ × ℝ, B p ≠ 0 → p.1 ∈ Icc l u :=
    fun p hp => Ioc_subset_Icc_self (hsupp _ hp)
  have hsF : tsupport F ⊆ I ×ˢ univ := by
    intro p hp
    exact ⟨(hsψ₀ (stationaryCutoffLift_support (continuous_const.mul hV.continuous)
      isCompact_Icc hKA hp).1).2,mem_univ _⟩
  obtain ⟨S,hSN,hST,ht⟩ := exact_passage_unfolded_spectral_limit hm hH hA hA₀ hAc hAd hAr
    hsupp hlo huo hlu hR hPr hV hPV hdV h0 hHc hAcont hδt hJ hIo hinj hd hj hJe hψ₀ hcψ₀
    hsψ₀ heψ hψc hχc hcχ hzχ hψ hχ hχW hQ h
  refine ⟨S,hSN,hST,?_⟩
  exact retained_circle_of_unfolded_limit hJ hIo hinj hd hF hcF hsF hε hz hψc hχc
    (fun n j => continuous_exactPassageCoeff (hHc n) hAcont j) o' hQ h S hSN ht

end ThreeTorus

end

end

end

end

end

end OAI
