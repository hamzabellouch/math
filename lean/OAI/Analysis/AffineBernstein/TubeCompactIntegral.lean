import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section
variable {S T : Type*} [NormedAddCommGroup S]
  [MeasurableSpace S] [BorelSpace S]
  [TopologicalSpace T] [T2Space T] [CompactSpace T] [SecondCountableTopology T]
  [MeasurableSpace T] [BorelSpace T]
  {μ : Measure S} {ν : Measure T} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasure ν]
lemma integrable_joint_compact_mul {f : S × T → ℝ} {σ : S → ℝ}
    (hσ : Continuous σ) (hc : HasCompactSupport σ)
    (hf : ContinuousOn f (tsupport σ ×ˢ (Set.univ : Set T))) :
    Integrable (fun q : S × T => f q*σ q.1) (μ.prod ν) := by
  have hs : Function.support (fun q : S × T => f q*σ q.1) ⊆ tsupport σ ×ˢ (Set.univ : Set T) := by
    intro q hq
    refine ⟨?_,Set.mem_univ _⟩
    by_contra hn
    simp [image_eq_zero_of_notMem_tsupport hn] at hq
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  exact ContinuousOn.integrableOn_compact (hc.isCompact.prod isCompact_univ)
    (hf.mul (hσ.comp continuous_fst).continuousOn)
end
open Metric
variable {S E : Type*} [NormedAddCommGroup S]
  [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]

def tubeOpenSet (D : Set S) : Set (S × E) := D ×ˢ {e : E | e ≠ 0}

def tubeLift (q : S × sphere (0:E) 1) : S × E := (q.1,(q.2:E))

omit [MeasurableSpace S] [BorelSpace S]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
lemma continuous_tubeLift : Continuous (tubeLift (S := S) (E := E)) :=
  continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)

omit [NormedAddCommGroup S]
  [MeasurableSpace S] [BorelSpace S] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tubeLift_mem {D : Set S} (q : S × sphere (0:E) 1) (h : q.1 ∈ D) :
    tubeLift q ∈ tubeOpenSet D := by
  refine ⟨h,?_⟩
  have hh : ‖(q.2:E)‖ = 1 := mem_sphere_zero_iff_norm.1 q.2.property
  intro hz
  change (q.2:E) = 0 at hz
  simp [hz] at hh

lemma integrable_tube_compact_mul {M g : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hσ : Continuous σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    (hM : ContinuousOn M (tubeOpenSet D)) (hg : ContinuousOn g (tubeOpenSet D)) :
    Integrable (fun q : S × sphere (0:E) 1 => M (tubeLift q)*g (tubeLift q)*σ q.1)
      (μ.prod (volume.toSphere : Measure (sphere (0:E) 1))) := by
  apply integrable_joint_compact_mul hσ hc
  exact (hM.mul hg).comp continuous_tubeLift.continuousOn
    (fun q hq => tubeLift_mem q (hσD hq.1))

lemma integrable_tube_compact_sq {M g : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hσ : Continuous σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    (hM : ContinuousOn M (tubeOpenSet D)) (hg : ContinuousOn g (tubeOpenSet D)) :
    Integrable (fun q : S × sphere (0:E) 1 => M (tubeLift q)*σ q.1^2*g (tubeLift q))
      (μ.prod (volume.toSphere : Measure (sphere (0:E) 1))) := by
  have hh := integrable_tube_compact_mul (μ := μ) hσ hc hσD hM
    (hg.mul (hσ.comp continuous_fst).continuousOn)
  convert hh using 1
  ext q
  simp only [tubeLift,Pi.mul_apply,Function.comp_apply]
  ring

/- The unrestricted product integral of a cutoff times a tube coefficient. -/
def tubeIntegral (μ : Measure S) (M : S × E → ℝ) (σ : S → ℝ) (g : S × E → ℝ) : ℝ :=
  ∫ q : S × sphere (0:E) 1, M (tubeLift q)*σ q.1*g (tubeLift q) ∂μ.prod volume.toSphere

lemma tubeIntegral_add {M f g : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hσ : Continuous σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    (hM : ContinuousOn M (tubeOpenSet D)) (hf : ContinuousOn f (tubeOpenSet D))
    (hg : ContinuousOn g (tubeOpenSet D)) :
    tubeIntegral μ M σ (fun q => f q+g q) = tubeIntegral μ M σ f+tubeIntegral μ M σ g := by
  have hi (f) (hf : ContinuousOn f (tubeOpenSet D)) :
      Integrable (fun q : S × sphere (0:E) 1 => M (tubeLift q)*σ q.1*f (tubeLift q)) (μ.prod volume.toSphere) := by
    convert integrable_tube_compact_mul (μ := μ) hσ hc hσD hM hf using 1
    ext q; ring
  simp only [tubeIntegral,mul_add]
  exact integral_add (hi f hf) (hi g hg)

omit [NormedAddCommGroup S] [BorelSpace S] [μ.IsAddHaarMeasure] in
lemma tubeIntegral_smul (M f : S × E → ℝ) (σ : S → ℝ) (c : ℝ) :
    tubeIntegral μ M σ (fun q => c*f q) = c*tubeIntegral μ M σ f := by
  simp only [tubeIntegral]
  simp_rw [show ∀ q : S × sphere (0:E) 1,
    M (tubeLift q)*σ q.1*(c*f (tubeLift q)) = c*(M (tubeLift q)*σ q.1*f (tubeLift q)) by intro q; ring]
  exact integral_const_mul _ _

section
variable [NormedSpace ℝ S] [FiniteDimensional ℝ S]

lemma tubeIntegral_base {M g : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hσ : Continuous σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    (hM : ContinuousOn M (tubeOpenSet D)) (hg : ContinuousOn g (tubeOpenSet D)) :
    tubeIntegral μ M σ g =
      ∫ e : sphere (0:E) 1, (∫ s, M (s,e)*σ s*g (s,e) ∂μ) ∂volume.toSphere := by
  have hi : Integrable (fun q : S × sphere (0:E) 1 => M (tubeLift q)*σ q.1*g (tubeLift q)) (μ.prod volume.toSphere) := by
    convert integrable_tube_compact_mul (μ := μ) hσ hc hσD hM hg using 1
    ext q; ring
  exact (integral_prod _ hi).trans (integral_integral_swap hi)

lemma tubeIntegral_angular {M g : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hσ : Continuous σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    (hM : ContinuousOn M (tubeOpenSet D)) (hg : ContinuousOn g (tubeOpenSet D)) :
    tubeIntegral μ M σ g =
      ∫ s, σ s*(∫ e : sphere (0:E) 1, M (s,e)*g (s,e) ∂volume.toSphere) ∂μ := by
  have hi : Integrable (fun q : S × sphere (0:E) 1 => M (tubeLift q)*σ q.1*g (tubeLift q)) (μ.prod volume.toSphere) := by
    convert integrable_tube_compact_mul (μ := μ) hσ hc hσD hM hg using 1
    ext q; ring
  rw [tubeIntegral,integral_prod _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    change (∫ e : sphere (0:E) 1, M (s,e)*σ s*g (s,e) ∂volume.toSphere) = _
    simp_rw [show ∀ e : sphere (0:E) 1,
      M (s,e)*σ s*g (s,e) = σ s*(M (s,e)*g (s,e)) by intro e; ring]
    exact integral_const_mul _ _

end

omit [BorelSpace S] [μ.IsAddHaarMeasure] in
lemma tubeIntegral_congr_on {M f g : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hσD : tsupport σ ⊆ D) (hfg : ∀ q ∈ tubeOpenSet D, f q = g q) :
    tubeIntegral μ M σ f = tubeIntegral μ M σ g := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  dsimp only
  by_cases hq : q.1 ∈ tsupport σ
  · rw [hfg (tubeLift q) (tubeLift_mem q (hσD hq))]
  · simp [image_eq_zero_of_notMem_tsupport hq]

omit [NormedAddCommGroup S] [BorelSpace S] [μ.IsAddHaarMeasure] in
lemma tubeIntegral_zero (M : S × E → ℝ) (σ : S → ℝ) :
    tubeIntegral μ M σ (fun _ => 0) = 0 := by simp [tubeIntegral]

omit [MeasurableSpace S] [BorelSpace S] in
lemma tsupport_sq_subset {σ : S → ℝ} : tsupport (fun s => σ s^2) ⊆ tsupport σ := by
  simpa only [pow_two] using (tsupport_mul_subset_left (f := σ) (g := σ))

omit [MeasurableSpace S] [BorelSpace S] in
lemma compactSupport_sq {σ : S → ℝ} (hc : HasCompactSupport σ) :
    HasCompactSupport (fun s => σ s^2) :=
  hc.isCompact.of_isClosed_subset isClosed_closure tsupport_sq_subset

lemma integrable_tube_supported {f : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    (hf : ContinuousOn f (tubeOpenSet D))
    (hz : ∀ s ∉ tsupport σ, ∀ e : E, f (s,e) = 0) :
    Integrable (fun q : S × sphere (0:E) 1 => f (tubeLift q)) (μ.prod volume.toSphere) := by
  have hs : Function.support (fun q : S × sphere (0:E) 1 => f (tubeLift q)) ⊆
      tsupport σ ×ˢ (Set.univ : Set (sphere (0:E) 1)) := by
    intro q hq
    refine ⟨?_,Set.mem_univ _⟩
    by_contra hn
    exact hq (hz q.1 hn q.2)
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  exact ContinuousOn.integrableOn_compact (hc.isCompact.prod isCompact_univ)
    (hf.comp continuous_tubeLift.continuousOn (fun q hq => tubeLift_mem q (hσD hq.1)))

omit [BorelSpace S] [μ.IsAddHaarMeasure] in
lemma tubeIntegral_congr_sphere {M f g : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hσD : tsupport σ ⊆ D) (hfg : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → f (s,e) = g (s,e)) :
    tubeIntegral μ M σ f = tubeIntegral μ M σ g := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  dsimp only
  by_cases hq : q.1 ∈ tsupport σ
  · rw [show f (tubeLift q) = g (tubeLift q) from
      hfg q.1 (hσD hq) q.2 (mem_sphere_zero_iff_norm.1 q.2.property)]
  · simp [image_eq_zero_of_notMem_tsupport hq]

lemma tubeIntegral_linearCombination {M f g : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hσ : Continuous σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    (hM : ContinuousOn M (tubeOpenSet D)) (hf : ContinuousOn f (tubeOpenSet D))
    (hg : ContinuousOn g (tubeOpenSet D)) (a b : ℝ) :
    tubeIntegral μ M σ (fun q => a*f q+b*g q) = a*tubeIntegral μ M σ f+b*tubeIntegral μ M σ g := by
  calc
    _ = tubeIntegral μ M σ (fun q => a*f q)+tubeIntegral μ M σ (fun q => b*g q) := by
      exact tubeIntegral_add hσ hc hσD hM (continuousOn_const.mul hf) (continuousOn_const.mul hg)
    _ = _ := by rw [tubeIntegral_smul,tubeIntegral_smul]

end AffineBernstein
end

end OAI
