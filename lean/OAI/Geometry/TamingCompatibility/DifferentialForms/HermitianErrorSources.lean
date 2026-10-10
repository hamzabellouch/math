import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.HermitianCutoffErrors
import OAI.Geometry.TamingCompatibility.Charts.HermitianBundleSources

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

def shiftedLogError (W : E → E →L[ℝ] E) (V : E → E) (R s : ℝ) (b z : E) : ℝ :=
  cutoffLogError W V R (s,b) (z-b)
def shiftedSqrtError (W : E → E →L[ℝ] E) (V : E → E) (R s : ℝ) (b z : E) : ℝ :=
  cutoffSqrtError W V R (s,b) (z-b)

omit [ProperSpace E] in
lemma shiftedLogError_smooth (W : E → E →L[ℝ] E) (V : E → E) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    ContDiff ℝ ∞ (shiftedLogError W V R s b) :=
  (cutoffLogError_smooth W V hW hV hR).comp
    (contDiff_const.prodMk (contDiff_id.sub contDiff_const))
omit [ProperSpace E] in
lemma shiftedSqrtError_smooth (W : E → E →L[ℝ] E) (V : E → E) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    ContDiff ℝ ∞ (shiftedSqrtError W V R s b) :=
  (cutoffSqrtError_smooth W V hW hV hR).comp
    (contDiff_const.prodMk (contDiff_id.sub contDiff_const))
omit [ProperSpace E] in
lemma shiftedLogError_support (W : E → E →L[ℝ] E) (V : E → E) {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    tsupport (shiftedLogError W V R s b) ⊆ closedBall b (2*R) :=
  tsupport_translated_subset b _ (cutoffLogError_tsupport W V hR (s,b))
omit [ProperSpace E] in
lemma shiftedSqrtError_support (W : E → E →L[ℝ] E) (V : E → E) {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    tsupport (shiftedSqrtError W V R s b) ⊆ closedBall b (2*R) :=
  tsupport_translated_subset b _ (cutoffSqrtError_tsupport W V hR (s,b))

omit [ProperSpace E] in
lemma shiftedLogError_weight (ρ : E → ℝ) (W : E → E →L[ℝ] E) (V : E → E) (R s : ℝ) (b z : E) :
    ρ z * shiftedLogError W V R s b z = shiftedLogError W (fun w => ρ w • V w) R s b z := by
  simp only [shiftedLogError,cutoffLogError,add_sub_cancel,ContinuousLinearMap.map_smul,smul_eq_mul]
  ring
omit [ProperSpace E] in
lemma shiftedSqrtError_weight (ρ : E → ℝ) (W : E → E →L[ℝ] E) (V : E → E) (R s : ℝ) (b z : E) :
    ρ z * shiftedSqrtError W V R s b z = shiftedSqrtError W (fun w => ρ w • V w) R s b z := by
  simp only [shiftedSqrtError,cutoffSqrtError,add_sub_cancel,ContinuousLinearMap.map_smul,smul_eq_mul]
  ring

lemma shiftedLogError_derivatives_bounded (W : E → E →L[ℝ] E) (V : E → E) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    {R : ℝ} (hR : 0 < R) {K : Set E} (hK : IsCompact K) (S : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) S, ∀ b ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (shiftedLogError W V R s b) z‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := cutoffLogError_derivatives_bounded W V hW hV hR hK S n
  refine ⟨C,hC,fun s hs b hbK z => ?_⟩
  change ‖iteratedFDeriv ℝ n (fun z => cutoffLogError W V R (s,b) (z-b)) z‖ ≤ _
  rw [iteratedFDeriv_comp_sub]
  exact hb s hs b hbK (z-b)
lemma shiftedSqrtError_derivatives_bounded (W : E → E →L[ℝ] E) (V : E → E) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    {R : ℝ} (hR : 0 < R) {K : Set E} (hK : IsCompact K) (S : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) S, ∀ b ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (shiftedSqrtError W V R s b) z‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := cutoffSqrtError_derivatives_bounded W V hW hV hR hK S n
  refine ⟨C,hC,fun s hs b hbK z => ?_⟩
  change ‖iteratedFDeriv ℝ n (fun z => cutoffSqrtError W V R (s,b) (z-b)) z‖ ≤ _
  rw [iteratedFDeriv_comp_sub]
  exact hb s hs b hbK (z-b)

variable (W : E → E →L[ℝ] E) (V : E → E) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V) {R : ℝ} (hR : 0 < R)

def logErrorSchwartz (s : ℝ) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedLogError W V R s b) :=
    (isCompact_closedBall b (2*R)).of_isClosed_subset (isClosed_tsupport _)
      (shiftedLogError_support W V hR s b)
  exact hc.toSchwartzMap (shiftedLogError_smooth W V hW hV hR s b)
def sqrtErrorSchwartz (s : ℝ) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedSqrtError W V R s b) :=
    (isCompact_closedBall b (2*R)).of_isClosed_subset (isClosed_tsupport _)
      (shiftedSqrtError_support W V hR s b)
  exact hc.toSchwartzMap (shiftedSqrtError_smooth W V hW hV hR s b)

def logErrorSupported (K : Set E) (s : ℝ) (b : E) (hb : closedBall b (2*R) ⊆ K) :
    supportedSchwartz K :=
  ⟨logErrorSchwartz W V hW hV hR s b,(shiftedLogError_support W V hR s b).trans hb⟩
def sqrtErrorSupported (K : Set E) (s : ℝ) (b : E) (hb : closedBall b (2*R) ⊆ K) :
    supportedSchwartz K :=
  ⟨sqrtErrorSchwartz W V hW hV hR s b,(shiftedSqrtError_support W V hR s b).trans hb⟩

lemma logErrorSchwartz_uniform_inputs (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    {K : Set E} (hK : IsCompact K) (S : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) S, ∀ b ∈ K,
      (∀ z, |logErrorSchwartz W V hW hV hR s b z| ≤ C) ∧
      (∀ n ≤ N, ∀ z, ‖iteratedFDeriv ℝ n (fun z => ρ z * logErrorSchwartz W V hW hV hR s b z) z‖ ≤ C) := by
  classical
  obtain ⟨D₀,hD₀,hb₀⟩ := shiftedLogError_derivatives_bounded W V hW hV hR hK S 0
  choose D hD hb using fun n => shiftedLogError_derivatives_bounded W
    (fun w => ρ w • V w) hW (hρ.smul hV) hR hK S n
  obtain ⟨C,hC,hC₀,hCD⟩ := finite_radialJet_constant D hD D₀ hD₀ N
  refine ⟨C,hC,?_⟩
  intro s hs b hbK
  constructor
  · intro z
    have h := hb₀ s hs b hbK z
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h
    exact h.trans hC₀
  · intro n hn z
    have he : (fun z => ρ z * logErrorSchwartz W V hW hV hR s b z) =
        shiftedLogError W (fun w => ρ w • V w) R s b :=
      funext (shiftedLogError_weight ρ W V R s b)
    rw [he]
    exact (hb n s hs b hbK z).trans ((hCD n hn).trans
      (div_le_self hC (one_le_pow₀ (by norm_num))))

lemma sqrtErrorSchwartz_uniform_inputs (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    {K : Set E} (hK : IsCompact K) (S : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) S, ∀ b ∈ K,
      (∀ z, |sqrtErrorSchwartz W V hW hV hR s b z| ≤ C) ∧
      (∀ n ≤ N, ∀ z, ‖iteratedFDeriv ℝ n (fun z => ρ z * sqrtErrorSchwartz W V hW hV hR s b z) z‖ ≤ C) := by
  classical
  obtain ⟨D₀,hD₀,hb₀⟩ := shiftedSqrtError_derivatives_bounded W V hW hV hR hK S 0
  choose D hD hb using fun n => shiftedSqrtError_derivatives_bounded W
    (fun w => ρ w • V w) hW (hρ.smul hV) hR hK S n
  obtain ⟨C,hC,hC₀,hCD⟩ := finite_radialJet_constant D hD D₀ hD₀ N
  refine ⟨C,hC,?_⟩
  intro s hs b hbK
  constructor
  · intro z
    have h := hb₀ s hs b hbK z
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h
    exact h.trans hC₀
  · intro n hn z
    have he : (fun z => ρ z * sqrtErrorSchwartz W V hW hV hR s b z) =
        shiftedSqrtError W (fun w => ρ w • V w) R s b :=
      funext (shiftedSqrtError_weight ρ W V R s b)
    rw [he]
    exact (hb n s hs b hbK z).trans ((hCD n hn).trans
      (div_le_self hC (one_le_pow₀ (by norm_num))))

end TamingCompatibility.HermitianRadial

end
end

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]
variable (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
  (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R)

def logSourceSchwartz {s : ℝ} (hs : 0 < s) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedLogSource W a V s b) :=
    (isCompact_closedBall b R).of_isClosed_subset (isClosed_tsupport _)
      (shiftedLogSource_support W a V s b R haR)
  exact hc.toSchwartzMap (shiftedLogSource_smooth W a V ha hV hs b)

def sqrtSourceSchwartz {s : ℝ} (hs : 0 < s) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedSqrtSource W a V s b) :=
    (isCompact_closedBall b R).of_isClosed_subset (isClosed_tsupport _)
      (shiftedSqrtSource_support W a V s b R haR)
  exact hc.toSchwartzMap (shiftedSqrtSource_smooth W a V ha hV hs b)

lemma logSourceSchwartz_reconstruction {s : ℝ} (hs : 0 < s) (b : E)
    (N : ℕ) (hN : R ≤ s*2^N) :
    logSourceSchwartz W a V ha hV R haR hs b = logInnerSchwartz W a V ha hV hs b +
    ∑ j ∈ Finset.range N, logShellSchwartz W a V ha hV (mul_pos hs (by positivity : 0 < (2:ℝ)^j)) hs b := by
  apply SchwartzMap.ext
  intro z
  change shiftedLogSource W a V s b z = shiftedLogInner W a V s b z +
    (∑ j ∈ Finset.range N, logShellSchwartz W a V ha hV (mul_pos hs (by positivity : 0 < (2:ℝ)^j)) hs b) z
  rw [sum_apply]
  change shiftedLogSource W a V s b z = scaledCutoff s (z-b) * shiftedLogSource W a V s b z +
    ∑ j ∈ Finset.range N, shellCutoff (s*2^j) (z-b) * shiftedLogSource W a V s b z
  rw [← Finset.sum_mul,← add_mul,dyadic_cutoff_telescope]
  by_cases hz : ‖z-b‖ ≤ s*2^N
  · rw [scaledCutoff_one (mul_pos hs (by positivity)) hz,one_mul]
  · have ha0 : a (z-b) = 0 := image_eq_zero_of_notMem_tsupport (fun h => by
      have hh := haR h
      simp only [mem_closedBall,dist_zero_right] at hh
      exact hz (hh.trans hN))
    simp [shiftedLogSource,logSingularSource,ha0]

lemma sqrtSourceSchwartz_reconstruction {s : ℝ} (hs : 0 < s) (b : E)
    (N : ℕ) (hN : R ≤ s*2^N) :
    sqrtSourceSchwartz W a V ha hV R haR hs b = sqrtInnerSchwartz W a V ha hV hs b +
    ∑ j ∈ Finset.range N, sqrtShellSchwartz W a V ha hV (mul_pos hs (by positivity : 0 < (2:ℝ)^j)) hs b := by
  apply SchwartzMap.ext
  intro z
  change shiftedSqrtSource W a V s b z = shiftedSqrtInner W a V s b z +
    (∑ j ∈ Finset.range N, sqrtShellSchwartz W a V ha hV (mul_pos hs (by positivity : 0 < (2:ℝ)^j)) hs b) z
  rw [sum_apply]
  change shiftedSqrtSource W a V s b z = scaledCutoff s (z-b) * shiftedSqrtSource W a V s b z +
    ∑ j ∈ Finset.range N, shellCutoff (s*2^j) (z-b) * shiftedSqrtSource W a V s b z
  rw [← Finset.sum_mul,← add_mul,dyadic_cutoff_telescope]
  by_cases hz : ‖z-b‖ ≤ s*2^N
  · rw [scaledCutoff_one (mul_pos hs (by positivity)) hz,one_mul]
  · have ha0 : a (z-b) = 0 := image_eq_zero_of_notMem_tsupport (fun h => by
      have hh := haR h
      simp only [mem_closedBall,dist_zero_right] at hh
      exact hz (hh.trans hN))
    simp [shiftedSqrtSource,sqrtSingularSource,ha0]

end TamingCompatibility.HermitianRadial

end
end

end
end

end OAI
