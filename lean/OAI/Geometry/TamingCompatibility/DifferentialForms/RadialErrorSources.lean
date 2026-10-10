import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.RadialCutoffErrors
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialScalarOff
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialJetConstants

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

omit [InnerProductSpace ℝ E] [HasContDiffBump E] [ProperSpace E] in
lemma tsupport_translated_subset {f : E → ℝ} (b : E) (R : ℝ)
    (hf : tsupport f ⊆ closedBall 0 R) :
    tsupport (fun z => f (z-b)) ⊆ closedBall b R := by
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  have hb := hf (subset_tsupport f hz)
  simpa only [mem_closedBall,dist_zero_right,dist_eq_norm,sub_zero] using hb

def shiftedLogError (V : E → E) (R s : ℝ) (b z : E) : ℝ :=
  cutoffLogError V R (s,b) (z-b)
def shiftedSqrtError (V : E → E) (R s : ℝ) (b z : E) : ℝ :=
  cutoffSqrtError V R (s,b) (z-b)

omit [ProperSpace E] in
lemma shiftedLogError_smooth (V : E → E) (hV : ContDiff ℝ ∞ V)
    {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    ContDiff ℝ ∞ (shiftedLogError V R s b) :=
  (cutoffLogError_smooth V hV hR).comp
    (contDiff_const.prodMk (contDiff_id.sub contDiff_const))
omit [ProperSpace E] in
lemma shiftedSqrtError_smooth (V : E → E) (hV : ContDiff ℝ ∞ V)
    {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    ContDiff ℝ ∞ (shiftedSqrtError V R s b) :=
  (cutoffSqrtError_smooth V hV hR).comp
    (contDiff_const.prodMk (contDiff_id.sub contDiff_const))
omit [ProperSpace E] in
lemma shiftedLogError_support (V : E → E) {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    tsupport (shiftedLogError V R s b) ⊆ closedBall b (2*R) :=
  tsupport_translated_subset b _ (cutoffLogError_tsupport V hR (s,b))
omit [ProperSpace E] in
lemma shiftedSqrtError_support (V : E → E) {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    tsupport (shiftedSqrtError V R s b) ⊆ closedBall b (2*R) :=
  tsupport_translated_subset b _ (cutoffSqrtError_tsupport V hR (s,b))

omit [ProperSpace E] in
lemma shiftedLogError_weight (ρ : E → ℝ) (V : E → E) (R s : ℝ) (b z : E) :
    ρ z * shiftedLogError V R s b z = shiftedLogError (fun w => ρ w • V w) R s b z := by
  simp only [shiftedLogError,cutoffLogError,add_sub_cancel,ContinuousLinearMap.map_smul,smul_eq_mul]
  ring
omit [ProperSpace E] in
lemma shiftedSqrtError_weight (ρ : E → ℝ) (V : E → E) (R s : ℝ) (b z : E) :
    ρ z * shiftedSqrtError V R s b z = shiftedSqrtError (fun w => ρ w • V w) R s b z := by
  simp only [shiftedSqrtError,cutoffSqrtError,add_sub_cancel,ContinuousLinearMap.map_smul,smul_eq_mul]
  ring

lemma shiftedLogError_derivatives_bounded (V : E → E) (hV : ContDiff ℝ ∞ V)
    {R : ℝ} (hR : 0 < R) {K : Set E} (hK : IsCompact K) (S : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) S, ∀ b ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (shiftedLogError V R s b) z‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := cutoffLogError_derivatives_bounded V hV hR hK S n
  refine ⟨C,hC,fun s hs b hbK z => ?_⟩
  change ‖iteratedFDeriv ℝ n (fun z => cutoffLogError V R (s,b) (z-b)) z‖ ≤ _
  rw [iteratedFDeriv_comp_sub]
  exact hb s hs b hbK (z-b)
lemma shiftedSqrtError_derivatives_bounded (V : E → E) (hV : ContDiff ℝ ∞ V)
    {R : ℝ} (hR : 0 < R) {K : Set E} (hK : IsCompact K) (S : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) S, ∀ b ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (shiftedSqrtError V R s b) z‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := cutoffSqrtError_derivatives_bounded V hV hR hK S n
  refine ⟨C,hC,fun s hs b hbK z => ?_⟩
  change ‖iteratedFDeriv ℝ n (fun z => cutoffSqrtError V R (s,b) (z-b)) z‖ ≤ _
  rw [iteratedFDeriv_comp_sub]
  exact hb s hs b hbK (z-b)

variable (V : E → E) (hV : ContDiff ℝ ∞ V) {R : ℝ} (hR : 0 < R)

def logErrorSchwartz (s : ℝ) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedLogError V R s b) :=
    (isCompact_closedBall b (2*R)).of_isClosed_subset (isClosed_tsupport _)
      (shiftedLogError_support V hR s b)
  exact hc.toSchwartzMap (shiftedLogError_smooth V hV hR s b)
def sqrtErrorSchwartz (s : ℝ) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedSqrtError V R s b) :=
    (isCompact_closedBall b (2*R)).of_isClosed_subset (isClosed_tsupport _)
      (shiftedSqrtError_support V hR s b)
  exact hc.toSchwartzMap (shiftedSqrtError_smooth V hV hR s b)

def logErrorSupported (K : Set E) (s : ℝ) (b : E) (hb : closedBall b (2*R) ⊆ K) :
    supportedSchwartz K :=
  ⟨logErrorSchwartz V hV hR s b,(shiftedLogError_support V hR s b).trans hb⟩
def sqrtErrorSupported (K : Set E) (s : ℝ) (b : E) (hb : closedBall b (2*R) ⊆ K) :
    supportedSchwartz K :=
  ⟨sqrtErrorSchwartz V hV hR s b,(shiftedSqrtError_support V hR s b).trans hb⟩

lemma logErrorSchwartz_uniform_inputs (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    {K : Set E} (hK : IsCompact K) (S : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) S, ∀ b ∈ K,
      (∀ z, |logErrorSchwartz V hV hR s b z| ≤ C) ∧
      (∀ n ≤ N, ∀ z, ‖iteratedFDeriv ℝ n (fun z => ρ z * logErrorSchwartz V hV hR s b z) z‖ ≤ C) := by
  classical
  obtain ⟨D₀,hD₀,hb₀⟩ := shiftedLogError_derivatives_bounded V hV hR hK S 0
  choose D hD hb using fun n => shiftedLogError_derivatives_bounded
    (fun w => ρ w • V w) (hρ.smul hV) hR hK S n
  obtain ⟨C,hC,hC₀,hCD⟩ := finite_radialJet_constant D hD D₀ hD₀ N
  refine ⟨C,hC,?_⟩
  intro s hs b hbK
  constructor
  · intro z
    have h := hb₀ s hs b hbK z
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h
    exact h.trans hC₀
  · intro n hn z
    have he : (fun z => ρ z * logErrorSchwartz V hV hR s b z) =
        shiftedLogError (fun w => ρ w • V w) R s b :=
      funext (shiftedLogError_weight ρ V R s b)
    rw [he]
    exact (hb n s hs b hbK z).trans ((hCD n hn).trans
      (div_le_self hC (one_le_pow₀ (by norm_num))))

lemma sqrtErrorSchwartz_uniform_inputs (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    {K : Set E} (hK : IsCompact K) (S : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) S, ∀ b ∈ K,
      (∀ z, |sqrtErrorSchwartz V hV hR s b z| ≤ C) ∧
      (∀ n ≤ N, ∀ z, ‖iteratedFDeriv ℝ n (fun z => ρ z * sqrtErrorSchwartz V hV hR s b z) z‖ ≤ C) := by
  classical
  obtain ⟨D₀,hD₀,hb₀⟩ := shiftedSqrtError_derivatives_bounded V hV hR hK S 0
  choose D hD hb using fun n => shiftedSqrtError_derivatives_bounded
    (fun w => ρ w • V w) (hρ.smul hV) hR hK S n
  obtain ⟨C,hC,hC₀,hCD⟩ := finite_radialJet_constant D hD D₀ hD₀ N
  refine ⟨C,hC,?_⟩
  intro s hs b hbK
  constructor
  · intro z
    have h := hb₀ s hs b hbK z
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h
    exact h.trans hC₀
  · intro n hn z
    have he : (fun z => ρ z * sqrtErrorSchwartz V hV hR s b z) =
        shiftedSqrtError (fun w => ρ w • V w) R s b :=
      funext (shiftedSqrtError_weight ρ V R s b)
    rw [he]
    exact (hb n s hs b hbK z).trans ((hCD n hn).trans
      (div_le_self hC (one_le_pow₀ (by norm_num))))

end TamingCompatibility.RadialPotential

end

end OAI
