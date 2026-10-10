import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.RadialPhysicalJets

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

def shiftedLogSource (a : E → ℝ) (V : E → E) (s : ℝ) (b z : E) : ℝ :=
  logSingularSource a V s b (z-b)
def shiftedSqrtSource (a : E → ℝ) (V : E → E) (s : ℝ) (b z : E) : ℝ :=
  sqrtSingularSource a V s b (z-b)

def shiftedLogShell (a : E → ℝ) (V : E → E) (r s : ℝ) (b z : E) : ℝ :=
  shellCutoff r (z-b) * shiftedLogSource a V s b z
def shiftedSqrtShell (a : E → ℝ) (V : E → E) (r s : ℝ) (b z : E) : ℝ :=
  shellCutoff r (z-b) * shiftedSqrtSource a V s b z

def shiftedLogInner (a : E → ℝ) (V : E → E) (s : ℝ) (b z : E) : ℝ :=
  scaledCutoff s (z-b) * shiftedLogSource a V s b z
def shiftedSqrtInner (a : E → ℝ) (V : E → E) (s : ℝ) (b z : E) : ℝ :=
  scaledCutoff s (z-b) * shiftedSqrtSource a V s b z

omit [HasContDiffBump E] [ProperSpace E] in
lemma shiftedLogSource_smooth (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (shiftedLogSource a V s b) := by
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ (logPotential s) (z-b) (V z)) :=
    (((logPotential_smooth hs).fderiv_right (by simp)).comp
      (contDiff_id.sub contDiff_const)).clm_apply hV
  have he : shiftedLogSource a V s b =
      fun z => a (z-b) * fderiv ℝ (logPotential s) (z-b) (V z) := by
    funext z
    simp [shiftedLogSource,logSingularSource,logGradientProfile_eq_fderiv hs]
  rw [he]
  exact (ha.comp (contDiff_id.sub contDiff_const)).mul hd

omit [HasContDiffBump E] [ProperSpace E] in
lemma shiftedSqrtSource_smooth (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (shiftedSqrtSource a V s b) := by
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ (sqrtPotential s) (z-b) (V z)) :=
    (((sqrtPotential_smooth hs).fderiv_right (by simp)).comp
      (contDiff_id.sub contDiff_const)).clm_apply hV
  have he : shiftedSqrtSource a V s b =
      fun z => a (z-b) * fderiv ℝ (sqrtPotential s) (z-b) (V z) := by
    funext z
    simp [shiftedSqrtSource,sqrtSingularSource,sqrtGradientProfile_eq_fderiv hs]
  rw [he]
  exact (ha.comp (contDiff_id.sub contDiff_const)).mul hd

omit [ProperSpace E] in
lemma shiftedLogShell_smooth (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) (r : ℝ) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (shiftedLogShell a V r s b) :=
  ((shellCutoff_smooth r).comp (contDiff_id.sub contDiff_const)).mul
    (shiftedLogSource_smooth a V ha hV hs b)
omit [ProperSpace E] in
lemma shiftedSqrtShell_smooth (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) (r : ℝ) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (shiftedSqrtShell a V r s b) :=
  ((shellCutoff_smooth r).comp (contDiff_id.sub contDiff_const)).mul
    (shiftedSqrtSource_smooth a V ha hV hs b)
omit [ProperSpace E] in
lemma shiftedLogInner_smooth (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (shiftedLogInner a V s b) :=
  ((scaledCutoff_smooth s).comp (contDiff_id.sub contDiff_const)).mul
    (shiftedLogSource_smooth a V ha hV hs b)
omit [ProperSpace E] in
lemma shiftedSqrtInner_smooth (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (shiftedSqrtInner a V s b) :=
  ((scaledCutoff_smooth s).comp (contDiff_id.sub contDiff_const)).mul
    (shiftedSqrtSource_smooth a V ha hV hs b)

omit [ProperSpace E] in
lemma shiftedLogShell_weight (a ρ : E → ℝ) (V : E → E) (r s : ℝ) (b z : E) :
    ρ z * shiftedLogShell a V r s b z =
      shiftedLogShell a (fun w => ρ w • V w) r s b z := by
  simp [shiftedLogShell,shiftedLogSource,logSingularSource,logGradientProfile,
    real_inner_smul_right]
  ring
omit [ProperSpace E] in
lemma shiftedSqrtShell_weight (a ρ : E → ℝ) (V : E → E) (r s : ℝ) (b z : E) :
    ρ z * shiftedSqrtShell a V r s b z =
      shiftedSqrtShell a (fun w => ρ w • V w) r s b z := by
  simp [shiftedSqrtShell,shiftedSqrtSource,sqrtSingularSource,sqrtGradientProfile,
    real_inner_smul_right]
  ring
omit [ProperSpace E] in
lemma shiftedLogInner_weight (a ρ : E → ℝ) (V : E → E) (s : ℝ) (b z : E) :
    ρ z * shiftedLogInner a V s b z =
      shiftedLogInner a (fun w => ρ w • V w) s b z := by
  simp [shiftedLogInner,shiftedLogSource,logSingularSource,logGradientProfile,
    real_inner_smul_right]
  ring
omit [ProperSpace E] in
lemma shiftedSqrtInner_weight (a ρ : E → ℝ) (V : E → E) (s : ℝ) (b z : E) :
    ρ z * shiftedSqrtInner a V s b z =
      shiftedSqrtInner a (fun w => ρ w • V w) s b z := by
  simp [shiftedSqrtInner,shiftedSqrtSource,sqrtSingularSource,sqrtGradientProfile,
    real_inner_smul_right]
  ring

lemma shiftedLogShell_derivatives_bounded (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioc (0:ℝ) R, ∀ s ∈ Icc (0:ℝ) r, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (shiftedLogShell a V r s b) x‖ ≤ C/r^(n+1) := by
  obtain ⟨C,hC,hb⟩ := logShell_derivatives_bounded a V ha hV hK R n
  refine ⟨C,hC,fun r hr s hs b hbK x => ?_⟩
  change ‖iteratedFDeriv ℝ n (fun z => (fun y => shellCutoff r y * logSingularSource a V s b y) (z-b)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub (f := fun y => shellCutoff r y * logSingularSource a V s b y) n b x]
  exact hb r hr s hs b hbK (x-b)
lemma shiftedSqrtShell_derivatives_bounded (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioc (0:ℝ) R, ∀ s ∈ Icc (0:ℝ) r, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (shiftedSqrtShell a V r s b) x‖ ≤ C/r^n := by
  obtain ⟨C,hC,hb⟩ := sqrtShell_derivatives_bounded a V ha hV hK R n
  refine ⟨C,hC,fun r hr s hs b hbK x => ?_⟩
  change ‖iteratedFDeriv ℝ n (fun z => (fun y => shellCutoff r y * sqrtSingularSource a V s b y) (z-b)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub (f := fun y => shellCutoff r y * sqrtSingularSource a V s b y) n b x]
  exact hb r hr s hs b hbK (x-b)
lemma shiftedLogInner_derivatives_bounded (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Ioc (0:ℝ) R, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (shiftedLogInner a V s b) x‖ ≤ C/s^(n+1) := by
  obtain ⟨C,hC,hb⟩ := logInner_derivatives_bounded a V ha hV hK R n
  refine ⟨C,hC,fun s hs b hbK x => ?_⟩
  change ‖iteratedFDeriv ℝ n (fun z => (fun y => scaledCutoff s y * logSingularSource a V s b y) (z-b)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub (f := fun y => scaledCutoff s y * logSingularSource a V s b y) n b x]
  exact hb s hs b hbK (x-b)
lemma shiftedSqrtInner_derivatives_bounded (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Ioc (0:ℝ) R, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (shiftedSqrtInner a V s b) x‖ ≤ C/s^n := by
  obtain ⟨C,hC,hb⟩ := sqrtInner_derivatives_bounded a V ha hV hK R n
  refine ⟨C,hC,fun s hs b hbK x => ?_⟩
  change ‖iteratedFDeriv ℝ n (fun z => (fun y => scaledCutoff s y * sqrtSingularSource a V s b y) (z-b)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub (f := fun y => scaledCutoff s y * sqrtSingularSource a V s b y) n b x]
  exact hb s hs b hbK (x-b)

end TamingCompatibility.RadialPotential

end

end OAI
