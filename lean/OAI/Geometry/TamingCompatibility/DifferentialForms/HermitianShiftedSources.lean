import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianPhysicalJets

namespace OAI


noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

def shiftedLogSource (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (s : ℝ) (b z : E) : ℝ :=
  logSingularSource W a V s b (z-b)
def shiftedSqrtSource (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (s : ℝ) (b z : E) : ℝ :=
  sqrtSingularSource W a V s b (z-b)

def shiftedLogShell (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (r s : ℝ) (b z : E) : ℝ :=
  shellCutoff r (z-b) * shiftedLogSource W a V s b z
def shiftedSqrtShell (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (r s : ℝ) (b z : E) : ℝ :=
  shellCutoff r (z-b) * shiftedSqrtSource W a V s b z

def shiftedLogInner (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (s : ℝ) (b z : E) : ℝ :=
  scaledCutoff s (z-b) * shiftedLogSource W a V s b z
def shiftedSqrtInner (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E) (s : ℝ) (b z : E) : ℝ :=
  scaledCutoff s (z-b) * shiftedSqrtSource W a V s b z

omit [HasContDiffBump E] [ProperSpace E] in
lemma shiftedLogSource_smooth (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (shiftedLogSource W a V s b) := by
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ (hermitianLogPotential (W b) s) (z-b) (V z)) :=
    (((hermitianLogPotential_smooth (W b) hs).fderiv_right (by simp)).comp
      (contDiff_id.sub contDiff_const)).clm_apply hV
  have he : shiftedLogSource W a V s b =
      fun z => a (z-b) * fderiv ℝ (hermitianLogPotential (W b) s) (z-b) (V z) := by
    funext z
    simp [shiftedLogSource,logSingularSource,hermitianLogGradient_eq_fderiv (W b) hs]
  rw [he]
  exact (ha.comp (contDiff_id.sub contDiff_const)).mul hd

omit [HasContDiffBump E] [ProperSpace E] in
lemma shiftedSqrtSource_smooth (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (shiftedSqrtSource W a V s b) := by
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ (hermitianSqrtPotential (W b) s) (z-b) (V z)) :=
    (((hermitianSqrtPotential_smooth (W b) hs).fderiv_right (by simp)).comp
      (contDiff_id.sub contDiff_const)).clm_apply hV
  have he : shiftedSqrtSource W a V s b =
      fun z => a (z-b) * fderiv ℝ (hermitianSqrtPotential (W b) s) (z-b) (V z) := by
    funext z
    simp [shiftedSqrtSource,sqrtSingularSource,hermitianSqrtGradient_eq_fderiv (W b) hs]
  rw [he]
  exact (ha.comp (contDiff_id.sub contDiff_const)).mul hd

omit [ProperSpace E] in
lemma shiftedLogShell_smooth (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) (r : ℝ) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (shiftedLogShell W a V r s b) :=
  ((shellCutoff_smooth r).comp (contDiff_id.sub contDiff_const)).mul
    (shiftedLogSource_smooth W a V ha hV hs b)
omit [ProperSpace E] in
lemma shiftedSqrtShell_smooth (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) (r : ℝ) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (shiftedSqrtShell W a V r s b) :=
  ((shellCutoff_smooth r).comp (contDiff_id.sub contDiff_const)).mul
    (shiftedSqrtSource_smooth W a V ha hV hs b)
omit [ProperSpace E] in
lemma shiftedLogInner_smooth (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (shiftedLogInner W a V s b) :=
  ((scaledCutoff_smooth s).comp (contDiff_id.sub contDiff_const)).mul
    (shiftedLogSource_smooth W a V ha hV hs b)
omit [ProperSpace E] in
lemma shiftedSqrtInner_smooth (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (shiftedSqrtInner W a V s b) :=
  ((scaledCutoff_smooth s).comp (contDiff_id.sub contDiff_const)).mul
    (shiftedSqrtSource_smooth W a V ha hV hs b)

omit [ProperSpace E] in
lemma shiftedLogShell_weight (W : E → E →L[ℝ] E) (a ρ : E → ℝ) (V : E → E) (r s : ℝ) (b z : E) :
    ρ z * shiftedLogShell W a V r s b z =
      shiftedLogShell W a (fun w => ρ w • V w) r s b z := by
  simp [shiftedLogShell,shiftedLogSource,logSingularSource,hermitianLogGradientProfile,map_smul,
    real_inner_smul_right]
  ring
omit [ProperSpace E] in
lemma shiftedSqrtShell_weight (W : E → E →L[ℝ] E) (a ρ : E → ℝ) (V : E → E) (r s : ℝ) (b z : E) :
    ρ z * shiftedSqrtShell W a V r s b z =
      shiftedSqrtShell W a (fun w => ρ w • V w) r s b z := by
  simp [shiftedSqrtShell,shiftedSqrtSource,sqrtSingularSource,hermitianSqrtGradientProfile,map_smul,
    real_inner_smul_right]
  ring
omit [ProperSpace E] in
lemma shiftedLogInner_weight (W : E → E →L[ℝ] E) (a ρ : E → ℝ) (V : E → E) (s : ℝ) (b z : E) :
    ρ z * shiftedLogInner W a V s b z =
      shiftedLogInner W a (fun w => ρ w • V w) s b z := by
  simp [shiftedLogInner,shiftedLogSource,logSingularSource,hermitianLogGradientProfile,map_smul,
    real_inner_smul_right]
  ring
omit [ProperSpace E] in
lemma shiftedSqrtInner_weight (W : E → E →L[ℝ] E) (a ρ : E → ℝ) (V : E → E) (s : ℝ) (b z : E) :
    ρ z * shiftedSqrtInner W a V s b z =
      shiftedSqrtInner W a (fun w => ρ w • V w) s b z := by
  simp [shiftedSqrtInner,shiftedSqrtSource,sqrtSingularSource,hermitianSqrtGradientProfile,map_smul,
    real_inner_smul_right]
  ring

lemma shiftedLogShell_derivatives_bounded (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioc (0:ℝ) R, ∀ s ∈ Icc (0:ℝ) r, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (shiftedLogShell W a V r s b) x‖ ≤ C/r^(n+1) := by
  obtain ⟨C,hC,hb⟩ := logShell_derivatives_bounded W a V hW ha hV hK R n
  refine ⟨C,hC,fun r hr s hs b hbK x => ?_⟩
  change ‖iteratedFDeriv ℝ n (fun z => (fun y => shellCutoff r y * logSingularSource W a V s b y) (z-b)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub (f := fun y => shellCutoff r y * logSingularSource W a V s b y) n b x]
  exact hb r hr s hs b hbK (x-b)
lemma shiftedSqrtShell_derivatives_bounded (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioc (0:ℝ) R, ∀ s ∈ Icc (0:ℝ) r, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (shiftedSqrtShell W a V r s b) x‖ ≤ C/r^n := by
  obtain ⟨C,hC,hb⟩ := sqrtShell_derivatives_bounded W a V hW ha hV hK R n
  refine ⟨C,hC,fun r hr s hs b hbK x => ?_⟩
  change ‖iteratedFDeriv ℝ n (fun z => (fun y => shellCutoff r y * sqrtSingularSource W a V s b y) (z-b)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub (f := fun y => shellCutoff r y * sqrtSingularSource W a V s b y) n b x]
  exact hb r hr s hs b hbK (x-b)
lemma shiftedLogInner_derivatives_bounded (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Ioc (0:ℝ) R, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (shiftedLogInner W a V s b) x‖ ≤ C/s^(n+1) := by
  obtain ⟨C,hC,hb⟩ := logInner_derivatives_bounded W a V hW ha hV hK R n
  refine ⟨C,hC,fun s hs b hbK x => ?_⟩
  change ‖iteratedFDeriv ℝ n (fun z => (fun y => scaledCutoff s y * logSingularSource W a V s b y) (z-b)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub (f := fun y => scaledCutoff s y * logSingularSource W a V s b y) n b x]
  exact hb s hs b hbK (x-b)
lemma shiftedSqrtInner_derivatives_bounded (W : E → E →L[ℝ] E) (a : E → ℝ) (V : E → E)
    (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Ioc (0:ℝ) R, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (shiftedSqrtInner W a V s b) x‖ ≤ C/s^n := by
  obtain ⟨C,hC,hb⟩ := sqrtInner_derivatives_bounded W a V hW ha hV hK R n
  refine ⟨C,hC,fun s hs b hbK x => ?_⟩
  change ‖iteratedFDeriv ℝ n (fun z => (fun y => scaledCutoff s y * sqrtSingularSource W a V s b y) (z-b)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub (f := fun y => scaledCutoff s y * sqrtSingularSource W a V s b y) n b x]
  exact hb s hs b hbK (x-b)

end TamingCompatibility.HermitianRadial

end

end OAI
