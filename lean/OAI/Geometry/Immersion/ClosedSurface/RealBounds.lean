import OAI.Geometry.Immersion.ClosedSurface.MeanDifferences
import OAI.Geometry.Immersion.ClosedSurface.RealModes

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

lemma norm_complexify {n : ℕ} (X : RVec n) : ‖complexify X‖ = ‖X‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg X)).mpr
    intro i
    simpa only [complexify_apply, Complex.norm_real] using norm_le_pi_norm X i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (complexify X))).mpr
    intro i
    simpa only [complexify_apply, Complex.norm_real] using norm_le_pi_norm (complexify X) i

def complexifyLI (n : ℕ) : RVec n →ₗᵢ[ℝ] Ambient n where
  toLinearMap := (complexifyCLM n).toLinearMap
  norm_map' := norm_complexify

lemma weighted_linearIsometry {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {U : Set E} (hU : UniqueDiffOn ℝ U) {f : E → X} (hf : ContDiffOn ℝ ∞ f U)
    {s C : ℝ} {m : ℕ} (hb : WeightedBound U s m C f) (A : X →ₗᵢ[ℝ] Y) :
    WeightedBound U s m C (A ∘ f) := by
  intro j hj p hp
  rw [A.norm_iteratedFDerivWithin_comp_left (hf p hp) hU hp
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))]
  exact hb j hj p hp

lemma weighted_freeSeed {F : RField 4} {U : Set Base} (hF : ContDiff ℝ ∞ F)
    (h : RealModeDomain F U) {δ τ s C D : ℝ} {m : ℕ} (hδ : 0 ≤ δ) (hτ : 0 ≤ τ)
    (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 ≤ D) {b : Base → ℝ}
    (hb : ContDiffOn ℝ ∞ b U) (hbb : WeightedBound U s m C b)
    (hbN : WeightedBound U s m D (freeNormal F)) :
    WeightedBound U s m ((Real.sqrt 2 * 2 ^ m * C * D) * (δ * τ)) (freeSeed δ τ b F) := by
  have hNc := (complexifyCLM 4).contDiff.comp_contDiffOn (contDiffOn_freeNormal hF h)
  have hbc := Complex.ofRealCLM.contDiff.comp_contDiffOn hb
  have hbNc := weighted_linearIsometry h.isOpen.uniqueDiffOn (contDiffOn_freeNormal hF h)
    hbN (complexifyLI 4)
  have hbbc := weighted_linearIsometry h.isOpen.uniqueDiffOn hb hbb Complex.ofRealLI
  have ha : WeightedBound U s m (2 ^ m * C * D)
      (fun p => (b p : ℂ) • complexify (freeNormal F p)) := by
    apply WeightedBound.pi h.isOpen.uniqueDiffOn hs (by positivity)
    · intro i; exact hbc.mul (contDiffOn_pi.mp hNc i)
    · intro i
      exact hbbc.mul h.isOpen.uniqueDiffOn hs.le hC hD hbc (contDiffOn_pi.mp hNc i)
        (hbNc.component h.isOpen.uniqueDiffOn hs.le hD hNc i)
  have hh := ha.complex_smul_pi h.isOpen.uniqueDiffOn hs (by positivity) (hbc.smul hNc)
    ((Real.sqrt 2 * δ * τ : ℝ) : ℂ)
  have he : ‖((Real.sqrt 2 * δ * τ : ℝ) : ℂ)‖ * (2 ^ m * C * D) =
      (Real.sqrt 2 * 2 ^ m * C * D) * (δ * τ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    ring
  rw [he] at hh
  apply hh.congr
  intro p hp
  ext i
  change ((Real.sqrt 2 * δ * τ * b p : ℝ) : ℂ) * complexify (freeNormal F p) i =
    ((Real.sqrt 2 * δ * τ : ℝ) : ℂ) * ((b p : ℂ) * complexify (freeNormal F p) i)
  push_cast
  ring


def normalizedMeanError (δ τ : ℝ) (F : RField 4) (b : Base → ℝ) (q : ℕ) (v w : Base) : Base → ℝ :=
  fun p => (δ ^ 2)⁻¹ * modeMeanError τ (fun p => complexify (F p))
    (freeSeed δ τ b F) (freeSeed δ τ b F) q v w p



theorem weighted_normalizedMeanError {F : RField 4} {U : Set Base} (hF : ContDiff ℝ ∞ F)
    (h : RealModeDomain F U) {δ τ s K C D : ℝ} (hδ : 0 < δ) (hτ : 0 < τ)
    (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D)
    {b : Base → ℝ} (hb : ContDiffOn ℝ ∞ b U) (q m : ℕ)
    (hc : ReconstructionCoefficientBound (fun p => complexify (F p)) U s (m + q + 2) K)
    (hbb : WeightedBound U s (m + q + 2) C b)
    (hbN : WeightedBound U s (m + q + 2) D (freeNormal F))
    (v w : Base) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    WeightedBound U s m (meanErrorConstant 4 m K q *
      (Real.sqrt 2 * 2 ^ (m + q + 2) * C * D) ^ 2 * (τ / s))
      (normalizedMeanError δ τ F b q v w) := by
  have hbV := weighted_freeSeed hF h hδ.le hτ.le hs hC hD hb hbb hbN
  have hV := freeSeed_isFree hF h δ τ hb
  have hh := weighted_modeMeanError hτ (contDiff_complexify hF) (h.complexDomain hF)
    hs hτs hs1 hK (by positivity) (by positivity) hV hV q m hc hbV hbV v w hv hw
  have hsm := contDiffOn_modeMeanError τ (h.complexDomain hF) hV.smooth hV.smooth q v w
  have hn := hh.const_smul h.isOpen.uniqueDiffOn hsm ((δ ^ 2)⁻¹)
  have he : |(δ ^ 2)⁻¹| * (meanErrorConstant 4 m K q *
      (((Real.sqrt 2 * 2 ^ (m + q + 2) * C * D) * (δ * τ)) *
        ((Real.sqrt 2 * 2 ^ (m + q + 2) * C * D) * (δ * τ)) / (s * τ))) =
      meanErrorConstant 4 m K q * (Real.sqrt 2 * 2 ^ (m + q + 2) * C * D) ^ 2 * (τ / s) := by
    rw [abs_of_nonneg (by positivity)]
    field_simp
  rw [he] at hn
  exact hn

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

lemma freeSeed_sub (δ τ : ℝ) (b c : Base → ℝ) (F : RField 4) :
    freeSeed δ τ (fun p => b p - c p) F = fun p => freeSeed δ τ b F p - freeSeed δ τ c F p := by
  ext p i
  simp only [freeSeed, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.ofReal_mul,
    Complex.ofReal_sub]
  ring

theorem weighted_normalizedMeanError_difference {F : RField 4} {U : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U) {δ τ s K C D B : ℝ}
    (hδ : 0 < δ) (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D) (hB : 0 ≤ B)
    {b c : Base → ℝ} (hb : ContDiffOn ℝ ∞ b U) (hcs : ContDiffOn ℝ ∞ c U) (q m : ℕ)
    (hc : ReconstructionCoefficientBound (fun p => complexify (F p)) U s (m + q + 2) K)
    (hbb : WeightedBound U s (m + q + 2) C b)
    (hbc : WeightedBound U s (m + q + 2) C c)
    (hbDiff : WeightedBound U s (m + q + 2) D (fun p => b p - c p))
    (hbN : WeightedBound U s (m + q + 2) B (freeNormal F))
    (v w : Base) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    WeightedBound U s m (2 * meanErrorConstant 4 m K q *
      (Real.sqrt 2 * 2 ^ (m + q + 2) * B) ^ 2 * C * D * (τ / s))
      (fun p => normalizedMeanError δ τ F b q v w p - normalizedMeanError δ τ F c q v w p) := by
  have hbV := weighted_freeSeed hF h hδ.le hτ.le hs hC hB hb hbb hbN
  have hbW := weighted_freeSeed hF h hδ.le hτ.le hs hC hB hcs hbc hbN
  have hbD := weighted_freeSeed hF h hδ.le hτ.le hs hD hB (hb.sub hcs) hbDiff hbN
  rw [freeSeed_sub] at hbD
  have hV := freeSeed_isFree hF h δ τ hb
  have hW := freeSeed_isFree hF h δ τ hcs
  have hh := weighted_modeMeanError_difference hτ (contDiff_complexify hF) (h.complexDomain hF)
    hs hτs hs1 hK (by positivity) (by positivity) hV hW q m hc hbV hbW hbD v w hv hw
  have hsm := (contDiffOn_modeMeanError τ (h.complexDomain hF) hV.smooth hV.smooth q v w).sub
    (contDiffOn_modeMeanError τ (h.complexDomain hF) hW.smooth hW.smooth q v w)
  have hn := hh.const_smul h.isOpen.uniqueDiffOn hsm ((δ ^ 2)⁻¹)
  have he : |(δ ^ 2)⁻¹| * (2 * meanErrorConstant 4 m K q *
      (((Real.sqrt 2 * 2 ^ (m + q + 2) * C * B) * (δ * τ)) *
        ((Real.sqrt 2 * 2 ^ (m + q + 2) * D * B) * (δ * τ)) / (s * τ))) =
      2 * meanErrorConstant 4 m K q * (Real.sqrt 2 * 2 ^ (m + q + 2) * B) ^ 2 * C * D * (τ / s) := by
    rw [abs_of_nonneg (by positivity)]
    field_simp
  rw [he] at hn
  apply hn.congr
  intro p hp
  dsimp only [normalizedMeanError, smul_eq_mul]
  ring

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma WeightedBound.real_mul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f g : E → ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2 ^ m * C * D) (fun x => f x * g x) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f U x‖ * ‖iteratedFDerivWithin ℝ (j - i) g U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_mul_le (n := j) (N := ∞) hf hg hU hx
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ ≤ 2 ^ j * C * D := weighted_binomial_bound hs hC hD j _ _
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun i hi => hbf i (hi.trans hj) x hx) (fun i hi => hbg i (hi.trans hj) x hx)
    _ ≤ _ := by gcongr; norm_num

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
