import OAI.Geometry.SurfaceImmersion.Geometry.ModulatedJets

namespace OAI

/-! Slow-scale bounds on the amplitudes of fast oscillatory jets. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates

lemma weighted_complexify {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → ℝ} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p : ℂ)) := by
  have hh := hb.linear hU hs hf Complex.ofRealCLM
  have hn : ‖Complex.ofRealCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
    hh.mono_const (mul_le_of_le_one_left hC hn)

lemma weighted_amplitudeDerivative {U : Set Base} (hU : IsOpen U)
    {φ : Base → ℝ} {Z : Base → ℂ} {τ s C P : ℝ} {m : ℕ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z)
    (hb : WeightedBound U s (m + 1) C Z) (v : Base) (hv : ‖v‖ ≤ 1)
    (hp : WeightedBound U s m P (fun p => fderiv ℝ φ p v)) :
    WeightedBound U s m ((1 + 2 ^ m * P) * C / τ) (amplitudeDerivative τ φ v Z) := by
  have hd := (hb.directional hU hs hZ.contDiffOn v).mono_const
    (mul_le_of_le_one_left (div_nonneg hC hs.le) hv)
  have hd' := hd.mono_const (div_le_div_of_nonneg_left hC hτ hτs)
  have hds : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const (c := v))
  have hc := weighted_complexify hU.uniqueDiffOn hs.le hP hds.contDiffOn hp
  have hcs := Complex.ofRealCLM.contDiff.comp hds
  have hc' := hc.const_mul hU.uniqueDiffOn hcs.contDiffOn (Complex.I / (τ : ℂ))
  have hn : ‖Complex.I / (τ : ℂ)‖ = 1 / τ := by
    simp [Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hτ.le]
  rw [hn] at hc'
  have hcm := (contDiff_const (c := Complex.I / (τ : ℂ))).mul hcs
  have hz := hc'.mul hU.uniqueDiffOn hs.le (by positivity) hC hcm.contDiffOn hZ.contDiffOn
    (hb.mono_order (Nat.le_succ m))
  have ha := hd'.add hU.uniqueDiffOn hs.le
    ((hZ.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const (c := v))).contDiffOn
    (hcm.mul hZ).contDiffOn hz
  convert ha using 1 <;> first | rfl | ring

def jetConstant (P : ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | m, r + 1 => (1 + 2 ^ m * P) * jetConstant P (m + 1) r

lemma jetConstant_nonneg {P : ℝ} (hP : 0 ≤ P) (m r : ℕ) : 0 ≤ jetConstant P m r := by
  induction r generalizing m with
  | zero => exact zero_le_one
  | succ r ih => exact mul_nonneg (by positivity) (ih (m + 1))

/-- Output derivatives remain at the slow scale. Only the length of the jet
word contributes short-scale powers. -/
theorem weighted_amplitudeJet {U : Set Base} (hU : IsOpen U)
    {φ : Base → ℝ} {Z : Base → ℂ} {τ s C P : ℝ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z) (w : List Base)
    (hw : ∀ v ∈ w, ‖v‖ ≤ 1) (m : ℕ)
    (hb : WeightedBound U s (m + w.length) C Z)
    (hp : ∀ v ∈ w, WeightedBound U s (m + w.length) P (fun p => fderiv ℝ φ p v)) :
    WeightedBound U s m (jetConstant P m w.length * C / τ ^ w.length)
      (amplitudeJet τ φ w Z) := by
  induction w generalizing m with
  | nil => simpa only [amplitudeJet, List.length_nil, Nat.add_zero, jetConstant, one_mul, pow_zero, div_one] using hb
  | cons v w ih =>
    have hlen : m + (v :: w).length = (m + 1) + w.length := by simp; omega
    have hb' := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx)) (m + 1)
      (hlen ▸ hb) (fun x hx => hlen ▸ hp x (List.mem_cons_of_mem _ hx))
    have hd := weighted_amplitudeDerivative hU hτ hs hτs
      (div_nonneg (mul_nonneg (jetConstant_nonneg hP _ _) hC) (pow_nonneg hτ.le _)) hP
      hφ (amplitudeJet_smooth hφ hZ τ w) hb' v (hw v (List.mem_cons_self ..))
      ((hp v (List.mem_cons_self ..)).mono_order (by simp))
    convert hd using 1
    · simp only [List.length_cons, jetConstant, pow_succ]
      ring
    · rfl

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
