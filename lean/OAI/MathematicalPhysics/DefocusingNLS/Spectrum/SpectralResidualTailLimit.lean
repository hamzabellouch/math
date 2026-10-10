import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNormalizedResidualLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorBoundedFamily
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialTailData

namespace OAI

/-! The normalized residuals extend to a convergent family in the exact
bounded tail space used by the coupled correction inverse. -/

open Filter Topology Set Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def spectralBoundedResidualAfter (T : ℝ) (R : ℂ[X] × ℂ[X]) : CircularTailSpace :=
  (boundedRadialResidualAfter T R.1,boundedRadialResidualAfter T R.2)

theorem spectralBoundedResidualAfter_limit (T ε : ℝ) (hT : Real.exp (-2*T) ≤ ε)
    (R : ℕ → ℂ[X] × ℂ[X]) (R₀ : ℂ[X] × ℂ[X])
    (hp : TendstoUniformlyOn (fun n z => (R n).1.eval z) (fun z => R₀.1.eval z)
      atTop (Metric.closedBall (0 : ℂ) ε))
    (hm : TendstoUniformlyOn (fun n z => (R n).2.eval z) (fun z => R₀.2.eval z)
      atTop (Metric.closedBall (0 : ℂ) ε)) :
    Tendsto (fun n => spectralBoundedResidualAfter T (R n)) atTop
      (𝓝 (spectralBoundedResidualAfter T R₀)) := by
  exact (boundedRadialResidualAfter_limit T ε hT (fun n => (R n).1) R₀.1 hp).prodMk_nhds
    (boundedRadialResidualAfter_limit T ε hT (fun n => (R n).2) R₀.2 hm)

theorem spectralBoundedResidualAfter_factor (T : ℝ) (νp νm η : ℂ) (m : ℕ)
    (P : ℂ[X]) (U R : ℂ[X] × ℂ[X]) (j : ℕ)
    (hp : (spectralPolynomialResidualPair νp νm η m P U).1=X^j*R.1)
    (hm : (spectralPolynomialResidualPair νp νm η m P U).2=X^j*R.2)
    (t : ℝ) (ht : T ≤ t) :
    Real.exp (-(2*(j : ℝ))*t) •
      circularTailEvaluation (spectralBoundedResidualAfter T R) t=
        -circularPolynomialResidualJet νp νm η m P U t := by
  have h₁ := boundedRadialResidualAfter_factor T _ R.1 j hp t ht
  have h₂ := boundedRadialResidualAfter_factor T _ R.2 j hm t ht
  apply Prod.ext
  · simpa only [spectralBoundedResidualAfter,circularTailEvaluation,
      circularPolynomialResidualJet,Prod.smul_fst,Prod.fst_neg,Prod.neg_mk,neg_zero] using h₁
  · simpa only [spectralBoundedResidualAfter,circularTailEvaluation,
      circularPolynomialResidualJet,Prod.smul_snd,Prod.snd_neg,Prod.neg_mk,neg_zero] using h₂

theorem exists_spectralOutgoing_residual_tail_limit
    (νp νm : ℕ → ℂ) (νp₀ νm₀ η : ℂ)
    (hp : Tendsto νp atTop (𝓝 νp₀)) (hm : Tendsto νm atTop (𝓝 νm₀))
    (P : ℕ → ℂ[X]) (Q : ℂ[X]) (d : ℕ)
    (hdeg : ∀ᶠ n in atTop, (P n).natDegree ≤ d)
    (hP : ∀ k, k ≤ d → Tendsto (fun n => (P n).coeff k) atTop (𝓝 (Q.coeff k)))
    (hzero : ‖Q.coeff 0‖ < 1) (c : ℂ × ℂ) (j : ℕ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∃ r : ℕ → CircularTailSpace, ∃ r₀ : CircularTailSpace,
      Tendsto r atTop (𝓝 r₀) ∧
      (∀ n t, T ≤ t → Real.exp (-(2*(j : ℝ))*t) • circularTailEvaluation (r n) t=
        -circularPolynomialResidualJet (νp n) (νm n) η n (P n)
          (spectralOutgoingPolynomial (νp n) (νm n) η n (P n) c j) t) ∧
      ∀ t, T ≤ t → Real.exp (-(2*(j : ℝ))*t) • circularTailEvaluation r₀ t=
        -circularPolynomialResidualJet νp₀ νm₀ η 1 0
          (spectralOutgoingPolynomial νp₀ νm₀ η 1 0 c j) t := by
  obtain ⟨ε,hε,_hε1,R,R₀,hR,hR₀p,hR₀m,hRp,hRm⟩ :=
    spectralOutgoing_normalized_residual_limit νp νm νp₀ νm₀ η hp hm P Q d hdeg hP hzero c j
  have he : Tendsto (fun t : ℝ => Real.exp (-2*t)) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ)<2)) using 1
    funext t
    simp [neg_mul]
  obtain ⟨T,hT,hTe⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (he.eventually (gt_mem_nhds hε))).exists
  refine ⟨T,hT,(fun n => spectralBoundedResidualAfter T (R n)),
    spectralBoundedResidualAfter T R₀,
    spectralBoundedResidualAfter_limit T ε hTe.le R R₀ hRp hRm,?_,?_⟩
  · intro n t ht
    exact spectralBoundedResidualAfter_factor T (νp n) (νm n) η n (P n) _ (R n) j
      (hR n).1 (hR n).2 t ht
  · intro t ht
    exact spectralBoundedResidualAfter_factor T νp₀ νm₀ η 1 0 _ R₀ j hR₀p hR₀m t ht

end DefocusingNLS

end OAI
