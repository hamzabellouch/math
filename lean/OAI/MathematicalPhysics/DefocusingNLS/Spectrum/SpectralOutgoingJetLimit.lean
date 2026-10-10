import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOutgoingPolynomialLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCorrectionLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorJetLimit

namespace OAI

/-! Uniform convergence of the complete finite-expansion plus correction
jets on the exterior half-line. -/

open Filter Topology Set Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem circularUnweight_uniform_limit (κ : ℝ) (hκ : 0 ≤ κ)
    (v : ℕ → CircularTailSpace) (w : CircularTailSpace) (hv : Tendsto v atTop (𝓝 w)) :
    TendstoUniformlyOn (fun n => circularUnweight κ (v n)) (circularUnweight κ w)
      atTop (Ici (0 : ℝ)) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_iff_norm_sub_tendsto_zero.mp hv).eventually (gt_mem_nhds hε)] with n hn t ht
  rw [dist_comm,dist_eq_norm]
  change ‖Real.exp (-κ*t) • circularTailEvaluation (v n) t-
    Real.exp (-κ*t) • circularTailEvaluation w t‖ < ε
  have he : Real.exp (-κ*t) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have ht0 : 0 ≤ t := ht
    nlinarith)
  have hd : circularTailEvaluation (v n) t-circularTailEvaluation w t=
      circularTailEvaluation (v n-w) t := rfl
  rw [← smul_sub,hd,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact ((mul_le_mul_of_nonneg_left (circularTailEvaluation_norm (v n-w) t)
    (Real.exp_nonneg _)).trans (mul_le_of_le_one_left (norm_nonneg _) he)).trans_lt hn

theorem circularPolynomialJet_uniform_limit (U : ℕ → ℂ[X] × ℂ[X]) (V : ℂ[X] × ℂ[X]) (d : ℕ)
    (hdeg : ∀ n, (U n).1.natDegree ≤ d ∧ (U n).2.natDegree ≤ d)
    (hV : V.1.natDegree ≤ d ∧ V.2.natDegree ≤ d)
    (hU : ∀ k, Tendsto (fun n => (U n).1.coeff k) atTop (𝓝 (V.1.coeff k)) ∧
      Tendsto (fun n => (U n).2.coeff k) atTop (𝓝 (V.2.coeff k))) :
    TendstoUniformlyOn (fun n => circularPolynomialJet (U n)) (circularPolynomialJet V)
      atTop (Ici (0 : ℝ)) := by
  have hp := radialPolynomialJet_uniform_limit (fun n => (U n).1) V.1 d
    (Eventually.of_forall (fun n => (hdeg n).1)) hV.1 (fun k _ => (hU k).1)
  have hm := radialPolynomialJet_uniform_limit (fun n => (U n).2) V.2 d
    (Eventually.of_forall (fun n => (hdeg n).2)) hV.2 (fun k _ => (hU k).2)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hp) ε hε,
    (Metric.tendstoUniformlyOn_iff.mp hm) ε hε] with n hpn hmn t ht
  exact max_lt (hpn t ht) (hmn t ht)

theorem spectralOutgoing_corrected_jet_uniform_limit
    (νp νm : ℕ → ℂ) (νp₀ νm₀ η : ℂ)
    (hp : Tendsto νp atTop (𝓝 νp₀)) (hm : Tendsto νm atTop (𝓝 νm₀))
    (P : ℕ → ℂ[X]) (Q : ℂ[X]) (d : ℕ)
    (hdeg : ∀ᶠ n in atTop, (P n).natDegree ≤ d)
    (hP : ∀ k, k ≤ d → Tendsto (fun n => (P n).coeff k) atTop (𝓝 (Q.coeff k)))
    (hzero : ‖Q.coeff 0‖ < 1) (c : ℂ × ℂ) (j : ℕ)
    (κ : ℝ) (hκ : 0 ≤ κ) (v : ℕ → CircularTailSpace) (w : CircularTailSpace)
    (hv : Tendsto v atTop (𝓝 w)) :
    TendstoUniformlyOn
      (fun n t => circularPolynomialJet (spectralOutgoingPolynomial (νp n) (νm n) η n (P n) c j) t+
        circularUnweight κ (v n) t)
      (fun t => circularPolynomialJet (spectralOutgoingPolynomial νp₀ νm₀ η 1 0 c j) t+
        circularUnweight κ w t) atTop (Ici (0 : ℝ)) := by
  have hU := circularPolynomialJet_uniform_limit
    (fun n => spectralOutgoingPolynomial (νp n) (νm n) η n (P n) c j)
    (spectralOutgoingPolynomial νp₀ νm₀ η 1 0 c j) j
    (fun n => spectralOutgoingPolynomial_degree _ _ _ _ _ _ _)
    (spectralOutgoingPolynomial_degree _ _ _ _ _ _ _)
    (spectralOutgoingPolynomial_coefficient_limit νp νm νp₀ νm₀ η hp hm P Q d hdeg hP hzero c j)
  exact hU.add (circularUnweight_uniform_limit κ hκ v w hv)

end DefocusingNLS

end OAI
