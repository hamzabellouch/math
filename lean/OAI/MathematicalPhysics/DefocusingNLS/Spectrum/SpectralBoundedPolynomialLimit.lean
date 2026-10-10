import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralBoundedPolynomialAnalytic
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOutgoingPolynomialLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorJetLimit

namespace OAI

/-! Finite coefficient limits imply norm convergence of the bounded
polynomial jets used in the actual outgoing forcing. -/

open Filter Topology Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem boundedRadialPolynomial_tendsto (P : ℕ → ℂ[X]) (Q : ℂ[X]) (d : ℕ)
    (hdeg : ∀ n, (P n).natDegree ≤ d) (hQ : Q.natDegree ≤ d)
    (hP : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (Q.coeff k))) :
    Tendsto (fun n => boundedRadialPolynomial (P n)) atTop (𝓝 (boundedRadialPolynomial Q)) := by
  have he : (fun n => boundedRadialPolynomial (P n))=
      fun n => ∑ k ∈ Finset.range (d+1), (P n).coeff k • boundedRadialPolynomial (X^k) := by
    funext n
    exact boundedRadialPolynomial_finite (P n) d (hdeg n)
  rw [he,boundedRadialPolynomial_finite Q d hQ]
  exact tendsto_finsetSum _ (fun k _ => (hP k).smul_const _)

theorem boundedCircularPolynomialComponent_tendsto (P : ℕ → ℂ[X]) (Q : ℂ[X]) (d : ℕ)
    (hdeg : ∀ n, (P n).natDegree ≤ d) (hQ : Q.natDegree ≤ d)
    (hP : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (Q.coeff k))) :
    Tendsto (fun n => boundedCircularPolynomialComponent (P n)) atTop
      (𝓝 (boundedCircularPolynomialComponent Q)) := by
  have hp := boundedRadialPolynomial_tendsto P Q d hdeg hQ hP
  have he := boundedRadialPolynomial_tendsto
    (fun n => radialPolynomialEuler (P n)) (radialPolynomialEuler Q) d
    (fun n => radialPolynomialEuler_degree (P n) d (hdeg n))
    (radialPolynomialEuler_degree Q d hQ)
    (fun k => by simpa only [radialPolynomialEuler_coeff] using (hP k).const_mul (-2*(k : ℂ)))
  have hlim := (tendsto_iff_norm_sub_tendsto_zero.mp hp).max
    (tendsto_iff_norm_sub_tendsto_zero.mp he)
  simp only [max_self] at hlim
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
  intro n
  apply (BoundedContinuousFunction.norm_le (le_max_of_le_left (norm_nonneg _))).mpr
  intro t
  change max ‖boundedRadialPolynomial (P n) t-boundedRadialPolynomial Q t‖
    ‖boundedRadialPolynomial (radialPolynomialEuler (P n)) t-
      boundedRadialPolynomial (radialPolynomialEuler Q) t‖ ≤ _
  exact max_le_max
    ((boundedRadialPolynomial (P n)-boundedRadialPolynomial Q).norm_coe_le_norm t)
    ((boundedRadialPolynomial (radialPolynomialEuler (P n))-
      boundedRadialPolynomial (radialPolynomialEuler Q)).norm_coe_le_norm t)

theorem boundedCircularPolynomialJet_tendsto
    (U : ℕ → ℂ[X] × ℂ[X]) (V : ℂ[X] × ℂ[X]) (d : ℕ)
    (hdeg : ∀ n, (U n).1.natDegree ≤ d ∧ (U n).2.natDegree ≤ d)
    (hV : V.1.natDegree ≤ d ∧ V.2.natDegree ≤ d)
    (hU : ∀ k, Tendsto (fun n => (U n).1.coeff k) atTop (𝓝 (V.1.coeff k)) ∧
      Tendsto (fun n => (U n).2.coeff k) atTop (𝓝 (V.2.coeff k))) :
    Tendsto (fun n => boundedCircularPolynomialJet (U n)) atTop
      (𝓝 (boundedCircularPolynomialJet V)) := by
  exact (boundedCircularPolynomialComponent_tendsto (fun n => (U n).1) V.1 d
    (fun n => (hdeg n).1) hV.1 (fun k => (hU k).1)).prodMk_nhds
    (boundedCircularPolynomialComponent_tendsto (fun n => (U n).2) V.2 d
      (fun n => (hdeg n).2) hV.2 (fun k => (hU k).2))

theorem spectralOutgoing_bounded_jet_tendsto
    (νp νm : ℕ → ℂ) (νp₀ νm₀ η : ℂ)
    (hp : Tendsto νp atTop (𝓝 νp₀)) (hm : Tendsto νm atTop (𝓝 νm₀))
    (P : ℕ → ℂ[X]) (Q : ℂ[X]) (d : ℕ)
    (hdeg : ∀ᶠ n in atTop, (P n).natDegree ≤ d)
    (hP : ∀ k, k ≤ d → Tendsto (fun n => (P n).coeff k) atTop (𝓝 (Q.coeff k)))
    (hzero : ‖Q.coeff 0‖ < 1) (c : ℂ × ℂ) (j : ℕ) :
    Tendsto (fun n => boundedCircularPolynomialJet
      (spectralOutgoingPolynomial (νp n) (νm n) η n (P n) c j)) atTop
      (𝓝 (boundedCircularPolynomialJet (spectralOutgoingPolynomial νp₀ νm₀ η 1 0 c j))) := by
  exact boundedCircularPolynomialJet_tendsto _ _ j
    (fun _ => spectralOutgoingPolynomial_degree _ _ _ _ _ _ _)
    (spectralOutgoingPolynomial_degree _ _ _ _ _ _ _)
    (spectralOutgoingPolynomial_coefficient_limit νp νm νp₀ νm₀ η hp hm P Q d hdeg hP hzero c j)

end DefocusingNLS

end OAI
