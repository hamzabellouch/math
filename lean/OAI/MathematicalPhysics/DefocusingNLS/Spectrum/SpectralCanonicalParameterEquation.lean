import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralDifferentiatedOutgoing
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHolomorphicSingularLimit

namespace OAI

/-! The canonical all-orders column inherits the differentiated equation from
the local weighted-resolvent construction, by outgoing uniqueness. -/

open Filter Topology
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem canonical_circular_parameter_equation (ν η b : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (L : ℝ) (hX : HasRadialExterior ν n b L) (hb : b ≠ 0)
    (c : ℂ × ℂ) (Y : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn ν η b n L c Y) (z : ℂ)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => deriv (fun lam => Y lam s) z)
      (circularLeadingField t (deriv (fun lam => Y lam t) z) +
        circularBoundedField (ν - 2 * z) (star ν - 2 * z) η n
          (radialExteriorCanonical ν n b L t).1 (deriv (fun lam => Y lam t) z) +
        circularPointSlopeCLM ν (star ν) z (Y z t)) t := by
  obtain ⟨q, hq, hP⟩ := canonical_circular_expansion_data ν b n L hX hb
  let C := circularFieldBound (ν - 2 * z) (star ν - 2 * z) η n ‖q‖
  have hC : 0 ≤ C := circularFieldBound_nonneg _ _ _ _ _
  obtain ⟨N, hN⟩ := exists_nat_gt (C + 1)
  obtain ⟨j, hNj, e, he⟩ := hP N
  have hNj' : (N : ℝ) ≤ j := by exact_mod_cast hNj
  have hj : 0 < j := by
    have hj' : (0 : ℝ) < j := by linarith
    exact_mod_cast hj'
  have hgap : C < 2 * (j : ℝ) := by linarith
  obtain ⟨W, _hWa, hWd, _hWlim, hWe, hWp⟩ := exists_differentiated_circular_outgoing
    ν (star ν) η n hn (radialExteriorExpansion ν n b j) c j hj q e he
  have hcont : Continuous (fun lam : ℂ =>
      circularFieldBound (ν - 2 * lam) (star ν - 2 * lam) η n ‖q‖) := by
    unfold circularFieldBound
    fun_prop
  have hnear : ∀ᶠ lam in 𝓝 z,
      circularFieldBound (ν - 2 * lam) (star ν - 2 * lam) η n ‖q‖ < 2 * (j : ℝ) :=
    hcont.continuousAt.eventually (gt_mem_nhds hgap)
  have hsame (s : ℝ) (hs : 0 ≤ s) :
      (fun lam => Y lam s) =ᶠ[𝓝 z] (fun lam => W lam s) := by
    filter_upwards [hnear] with lam hlam
    obtain ⟨k, hjk, w, hw⟩ := hY.2.2.2 lam j
    obtain ⟨v, hv⟩ := hWe lam
    have heq := circular_outgoing_orders_unique ν (ν - 2 * lam) (star ν - 2 * lam)
      η b n hn c j k hjk v w ‖q‖ 0 q (W lam) (Y lam)
      (fun r _ => q.norm_coe_le_norm r) (hWd lam hlam)
      (fun r hr => by simpa only [hq r hr] using hY.1 lam r hr)
      (fun r _ => hv r) hw hlam
    exact (heq s (by simpa only [max_self] using hs)).symm
  have hderiv (s : ℝ) (hs : 0 ≤ s) :
      deriv (fun lam => Y lam s) z = deriv (fun lam => W lam s) z :=
    (hsame s hs).deriv_eq
  have htime : (fun s => deriv (fun lam => Y lam s) z) =ᶠ[𝓝 t]
      (fun s => deriv (fun lam => W lam s) z) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact hderiv s hs.le
  have hd := (hWp z hgap t ht.le).congr_of_eventuallyEq htime
  apply hd.congr_deriv
  rw [hderiv t ht.le, (hsame t ht.le).eq_of_nhds, ← hq t ht.le]

end DefocusingNLS

end OAI
