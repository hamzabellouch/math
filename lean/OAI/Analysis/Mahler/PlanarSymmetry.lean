import OAI.Analysis.Mahler.PlanarDensity
import Mathlib.Analysis.Calculus.Deriv.Star

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology

lemma inverseF_deriv_conj {u : ℂ} (hu : u ∈ MahlerConformal.Omega) :
    deriv MahlerConformal.inverseF (starRingEnd ℂ u) =
      starRingEnd ℂ (deriv MahlerConformal.inverseF u) := by
  have h := ((MahlerConformal.hasDerivAt_inverseF hu).differentiableAt.hasDerivAt).conj_conj
  have hd : HasDerivAt MahlerConformal.inverseF
      (starRingEnd ℂ (deriv MahlerConformal.inverseF u)) (starRingEnd ℂ u) := by
    apply h.congr_of_eventuallyEq
    filter_upwards [MahlerConformal.isOpen_Omega.mem_nhds (MahlerConformal.Omega_conj hu)] with v hv
    change MahlerConformal.inverseF v = starRingEnd ℂ (MahlerConformal.inverseF (starRingEnd ℂ v))
    rw [MahlerConformal.inverseF_conj hv]
    simp
  exact hd.deriv

lemma planarDensity_conj (m : ℕ) {u : ℂ} (hu : u ∈ MahlerConformal.Omega) :
    planarDensity m (starRingEnd ℂ u) = planarDensity m u := by
  unfold planarDensity
  rw [MahlerConformal.inverseF_conj hu, inverseF_deriv_conj hu]
  simp

/-- Conjugation changes the sign of the original vertical primitive. -/
theorem planarPrimitive_neg (m : ℕ) {q t : ℝ}
    (hseg : ∀ s ∈ uIcc (0 : ℝ) t, (q : ℂ)+(s : ℂ)*Complex.I ∈ MahlerConformal.Omega) :
    planarPrimitive m q (-t) = -planarPrimitive m q t := by
  have heq : (∫ s in (0 : ℝ)..t, planarDensity m ((q : ℂ)+((-s : ℝ) : ℂ)*Complex.I)) =
      planarPrimitive m q t := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hc : (q : ℂ)+((-s : ℝ) : ℂ)*Complex.I =
        starRingEnd ℂ ((q : ℂ)+(s : ℂ)*Complex.I) := by simp
    dsimp only
    rw [hc]
    exact planarDensity_conj m (hseg s hs)
  have hchange : (∫ s in (0 : ℝ)..t, planarDensity m ((q : ℂ)+((-s : ℝ) : ℂ)*Complex.I)) =
      -planarPrimitive m q (-t) := by
    change (∫ s in (0 : ℝ)..t, (fun x : ℝ => planarDensity m ((q : ℂ)+(x : ℂ)*Complex.I)) (-s)) = _
    have hc := intervalIntegral.integral_comp_neg
      (f := fun x : ℝ => planarDensity m ((q : ℂ)+(x : ℂ)*Complex.I)) (a := 0) (b := t)
    calc
      _ = ∫ s in (-t)..(0 : ℝ), planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I) := by
        simpa only [neg_zero] using hc
      _ = _ := intervalIntegral.integral_symm 0 (-t)
  linarith

end SymmetricMahler

end OAI
