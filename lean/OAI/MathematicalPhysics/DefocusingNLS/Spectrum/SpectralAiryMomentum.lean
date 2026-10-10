import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarModulus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

/-! Nonzero flux forces the forbidden-side Airy momentum to become positive. -/

open Set
namespace DefocusingNLS

theorem spectralAiry_momentum_lower (q : ℂ × ℂ) (t : ℝ) (ht : 1≤t) :
    2*|spectralScalarFlux q|≤Complex.normSq q.2+t*spectralScalarMass q := by
  let Q := spectralScalarMass q
  let D := Complex.normSq q.2
  let P := spectralScalarMomentum q
  let J := spectralScalarFlux q
  have hQ : 0≤Q := Complex.normSq_nonneg _
  have hD : 0≤D := Complex.normSq_nonneg _
  have hrel : Q*D=P^2+J^2 := spectralScalarFlux_identity q
  have hsum : 2*|J|≤Q+D := by
    nlinarith [sq_nonneg (Q-D),sq_nonneg P,sq_abs J,abs_nonneg J]
  change 2*|J|≤D+t*Q
  nlinarith

theorem spectralAiry_eventually_positive_momentum
    (q : ℝ → ℂ × ℂ) (T : ℝ) (hT : 1≤T)
    (hq : ContinuousOn q (Ici T))
    (hD : ∀ t, T≤t → HasDerivAt q (spectralScalarField (-(t : ℂ)) (q t)) t)
    (hJ : spectralScalarFlux (q T)≠0) :
    ∃ S : ℝ, T≤S ∧ ∀ t, S≤t → 0<spectralScalarMomentum (q t) := by
  let P := fun t => spectralScalarMomentum (q t)
  let c := 2*|spectralScalarFlux (q T)|
  have hc : 0<c := mul_pos (by norm_num) (abs_pos.mpr hJ)
  have hflux (t : ℝ) (ht : T≤t) : spectralScalarFlux (q t)=spectralScalarFlux (q T) :=
    spectralScalarFlux_const T t q (fun x => -x)
      (hq.mono (fun _ hx => hx.1))
      (fun x hx => by simpa only [Complex.ofReal_neg] using hD x hx.1.le) t ⟨ht,le_rfl⟩
  have hPc : ContinuousOn P (Ici T) :=
    Complex.continuous_re.comp_continuousOn (hq.fst.star.mul hq.snd)
  have hPd (t : ℝ) (ht : T≤t) :
      HasDerivAt P (Complex.normSq (q t).2+t*spectralScalarMass (q t)) t := by
    simpa only [Complex.neg_re,Complex.ofReal_re,neg_mul,sub_neg_eq_add] using
      spectralScalarMomentum_hasDerivAt q (-(t : ℂ)) t (hD t ht)
  have hlower (x y : ℝ) (hx : T≤x) (hy : T≤y) (hxy : x≤y) :
      c*(y-x)≤P y-P x := by
    apply (convex_Ici T).mul_sub_le_image_sub_of_le_deriv hPc
      (fun t ht => (hPd t (le_of_lt (by simpa only [interior_Ici,mem_Ioi] using ht))).differentiableAt.differentiableWithinAt)
      _ x hx y hy hxy
    intro t ht
    have htt : T≤t := (by simpa only [interior_Ici,mem_Ioi] using ht : T<t).le
    rw [(hPd t htt).deriv]
    have hb := spectralAiry_momentum_lower (q t) t (hT.trans htt)
    rwa [hflux t htt] at hb
  let S := T+(|P T|+1)/c
  have hST : T≤S := by
    have hp : 0≤(|P T|+1)/c := by positivity
    dsimp only [S]
    linarith
  have he : c*(S-T)=|P T|+1 := by dsimp only [S]; field_simp; ring
  have hPS : 0<P S := by
    have hh := hlower T S le_rfl hST hST
    rw [he] at hh
    linarith [neg_abs_le (P T)]
  refine ⟨S,hST,?_⟩
  intro t ht
  have hb := hlower S t hST (hST.trans ht) ht
  have hnonneg := mul_nonneg hc.le (sub_nonneg.mpr ht)
  linarith

end DefocusingNLS

end OAI
