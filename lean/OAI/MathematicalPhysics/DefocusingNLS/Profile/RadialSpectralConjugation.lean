import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralMode

namespace OAI

/-! Conjugating and swapping the physical components reflects a radial mode
across the real spectral axis and preserves all regular outgoing conditions. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectral_iteratedDeriv_star (f : ℝ → ℂ) (N : ℕ) :
    iteratedDeriv N (fun r => star (f r))=fun r => star (iteratedDeriv N f r) := by
  induction N with
  | zero => rfl
  | succ N ih => rw [iteratedDeriv_succ,ih,deriv.star',iteratedDeriv_succ]

theorem harmonicRadialEigenpair_conjugate (a b : ℝ) (m : ℕ) (Q f g : ℝ → ℂ)
    (eta : ℝ) (lam : ℂ) (he : IsHarmonicRadialEigenpair a b m Q (eta : ℂ) lam f g) :
    IsHarmonicRadialEigenpair a b m Q (eta : ℂ) (star lam)
      (fun r => star (g r)) (fun r => star (f r)) := by
  intro r hr
  obtain ⟨h1,h2⟩ := he r hr
  have h1s := congrArg star h1
  have h2s := congrArg star h2
  have hI : star (Complex.I : ℂ) = -Complex.I := Complex.conj_I
  have hrstar (x : ℝ) : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
  simp only [star_add,star_sub,star_mul,star_neg,star_div₀,star_pow,star_natCast,
    star_star,hI,hrstar,neg_neg] at h1s h2s
  simp only [deriv.star',deriv.star,star_mul,star_pow,star_natCast,star_star]
  constructor
  · convert h2s using 1 <;> ring
  · convert h1s using 1 <;> ring

noncomputable def RadialSpectralMode.conjugate {a b : ℝ} {m N : ℕ} {Q : ℝ → ℂ}
    {eta : ℝ} {lam : ℂ} (u : RadialSpectralMode a b m N Q (eta : ℂ) lam) :
    RadialSpectralMode a b m N Q (eta : ℂ) (star lam) where
  first := fun r => star (u.second r)
  second := fun r => star (u.first r)
  first_c2 := (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp u.second_c2
  second_c2 := (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp u.first_c2
  equation := harmonicRadialEigenpair_conjugate a b m Q u.first u.second eta lam u.equation
  first_smooth := (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn u.second_smooth
  second_smooth := (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn u.first_smooth
  first_top := by simpa only [spectral_iteratedDeriv_star,norm_star] using u.second_top
  second_top := by simpa only [spectral_iteratedDeriv_star,norm_star] using u.first_top
  bounded := by
    obtain ⟨M,hM,hb⟩ := u.bounded
    refine ⟨M,hM,fun r => ?_⟩
    simpa only [Prod.norm_def,norm_star,max_comm] using hb r
  nonzero := by
    obtain ⟨r,hr,hn⟩ := u.nonzero
    exact ⟨r,hr,hn.elim (fun h => Or.inr (star_ne_zero.mpr h)) (fun h => Or.inl (star_ne_zero.mpr h))⟩

end DefocusingNLS

end OAI
