import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSequenceExtension
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingCanonicalSelection

namespace OAI

/-! Extend prescribed canonical columns along an increasing power sequence. -/

open Filter
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialCanonicalExtension (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall) (ell : ℕ) (c : ℂ × ℂ)
    (Y : ℕ → ℂ → ℝ → E₄)
    (hY : ∀ i, IsCanonicalHolomorphicColumn (radialShootingNu (s i) (z i))
      ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z i)) (s i)
      (Real.log innerBoundaryRadius) c (Y i)) :
    let ze := radialIndexedExtension s z (fun _ => z₀)
    ∃ Ye : ℕ → ℂ → ℝ → E₄, (∀ i, Ye (s i)=Y i) ∧
      ∀ᶠ n in atTop, IsCanonicalHolomorphicColumn (radialShootingNu n (ze n))
        ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (ze n)) n
        (Real.log innerBoundaryRadius) c (Ye n) := by
  classical
  let ze := radialIndexedExtension s z (fun _ => z₀)
  obtain ⟨W,hW⟩ := radialShooting_exists_canonical_column ze ell c
  let Ye := radialIndexedExtension s Y W
  refine ⟨Ye,fun i => radialIndexedExtension_apply s hs Y W i,?_⟩
  filter_upwards [hW] with n hWn
  by_cases he : ∃ i, s i=n
  · obtain ⟨i,rfl⟩ := he
    simpa only [Ye,ze,radialIndexedExtension_apply s hs] using hY i
  · simpa only [Ye,ze,radialIndexedExtension,dite_eq_right he] using hWn

end DefocusingNLS

end OAI
