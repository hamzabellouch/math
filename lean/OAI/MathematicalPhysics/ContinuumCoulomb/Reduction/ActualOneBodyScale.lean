import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedMatrixDecayBound
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteOneBodyCorrection
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OneBodyScaleBudget

namespace OAI

/-! Actual corrected nuclear entries at the physical amplification. The
Gram error uses the decaying shifted matrix, not a uniform operator bound. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem correctedNuclearOneBodyMatrix_physical_scale
    {rho H S freq D R a E : ℝ} (hrho : 0 ≤ rho) (hH : 0 < H)
    (hS : 0 < S) (hf : 0 < freq) (hD : 0 ≤ D) (hR : 2 ≤ R)
    (ha : 0 < a) (hE : 0 ≤ E) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2)
    (h19 : Real.exp (-(19/10:ℝ)*D) ≤ 1/R^40)
    (h9 : Real.exp (-(9/10:ℝ)*D) ≤ 1/R^22)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/(a*R^30) ∧
      localizedCounterterm freq u i/(a*R^30) ≤ localizedCountertermBound freq*m/(a*R^30))
    (hbox : ∀ j, (∫ x, finiteBoxOrbitalResidual rho H S freq (a*R^30) u j x^2) ≤ (1/R^32)^2)
    (F : Position → ℝ)
    (hI : ∀ i j, Integrable (fun x => F x*continuumLocalizedMode freq (u i) x*
      continuumLocalizedMode freq (u j) x))
    (hF : ∀ i j, |∫ x, F x*continuumLocalizedMode freq (u i) x*
      continuumLocalizedMode freq (u j) x| ≤ E*((m:ℝ)+1)/R^32) (i j : Fin m) :
    |(a*R^30)*correctedNuclearOneBodyMatrix rho H S freq (a*R^30) u F i j-
        localizedOneBodyTarget (a*R^30) freq u i j| ≤
      (4*a+8*a*E+8*a*PlanarSobolev.wellBound*planarOverlapConstant^2+
        8*a*planarOverlapConstant*planarWellMatrixConstant+
        8*localizedCountertermBound freq*planarOverlapConstant*planarWellMatrixConstant+
        a*planarWellMatrixConstant+localizedCountertermBound freq*planarWellMatrixConstant+
        localizedCountertermBound freq*PlanarSobolev.wellBound*planarOverlapConstant)*
      ((m:ℝ)+1)^5/R^2 := by
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hscale : 0 < a*R^30 := by positivity
  have hd := localizedCountertermBound_nonnegative freq
  have hP := planarWellMatrixConstant_nonnegative
  have hO := planarOverlapConstant_nonnegative
  have hW := PlanarSobolev.wellBound_nonnegative
  let δ := localizedCountertermBound freq*(m:ℝ)/(a*R^30)
  let B := (PlanarSobolev.wellBound*planarOverlapConstant+(m:ℝ)*planarWellMatrixConstant)/R^22+
    (m:ℝ)*δ*planarWellMatrixConstant
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (p q : Fin m) : |localizedCorrectedOneBodyMatrix freq (a*R^30) u p q| ≤ B := by
    apply (localizedCorrectedOneBodyMatrix_decay hf hD hδ (a*R^30) u hsep hcoeff p q).trans
    dsimp only [B]
    have h := mul_le_mul_of_nonneg_left h9
      (show 0 ≤ PlanarSobolev.wellBound*planarOverlapConstant+(m:ℝ)*planarWellMatrixConstant by positivity)
    exact add_le_add (by simpa only [mul_one_div] using h) le_rfl
  have hg : localizedOverlapBound D ≤ planarOverlapConstant/R^22 := by
    unfold localizedOverlapBound
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left h9 hO
  have he := correctedNuclearOneBodyMatrix_error hrho hH hS hf (ne_of_gt hscale) u hδ hcoeff
    hsep hs (show 0 ≤ 1/R^32 by positivity) hbox hB hb F hI hF i j
  apply he.trans
  apply le_trans _ (one_body_scale_bound hR1 ha hd hE hP hO hW (Nat.cast_nonneg m))
  dsimp only [B,δ]
  rw [abs_of_pos hscale]
  have hgm : (m:ℝ)^2*(4*(2*m*localizedOverlapBound D)*B) ≤
      (m:ℝ)^2*(4*(2*m*(planarOverlapConstant/R^22))*B) := by gcongr
  have hn := add_le_add (add_le_add
    (show 4*(m:ℝ)^2*(1/R^32) ≤ 4*(m:ℝ)^2/R^32 by exact le_of_eq (by ring)) hgm)
    (le_refl (4*(m:ℝ)^2*(E*((m:ℝ)+1)/R^32)))
  have ht := mul_le_mul_of_nonneg_left hn hscale.le
  have he19 := mul_le_mul_of_nonneg_left h19
    (show 0 ≤ a*R^30*m*planarWellMatrixConstant+(m:ℝ)^2*localizedCountertermBound freq*planarWellMatrixConstant by positivity)
  have he9 := mul_le_mul_of_nonneg_left h9
    (show 0 ≤ (m:ℝ)^2*localizedCountertermBound freq*(PlanarSobolev.wellBound*planarOverlapConstant) by positivity)
  have he19' : (a*R^30*m*planarWellMatrixConstant+(m:ℝ)^2*localizedCountertermBound freq*planarWellMatrixConstant)*
      Real.exp (-(19/10:ℝ)*D) ≤
      (a*R^30*m*planarWellMatrixConstant+(m:ℝ)^2*localizedCountertermBound freq*planarWellMatrixConstant)/R^40 := by
    simpa only [mul_one_div] using he19
  have he9' : ((m:ℝ)^2*localizedCountertermBound freq*(PlanarSobolev.wellBound*planarOverlapConstant))*
      Real.exp (-(9/10:ℝ)*D) ≤
      ((m:ℝ)^2*localizedCountertermBound freq*(PlanarSobolev.wellBound*planarOverlapConstant))/R^22 := by
    simpa only [mul_one_div] using he9
  exact add_le_add (add_le_add ht he19') he9'

end ContinuumCoulomb

end

end OAI
