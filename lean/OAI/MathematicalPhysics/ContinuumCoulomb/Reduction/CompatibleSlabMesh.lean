import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabHighAspectRatio
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteBoxMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearMeshBalance

namespace OAI

/-! Compatible polynomial choices for the finite slab and nuclear mesh.
The horizontal radius may grow as the tenth power of the slab height. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem finiteBoxOrbitalResidual_tenthPower_bound {rho T freq : ℝ}
    (hrho : 0 ≤ rho) (hT : 2 ≤ T) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ)
    (j : Fin m) :
    (∫ x, finiteBoxOrbitalResidual rho (T^10) T freq scale u j x^2) ≤
      2*(slabResidualSeventySecondBound rho freq (u j)/T^14+
        ((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2/(T/2)^24*
          (∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2)) := by
  have hT0 : 0 < T := by linarith
  have hs := slabOrbitalResidual_square_integrable hrho (pow_nonneg hT0.le 10) hT0.le hfreq (u j)
  obtain ⟨hw,hwb⟩ := finiteWellOrbitalResidual_square_bound hfreq hT0 scale u hδ hcoeff j
  have h := integral_mono
    (finiteBoxOrbitalResidual_memLp hrho (pow_nonneg hT0.le 10) hT0 hfreq scale u hδ hcoeff j).integrable_sq
    ((hs.add hw).const_mul 2) (fun x => show
      finiteBoxOrbitalResidual rho (T^10) T freq scale u j x^2 ≤
        2*(slabOrbitalResidual rho (T^10) T freq (u j) x^2+
          finiteWellOrbitalResidual freq scale T u j x^2) from by
      dsimp [finiteBoxOrbitalResidual]
      nlinarith [sq_nonneg (slabOrbitalResidual rho (T^10) T freq (u j) x-
        finiteWellOrbitalResidual freq scale T u j x)])
  rw [integral_const_mul] at h
  simp only [Pi.add_apply] at h
  rw [integral_add hs hw] at h
  have hb := slabOrbitalResidual_tenthPower_bound hrho hT hfreq (u j)
  linarith

theorem nuclear_mesh_tenthPower_balance {R a b c q p rho : ℝ} (hR : 1 ≤ R)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hrho : 0 ≤ rho) :
    (8/rho)*R^30*((a*p*R^8+b*R^6+c*R^3)*(1/R^10)^4+q*(1/R^10)^2/R^12) ≤
      (8/rho)*(a*p+b+c+q)/R^2 := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have he : R^30*((a*p*R^8+b*R^6+c*R^3)*(1/R^10)^4+q*(1/R^10)^2/R^12) =
      a*p/R^2+b/R^4+c/R^7+q/R^2 := by
    field_simp [ne_of_gt hR0]
  have hb' := div_le_div_of_nonneg_left hb (pow_pos hR0 2)
    (pow_le_pow_right₀ hR (by decide : 2 ≤ 4))
  have hc' := div_le_div_of_nonneg_left hc (pow_pos hR0 2)
    (pow_le_pow_right₀ hR (by decide : 2 ≤ 7))
  have h : R^30*((a*p*R^8+b*R^6+c*R^3)*(1/R^10)^4+q*(1/R^10)^2/R^12) ≤
      (a*p+b+c+q)/R^2 := by
    rw [he]
    calc
      _ ≤ a*p/R^2+b/R^2+c/R^2+q/R^2 := by linarith
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ 8/rho by positivity)
  convert hh using 1 <;> ring

end ContinuumCoulomb

end

end OAI
