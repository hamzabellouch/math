import OAI.Geometry.NodalSets.Charts.SimplicityEnergyDensity
import OAI.Geometry.NodalSets.Elliptic.CompactWeightedDivergenceIntegral

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff
noncomputable section

def roundSimplicityEnergy (u v zeta : Yau.Jets.Coord → ℝ) (lam : ℝ) : ℝ :=
  ∫ x, roundCoordDensity x * (zeta x*u x^2*Yau.pairing v (roundCoordGradient v) x -
    lam*simplicityDensityPerturbation roundCoordDensity u zeta (roundCoordGradient u) lam x*v x^2)

lemma round_simplicity_square_integrable (u v zeta : Yau.Jets.Coord → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hz : ContDiff ℝ ∞ zeta)
    (hc : HasCompactSupport zeta) :
    Integrable (fun x ↦ roundCoordDensity x*zeta x*roundSimplicitySquare u v x) := by
  have hs := ((roundCoordDensity_smooth.mul hz).mul (roundSimplicitySquare_smooth u v hu hv)).continuous
  have hcomp : HasCompactSupport (fun x ↦ roundCoordDensity x*zeta x) := hc.mul_left
  exact hs.integrable_of_hasCompactSupport hcomp.mul_right

theorem round_simplicity_energy_identity (u v zeta : Yau.Jets.Coord → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hz : ContDiff ℝ ∞ zeta)
    (hc : HasCompactSupport zeta) (lam : ℝ) (hlam : lam ≠ 0) :
    Integrable (fun x ↦ roundCoordDensity x * (zeta x*u x^2*Yau.pairing v (roundCoordGradient v) x -
      lam*simplicityDensityPerturbation roundCoordDensity u zeta (roundCoordGradient u) lam x*v x^2)) ∧
    roundSimplicityEnergy u v zeta lam =
      ∫ x, roundCoordDensity x*zeta x*roundSimplicitySquare u v x := by
  let V : Yau.Jets.Coord → Yau.Jets.Coord :=
    fun y i ↦ (u y*v y^2)*(zeta y*roundCoordGradient u y i)
  have hV (i : Fin 4) : ContDiff ℝ ∞ (fun x ↦ V x i) :=
    (hu.mul (hv.pow 2)).mul (hz.mul ((contDiff_pi.mp (roundCoordGradient_smooth u hu)) i))
  have hVc (i : Fin 4) : HasCompactSupport (fun x ↦ V x i) := by
    have h : HasCompactSupport (fun x ↦ zeta x*roundCoordGradient u x i) := hc.mul_right
    exact h.mul_left
  obtain ⟨hiD,hD⟩ := Yau.integral_weightedDiv_compact_zero roundCoordDensity
    roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne') V hV hVc
  have hiS := round_simplicity_square_integrable u v zeta hu hv hz hc
  have he : (fun x ↦ roundCoordDensity x * (zeta x*u x^2*Yau.pairing v (roundCoordGradient v) x -
      lam*simplicityDensityPerturbation roundCoordDensity u zeta (roundCoordGradient u) lam x*v x^2)) =
      (fun x ↦ roundCoordDensity x*zeta x*roundSimplicitySquare u v x +
        roundCoordDensity x*Yau.weightedDiv roundCoordDensity V x) := by
    funext x
    rw [round_simplicity_energy_density u v zeta hu hv hz lam hlam x]
    change _ = _ + roundCoordDensity x*Yau.weightedDiv roundCoordDensity
      (fun y i ↦ (u y*v y^2)*(zeta y*roundCoordGradient u y i)) x
    ring
  constructor
  · rw [he]
    exact hiS.add hiD
  · unfold roundSimplicityEnergy
    rw [he,integral_add hiS hiD,hD,add_zero]

lemma round_simplicity_energy_nonneg (u v zeta : Yau.Jets.Coord → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hz : ContDiff ℝ ∞ zeta)
    (hc : HasCompactSupport zeta) (hzn : ∀ x, 0 ≤ zeta x) (lam : ℝ) (hlam : lam ≠ 0) :
    0 ≤ roundSimplicityEnergy u v zeta lam := by
  rw [(round_simplicity_energy_identity u v zeta hu hv hz hc lam hlam).2]
  exact integral_nonneg (fun x ↦ mul_nonneg (mul_nonneg (roundCoordDensity_pos x).le (hzn x))
    (roundSimplicitySquare_nonneg u v x))

theorem round_simplicity_zero_energy_jet (u v zeta : Yau.Jets.Coord → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hz : ContDiff ℝ ∞ zeta)
    (hc : HasCompactSupport zeta) (hzn : ∀ x, 0 ≤ zeta x) (lam : ℝ) (hlam : lam ≠ 0)
    (he : roundSimplicityEnergy u v zeta lam = 0) :
    ∀ x, 0 < zeta x → ∀ i : Fin 4,
      u x*Yau.coordPartial v x i = v x*Yau.coordPartial u x i := by
  have hi := round_simplicity_square_integrable u v zeta hu hv hz hc
  have hs := ((roundCoordDensity_smooth.mul hz).mul (roundSimplicitySquare_smooth u v hu hv)).continuous
  have hn (x) : 0 ≤ roundCoordDensity x*zeta x*roundSimplicitySquare u v x :=
    mul_nonneg (mul_nonneg (roundCoordDensity_pos x).le (hzn x)) (roundSimplicitySquare_nonneg u v x)
  have hint : (∫ x, roundCoordDensity x*zeta x*roundSimplicitySquare u v x) = 0 :=
    (round_simplicity_energy_identity u v zeta hu hv hz hc lam hlam).2.symm.trans he
  have hzall (x) : roundCoordDensity x*zeta x*roundSimplicitySquare u v x = 0 := by
    by_contra hx
    have hp := integral_pos_of_integrable_nonneg_nonzero hs hi hn hx
    linarith only [hint,hp]
  intro x hx i
  have hsq : roundSimplicitySquare u v x = 0 :=
    (mul_eq_zero.mp (hzall x)).resolve_left (mul_pos (roundCoordDensity_pos x) hx).ne'
  have hfac : 0 < roundCoordFactor x := lt_of_lt_of_le zero_lt_one (roundCoordFactor_ge_one x)
  have hsum : ∑ i : Fin 4, (u x*Yau.coordPartial v x i-v x*Yau.coordPartial u x i)^2 = 0 :=
    (mul_eq_zero.mp hsq).resolve_left hfac.ne'
  have hle := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦
    sq_nonneg (u x*Yau.coordPartial v x j-v x*Yau.coordPartial u x j)) (Finset.mem_univ i)
  rw [hsum] at hle
  have hzsq := le_antisymm hle (sq_nonneg (u x*Yau.coordPartial v x i-v x*Yau.coordPartial u x i))
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hzsq)

end
end Yau.Target

end OAI
