import OAI.Geometry.NodalSets.Elliptic.CorrugationPeriodicBounds
import OAI.Geometry.NodalSets.Elliptic.CorrugationPeriodicFlatJets

namespace OAI

namespace Yau.Geometry
open Real Set Filter
open scoped Topology
noncomputable section

lemma nonzero_integer_shift_square_wide (x : ℝ) (hx : |x| ≤ 3/4)
    (k : ℤ) (hk : k ≠ 0) : (1/16:ℝ) ≤ (x-(k:ℝ))^2 := by
  have hx' := abs_le.mp hx
  rcases lt_or_gt_of_ne hk with hk | hk
  · have hk1 : k ≤ -1 := by omega
    have hkR : (k:ℝ) ≤ -1 := by exact_mod_cast hk1
    nlinarith
  · have hk1 : 1 ≤ k := by omega
    have hkR : 1 ≤ (k:ℝ) := by exact_mod_cast hk1
    nlinarith

lemma corrugationPeriodicWell_wide_cell (a : ℝ) (z : ℝ × ℝ)
    (hz₁ : |z.1| ≤ 3/4) (hz₂ : |z.2| ≤ 3/4) :
    corrugationPeriodicWell a z = corrugationDiskWell a (1/4) z := by
  unfold corrugationPeriodicWell
  rw [tsum_eq_single (0 : ℤ × ℤ)]
  · simp
  · intro k hk
    apply corrugationDiskWell_zero
    have h : k.1 ≠ 0 ∨ k.2 ≠ 0 := by
      by_contra h
      simp only [not_or,not_not] at h
      exact hk (Prod.ext h.1 h.2)
    rcases h with h | h
    · have hs := nonzero_integer_shift_square_wide z.1 hz₁ k.1 h
      dsimp only
      nlinarith [sq_nonneg (z.2-(k.2:ℝ))]
    · have hs := nonzero_integer_shift_square_wide z.2 hz₂ k.2 h
      dsimp only
      nlinarith [sq_nonneg (z.1-(k.1:ℝ))]

lemma corrugationPeriodicWell_closed_cell_eventually (a : ℝ) (z : ℝ × ℝ)
    (hz₁ : |z.1| ≤ 1/2) (hz₂ : |z.2| ≤ 1/2) :
    corrugationPeriodicWell a =ᶠ[𝓝 z] corrugationDiskWell a (1/4) := by
  have h1 : ∀ᶠ w : ℝ × ℝ in 𝓝 z, |w.1| < 3/4 :=
    continuous_fst.abs.continuousAt.eventually_lt_const (by linarith)
  have h2 : ∀ᶠ w : ℝ × ℝ in 𝓝 z, |w.2| < 3/4 :=
    continuous_snd.abs.continuousAt.eventually_lt_const (by linarith)
  filter_upwards [h1,h2] with w hw1 hw2
  exact corrugationPeriodicWell_wide_cell a w hw1.le hw2.le

lemma corrugationPeriodicWell_closed_cell_jets (a : ℝ) (z : ℝ × ℝ)
    (hz₁ : |z.1| ≤ 1/2) (hz₂ : |z.2| ≤ 1/2) :
    fderiv ℝ (corrugationPeriodicWell a) z = fderiv ℝ (corrugationDiskWell a (1/4)) z ∧
    fderiv ℝ (fderiv ℝ (corrugationPeriodicWell a)) z =
      fderiv ℝ (fderiv ℝ (corrugationDiskWell a (1/4))) z := by
  have h := corrugationPeriodicWell_closed_cell_eventually a z hz₁ hz₂
  exact ⟨h.fderiv_eq,h.fderiv.fderiv_eq⟩

lemma corrugationPeriodicWell_boundary_plateau (a : ℝ) (z : ℝ × ℝ)
    (hz₁ : |z.1| ≤ 1/2) (hz₂ : |z.2| ≤ 1/2)
    (hb : |z.1| = 1/2 ∨ |z.2| = 1/2) :
    corrugationPeriodicWell a =ᶠ[𝓝 z] 0 := by
  have hz : (1/4:ℝ)^2 < z.1^2+z.2^2 := by
    rcases hb with h | h
    · have he := sq_abs z.1
      rw [h] at he
      nlinarith [sq_nonneg z.2]
    · have he := sq_abs z.2
      rw [h] at he
      nlinarith [sq_nonneg z.1]
  have hnear : ∀ᶠ w : ℝ × ℝ in 𝓝 z, (1/4:ℝ)^2 < w.1^2+w.2^2 :=
    ((continuous_fst.pow 2).add (continuous_snd.pow 2)).continuousAt.eventually_const_lt hz
  filter_upwards [corrugationPeriodicWell_closed_cell_eventually a z hz₁ hz₂,hnear] with w hw hr
  exact hw.trans (corrugationDiskWell_zero hr.le)

lemma corrugationPeriodicWell_closed_derivative_bound {a : ℝ} (ha : 0 ≤ a)
    (m : ℤ × ℤ) (z : ℝ × ℝ) (hz₁ : |z.1| ≤ 1/2) (hz₂ : |z.2| ≤ 1/2)
    {r : ℝ} (hr : 0 ≤ r) (hz : r^2=z.1^2+z.2^2) :
    ‖fderiv ℝ (corrugationPeriodicWell a) (z.1+(m.1:ℝ),z.2+(m.2:ℝ))‖ ≤
      2*corrugationSlope a (1/4) r := by
  by_cases h1 : |z.1| < 1/2
  · by_cases h2 : |z.2| < 1/2
    · exact corrugationPeriodicWell_derivative_bound_nonneg ha m z h1 h2 hr hz
    · have hp := corrugationPeriodicWell_boundary_plateau a z hz₁ hz₂
        (Or.inr (le_antisymm hz₂ (le_of_not_gt h2)))
      rw [(corrugationPeriodicWell_shift_jets a m z).1,hp.fderiv_eq]
      simpa using mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) (corrugationSlope_nonneg ha hr)
  · have hp := corrugationPeriodicWell_boundary_plateau a z hz₁ hz₂
      (Or.inl (le_antisymm hz₁ (le_of_not_gt h1)))
    rw [(corrugationPeriodicWell_shift_jets a m z).1,hp.fderiv_eq]
    simpa using mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) (corrugationSlope_nonneg ha hr)

end
end Yau.Geometry

end OAI
