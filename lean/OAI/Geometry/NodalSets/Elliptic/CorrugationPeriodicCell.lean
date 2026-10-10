import OAI.Geometry.NodalSets.Elliptic.CorrugationPeriodicWell

namespace OAI

namespace Yau.Geometry
open Real Set Filter
open scoped ContDiff Topology
noncomputable section

lemma nonzero_integer_shift_square (x : ℝ) (hx : |x| ≤ 1/2) (k : ℤ) (hk : k ≠ 0) :
    (1/4:ℝ) ≤ (x-(k:ℝ))^2 := by
  have hx' := abs_le.mp hx
  rcases lt_or_gt_of_ne hk with hk | hk
  · have hk1 : k ≤ -1 := by omega
    have hkR : (k:ℝ) ≤ -1 := by exact_mod_cast hk1
    nlinarith
  · have hk1 : 1 ≤ k := by omega
    have hkR : 1 ≤ (k:ℝ) := by exact_mod_cast hk1
    nlinarith

lemma corrugationPeriodicWell_cell (a : ℝ) (z : ℝ × ℝ)
    (hz₁ : |z.1| ≤ 1/2) (hz₂ : |z.2| ≤ 1/2) :
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
    · have hs := nonzero_integer_shift_square z.1 hz₁ k.1 h
      dsimp only
      nlinarith [sq_nonneg (z.2-(k.2:ℝ))]
    · have hs := nonzero_integer_shift_square z.2 hz₂ k.2 h
      dsimp only
      nlinarith [sq_nonneg (z.1-(k.1:ℝ))]

lemma corrugationPeriodicWell_cell_eventually (a : ℝ) (z : ℝ × ℝ)
    (hz₁ : |z.1| < 1/2) (hz₂ : |z.2| < 1/2) :
    corrugationPeriodicWell a =ᶠ[𝓝 z] corrugationDiskWell a (1/4) := by
  have h1 : ∀ᶠ w : ℝ × ℝ in 𝓝 z, |w.1| < 1/2 :=
    continuous_fst.abs.continuousAt.eventually_lt_const hz₁
  have h2 : ∀ᶠ w : ℝ × ℝ in 𝓝 z, |w.2| < 1/2 :=
    continuous_snd.abs.continuousAt.eventually_lt_const hz₂
  filter_upwards [h1,h2] with w hw1 hw2
  exact corrugationPeriodicWell_cell a w hw1.le hw2.le

lemma corrugationPeriodicWell_cell_jets (a : ℝ) (z : ℝ × ℝ)
    (hz₁ : |z.1| < 1/2) (hz₂ : |z.2| < 1/2) :
    fderiv ℝ (corrugationPeriodicWell a) z = fderiv ℝ (corrugationDiskWell a (1/4)) z ∧
    fderiv ℝ (fderiv ℝ (corrugationPeriodicWell a)) z =
      fderiv ℝ (fderiv ℝ (corrugationDiskWell a (1/4))) z := by
  have h := corrugationPeriodicWell_cell_eventually a z hz₁ hz₂
  exact ⟨h.fderiv_eq,h.fderiv.fderiv_eq⟩

lemma corrugationPeriodicWell_plateau (a : ℝ) (z : ℝ × ℝ)
    (hz₁ : |z.1| ≤ 1/2) (hz₂ : |z.2| ≤ 1/2) (hz : (1/4:ℝ)^2 ≤ z.1^2+z.2^2) :
    corrugationPeriodicWell a z = 0 := by
  rw [corrugationPeriodicWell_cell a z hz₁ hz₂]
  exact corrugationDiskWell_zero hz

end
end Yau.Geometry

end OAI
