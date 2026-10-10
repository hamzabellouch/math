import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.Model

namespace OAI

/-!
# The explicit cap in the isolated-well construction

The quintic transition is the normalized integral of a positive multiple
of `s²(1-s)²`. Capping removes a whole neighbourhood of both nuclear poles.
The resulting pointwise bound is uniform in the secondary displacements,
as required before any energy tuning is carried out.
-/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def wellTransition (s : ℝ) : ℝ := 6 * s ^ 5 - 15 * s ^ 4 + 10 * s ^ 3

theorem wellTransition_bounds {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ wellTransition s ∧ wellTransition s ≤ 1 := by
  have hleft : wellTransition s =
      s ^ 3 * (1 + 3 * (1 - s) + 6 * (1 - s) ^ 2) := by
    unfold wellTransition
    ring
  have hright : 1 - wellTransition s = (1 - s) ^ 3 * (1 + 3 * s + 6 * s ^ 2) := by
    unfold wellTransition
    ring
  have h0 : 0 ≤ wellTransition s := by rw [hleft]; positivity
  have h1 : 0 ≤ 1 - wellTransition s := by rw [hright]; positivity
  exact ⟨h0, by linarith⟩

def wellCap (t : ℝ) : ℝ :=
  if t ≤ 1 / 16 then 0 else if 1 / 8 ≤ t then 1 else wellTransition (16 * t - 1)

theorem wellCap_eq_zero {t : ℝ} (ht : t ≤ 1 / 16) : wellCap t = 0 := by
  simp only [wellCap, ite_eq_left ht]

theorem wellCap_eq_one {t : ℝ} (ht : 1 / 8 ≤ t) : wellCap t = 1 := by
  have hn : ¬ t ≤ 1 / 16 := by linarith
  simp only [wellCap, ite_eq_right hn, ite_eq_left ht]

theorem wellCap_bounds (t : ℝ) : 0 ≤ wellCap t ∧ wellCap t ≤ 1 := by
  unfold wellCap
  split_ifs with h0 h1
  · norm_num
  · norm_num
  · exact wellTransition_bounds (by linarith) (by linarith)

theorem wellCap_nonzero_radius {D r : ℝ} (hD : 0 < D)
    (hcap : wellCap (r / D) ≠ 0) : D / 16 < r := by
  have h : ¬ r / D ≤ 1 / 16 := fun hr => hcap (wellCap_eq_zero hr)
  have hr := (lt_div_iff₀ hD).mp (lt_of_not_ge h)
  linarith

def sitePotential (q q' : ℝ) (center displacement x : Position) : ℝ :=
  q * Coulomb.coulombKernel (x - center) +
    q' * Coulomb.coulombKernel (x - center - displacement)

def cappedSitePotential (D q q' : ℝ) (center displacement x : Position) : ℝ :=
  wellCap (‖x - center‖ / D) * sitePotential q q' center displacement x

theorem sitePotential_nonneg {q q' : ℝ} (hq : 0 ≤ q) (hq' : 0 ≤ q')
    (center displacement x : Position) : 0 ≤ sitePotential q q' center displacement x := by
  unfold sitePotential Coulomb.coulombKernel
  positivity

theorem cappedSitePotential_nonneg {D q q' : ℝ} (hq : 0 ≤ q) (hq' : 0 ≤ q')
    (center displacement x : Position) :
    0 ≤ cappedSitePotential D q q' center displacement x :=
  mul_nonneg (wellCap_bounds _).1 (sitePotential_nonneg hq hq' _ _ _)

theorem cappedSitePotential_zero_near_primary {D q q' : ℝ} (hD : 0 < D)
    (center displacement x : Position) (hx : ‖x - center‖ ≤ D / 16) :
    cappedSitePotential D q q' center displacement x = 0 := by
  unfold cappedSitePotential
  rw [wellCap_eq_zero ((div_le_iff₀ hD).mpr (by linarith)), zero_mul]

/-- The cap removes the secondary pole together with an explicit surrounding
ball; the cancellation is not merely a convention for the value at the pole. -/
theorem cappedSitePotential_zero_near_secondary {D q q' : ℝ}
    (hD : 128 ≤ D) (center displacement x : Position)
    (hdisp : ‖displacement‖ ≤ 4)
    (hx : ‖x - center - displacement‖ ≤ D / 32) :
    cappedSitePotential D q q' center displacement x = 0 := by
  have hD0 : 0 < D := by linarith
  have hnorm : ‖x - center‖ ≤ D / 16 := by
    calc
      ‖x - center‖ = ‖(x - center - displacement) + displacement‖ := by congr 1; abel
      _ ≤ ‖x - center - displacement‖ + ‖displacement‖ := norm_add_le _ _
      _ ≤ D / 16 := by linarith
  unfold cappedSitePotential
  rw [wellCap_eq_zero ((div_le_iff₀ hD0).mpr (by linarith)), zero_mul]

theorem cappedSitePotential_bound {D q q' : ℝ} (hD : 128 ≤ D)
    (hq : 0 ≤ q) (hq' : 0 ≤ q') (center displacement x : Position)
    (hdisp : ‖displacement‖ ≤ 4) :
    cappedSitePotential D q q' center displacement x ≤ (16 * q + 32 * q') / D := by
  have hD0 : 0 < D := by linarith
  by_cases hc : wellCap (‖x - center‖ / D) = 0
  · simp only [cappedSitePotential, hc, zero_mul]
    positivity
  · have hr := wellCap_nonzero_radius hD0 hc
    have hs : D / 32 ≤ ‖x - center - displacement‖ := by
      have ht : ‖x - center‖ ≤ ‖x - center - displacement‖ + ‖displacement‖ := by
        calc
          _ = ‖(x - center - displacement) + displacement‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      linarith
    have hprimary : Coulomb.coulombKernel (x - center) ≤ 16 / D := by
      unfold Coulomb.coulombKernel
      calc
        _ ≤ (D / 16)⁻¹ := inv_anti₀ (by positivity) hr.le
        _ = _ := by ring
    have hsecondary : Coulomb.coulombKernel (x - center - displacement) ≤ 32 / D := by
      unfold Coulomb.coulombKernel
      calc
        _ ≤ (D / 32)⁻¹ := inv_anti₀ (by positivity) hs
        _ = _ := by ring
    calc
      cappedSitePotential D q q' center displacement x ≤ sitePotential q q' center displacement x :=
        mul_le_of_le_one_left (sitePotential_nonneg hq hq' _ _ _) (wellCap_bounds _).2
      _ ≤ q * (16 / D) + q' * (32 / D) :=
        add_le_add (mul_le_mul_of_nonneg_left hprimary hq)
          (mul_le_mul_of_nonneg_left hsecondary hq')
      _ = _ := by ring

def backgroundPotential {m : ℕ} (D q q' : ℝ) (center displacement : Fin m → Position)
    (site : Fin m) (x : Position) : ℝ :=
  ∑ j, if j = site then 0 else cappedSitePotential D q q' (center j) (displacement j) x

theorem backgroundPotential_bounds {m : ℕ} {D q q' : ℝ} (hD : 128 ≤ D)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hq' : 0 ≤ q') (hq'1 : q' ≤ 1)
    (center displacement : Fin m → Position) (hdisp : ∀ j, ‖displacement j‖ ≤ 4)
    (site : Fin m) (x : Position) :
    0 ≤ backgroundPotential D q q' center displacement site x ∧
      backgroundPotential D q q' center displacement site x ≤ 48 * m / D := by
  have hD0 : 0 < D := by linarith
  constructor
  · exact Finset.sum_nonneg fun j _ => by
      split_ifs
      · exact le_rfl
      · exact cappedSitePotential_nonneg hq hq' _ _ _
  · calc
      _ ≤ ∑ _j : Fin m, (48 / D : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs
        · positivity
        · apply (cappedSitePotential_bound hD hq hq' _ _ _ (hdisp j)).trans
          apply (div_le_div_iff_of_pos_right hD0).mpr
          linarith
      _ = _ := by simp; ring

end ContinuumCoulomb

end

end OAI
