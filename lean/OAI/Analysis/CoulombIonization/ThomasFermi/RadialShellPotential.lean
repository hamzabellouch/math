import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SpatialRotation

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombAnalysis

lemma tfPotential_radial_max {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5/3)) (hr : IsRadial ρ) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R) (x : TFSpace) :
    tfPotential ρ x = ∫ y, ρ y / max ‖x‖ ‖y‖ := by
  by_cases hx : x = 0
  · subst x
    simp only [tfPotential, norm_zero, max_eq_right (norm_nonneg _), zero_sub, norm_neg]
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hi : Integrable (fun y => ρ y/max ‖x‖ ‖y‖) := by
    apply (h1.norm.div_const ‖x‖).mono'
      (h1.aemeasurable.div
        ((continuous_const.max continuous_norm).aemeasurable)).aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      change ‖ρ y/max ‖x‖ ‖y‖‖ ≤ ‖ρ y‖/‖x‖
      rw [norm_div, Real.norm_of_nonneg
        (show 0 ≤ max ‖x‖ ‖y‖ from (norm_nonneg x).trans (le_max_left _ _))]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hx0 (le_max_left _ _)
  rw [tfPotential_newton h1 hp hr hR hs hx]
  let A := {y : TFSpace | ‖y‖ ≤ ‖x‖}
  have hA : MeasurableSet A := measurableSet_le measurable_norm measurable_const
  rw [← integral_add_compl hA hi]
  congr 1
  · rw [← integral_div]
    apply setIntegral_congr_fun hA
    intro y hy
    change ρ y/‖x‖ = ρ y/max ‖x‖ ‖y‖
    rw [max_eq_left (show ‖y‖ ≤ ‖x‖ from hy)]
  · have he : Aᶜ = {y : TFSpace | ‖x‖ < ‖y‖} := by ext y; simp [A, not_le]
    rw [he]
    apply setIntegral_congr_fun (measurableSet_lt measurable_const measurable_norm)
    intro y hy
    change ρ y/‖y‖ = ρ y/max ‖x‖ ‖y‖
    rw [max_eq_right hy.le]

lemma tfPotential_annular_bounds {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5/3)) (hr : IsRadial ρ) (hn : ∀ y, 0 ≤ ρ y)
    (hm : ∫ y, ρ y = 1) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : ∀ y, ρ y ≠ 0 → a ≤ ‖y‖ ∧ ‖y‖ ≤ b) (x : TFSpace) :
    1/max ‖x‖ b ≤ tfPotential ρ x ∧ tfPotential ρ x ≤ 1/max ‖x‖ a := by
  rw [tfPotential_radial_max h1 hp hr (ha.le.trans hab) (fun y hy => (hs y hy).2)]
  have ham : 0 < max ‖x‖ a := ha.trans_le (le_max_right _ _)
  have hbm : 0 < max ‖x‖ b := (ha.trans_le hab).trans_le (le_max_right _ _)
  have hind (y : TFSpace) : ‖ρ y/max ‖x‖ ‖y‖‖ ≤ ρ y/max ‖x‖ a := by
    by_cases hy : ρ y = 0
    · simp [hy]
    · rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (hn _) (le_max_left _ _ |>.trans' (norm_nonneg _)))]
      exact div_le_div_of_nonneg_left (hn _) ham (max_le_max_left _ (hs y hy).1)
  have hi : Integrable (fun y => ρ y/max ‖x‖ ‖y‖) :=
    (h1.div_const _).mono' (h1.aemeasurable.div
      ((continuous_const.max continuous_norm).aemeasurable)).aestronglyMeasurable
      (Eventually.of_forall hind)
  constructor
  · rw [← hm, ← integral_div]
    apply integral_mono (h1.div_const _) hi
    intro y
    by_cases hy : ρ y = 0
    · simp [hy]
    · have hp0 : 0 < max ‖x‖ ‖y‖ := ham.trans_le (max_le_max_left _ (hs y hy).1)
      exact div_le_div_of_nonneg_left (hn _) hp0 (max_le_max_left _ (hs y hy).2)
  · rw [← hm, ← integral_div]
    exact integral_mono hi (h1.div_const _) (fun y => (le_abs_self _).trans (hind y))

end CoulombAnalysis
namespace CoulombAtom

lemma averagedPacket_annulus (p : Space) {r : ℝ} (hr : 0 < r) {x : Space}
    (hx : averagedPacket p r x ≠ 0) : ‖p‖-r ≤ ‖x‖ ∧ ‖x‖ ≤ ‖p‖+r := by
  refine ⟨?_,averagedPacket_support p hr hx⟩
  by_contra hn
  apply hx
  unfold averagedPacket
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro g
  by_contra hg
  have hd := packetDensity_support (rotate g p) hr hg
  have hh := norm_add_le (rotate g p-x) x
  rw [sub_add_cancel,(rotate g).norm_map,norm_sub_rev] at hh
  linarith

lemma averagedPacket_potential_bounds (p : Space) {r : ℝ} (hr : 0 < r)
    (hpr : r < ‖p‖) (x : Space) :
    1/max ‖x‖ (‖p‖+r) ≤ CoulombAnalysis.tfPotential (averagedPacket p r) x ∧
      CoulombAnalysis.tfPotential (averagedPacket p r) x ≤ 1/max ‖x‖ (‖p‖-r) :=
  CoulombAnalysis.tfPotential_annular_bounds (averagedPacket_integrable p hr)
    (averagedPacket_memLp p hr) (averagedPacket_radial p r) (averagedPacket_nonneg p r)
    (averagedPacket_mass p hr) (by linarith) (by linarith)
    (fun _ hh => averagedPacket_annulus p hr hh) x

end CoulombAtom

end

end OAI
