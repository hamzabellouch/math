import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SmoothNewton
import OAI.Analysis.CoulombIonization.ThomasFermi.RadialShellPotential

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

lemma tfPotential_radial_lower {ρ : Space → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5/3)) (hr : IsRadial ρ) (hn : ∀ y, 0 ≤ ρ y)
    (hm : ∫ y, ρ y = 1) {R : ℝ} (hR : 0 < R)
    (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R) (x : Space) :
    1/max ‖x‖ R ≤ tfPotential ρ x := by
  have hmajor : Integrable (fun y => ρ y/‖y‖) := by
    simpa only [zero_sub,norm_neg] using tfPotential_integrable h1 hp 0
  have hi : Integrable (fun y => ρ y/max ‖x‖ ‖y‖) := by
    apply hmajor.mono'
      (h1.aemeasurable.div ((continuous_const.max continuous_norm).aemeasurable)).aestronglyMeasurable
    filter_upwards [ae_ne_point (0 : Space)] with y hy
    change ‖ρ y/max ‖x‖ ‖y‖‖ ≤ ρ y/‖y‖
    rw [Real.norm_of_nonneg (div_nonneg (hn _) ((norm_nonneg x).trans (le_max_left _ _)))]
    exact div_le_div_of_nonneg_left (hn y) (norm_pos_iff.mpr hy) (le_max_right _ _)
  rw [tfPotential_radial_max h1 hp hr hR.le hs,←hm,←integral_div]
  apply integral_mono_ae (h1.div_const _) hi
  filter_upwards [ae_ne_point (0 : Space)] with y hy
  by_cases hz : ρ y = 0
  · simp [hz]
  · exact div_le_div_of_nonneg_left (hn y)
      ((norm_pos_iff.mpr hy).trans_le (le_max_right _ _)) (max_le_max_left _ (hs y hz))

def newtonComparisonTest (r R : ℝ) (x : Space) : ℝ :=
  tfPotential (packetDensity 0 r) x-tfPotential (packetDensity 0 R) x

lemma newtonComparisonTest_smooth {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    ContDiff ℝ 2 (newtonComparisonTest r R) :=
  (tfPotential_contDiff ((packetDensity_smooth 0 r).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    (packetDensity_compact 0 hr)).sub
  (tfPotential_contDiff ((packetDensity_smooth 0 R).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    (packetDensity_compact 0 hR))

lemma newtonComparisonTest_tsupport {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R) :
    tsupport (newtonComparisonTest r R) ⊆ closedBall 0 R := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hn
  have hxR : R ≤ ‖x‖ := (not_le.mp (by simpa only [mem_closedBall,dist_zero_right] using hn)).le
  apply hx
  simp only [newtonComparisonTest]
  rw [tfPotential_newton_exterior_closed (packetDensity_integrable 0 hr)
    (packetDensity_memLp 0 hr) (packetDensity_radial r) hr
    (fun y hy => by simpa only [sub_zero] using packetDensity_support 0 hr hy) (hrR.trans hxR),
    tfPotential_newton_exterior_closed (packetDensity_integrable 0 hR)
    (packetDensity_memLp 0 hR) (packetDensity_radial R) hR
    (fun y hy => by simpa only [sub_zero] using packetDensity_support 0 hR hy) hxR,
    packetDensity_mass 0 hr,packetDensity_mass 0 hR,sub_self]

lemma newtonComparisonTest_compact {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    HasCompactSupport (newtonComparisonTest r R) := by
  by_cases hh : r ≤ R
  · exact (isCompact_closedBall 0 R).of_isClosed_subset isClosed_closure
      (newtonComparisonTest_tsupport hr hR hh)
  · have ht : HasCompactSupport (newtonComparisonTest R r) := (isCompact_closedBall 0 r).of_isClosed_subset isClosed_closure
      (newtonComparisonTest_tsupport hR hr (le_of_not_ge hh))
    have he : newtonComparisonTest r R = -newtonComparisonTest R r := by
      funext x; simp only [newtonComparisonTest,Pi.neg_apply,neg_sub]
    rw [he]
    exact ht.neg

lemma newtonComparisonTest_laplacian {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    Δ (newtonComparisonTest r R) = fun x => 4*Real.pi*(packetDensity 0 R x-packetDensity 0 r x) := by
  funext x
  rw [show newtonComparisonTest r R = tfPotential (packetDensity 0 r)-tfPotential (packetDensity 0 R) from rfl,
    ((tfPotential_contDiff ((packetDensity_smooth 0 r).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
      (packetDensity_compact 0 hr)).contDiffAt).laplacian_sub
      ((tfPotential_contDiff ((packetDensity_smooth 0 R).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
      (packetDensity_compact 0 hR)).contDiffAt),
    tfPotential_poisson_global ((packetDensity_smooth 0 r).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
      (packetDensity_compact 0 hr) (packetDensity_radial r),
    tfPotential_poisson_global ((packetDensity_smooth 0 R).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
      (packetDensity_compact 0 hR) (packetDensity_radial R)]
  ring

lemma newtonComparisonTest_nonneg {r R M : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hrR : r ≤ R) (hM : ∀ x ∈ closedBall (0 : Space) R, tfPotential (packetDensity 0 R) x ≤ M)
    (hrM : M ≤ 1/r) (x : Space) : 0 ≤ newtonComparisonTest r R x := by
  apply sub_nonneg.mpr
  by_cases hx : ‖x‖ ≤ r
  · have hh := tfPotential_radial_lower (packetDensity_integrable 0 hr)
      (packetDensity_memLp 0 hr) (packetDensity_radial r) (packetDensity_nonneg 0 r)
      (packetDensity_mass 0 hr) hr
      (fun y hy => by simpa only [sub_zero] using packetDensity_support 0 hr hy) x
    rw [max_eq_right hx] at hh
    exact (hM x (by simpa only [mem_closedBall,dist_zero_right] using hx.trans hrR)).trans (hrM.trans hh)
  · have hx0 : x ≠ 0 := norm_pos_iff.mp (hr.trans (lt_of_not_ge hx))
    have hh := radial_potential_le_point (packetDensity_integrable 0 hR)
      (packetDensity_memLp 0 hR) (packetDensity_nonneg 0 R) (packetDensity_radial R)
      hR.le (fun y hy => by simpa only [sub_zero] using packetDensity_support 0 hR hy) hx0
    rw [packetDensity_mass 0 hR] at hh
    rw [tfPotential_newton_exterior_closed (packetDensity_integrable 0 hr)
      (packetDensity_memLp 0 hr) (packetDensity_radial r) hr
      (fun y hy => by simpa only [sub_zero] using packetDensity_support 0 hr hy) (le_of_not_ge hx),
      packetDensity_mass 0 hr]
    exact hh

def packetSecondMoment (r : ℝ) : ℝ := ∫ x : Space, ‖x‖^2*packetDensity 0 r x

lemma packetSecondMoment_nonneg (r : ℝ) : 0 ≤ packetSecondMoment r :=
  integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (packetDensity_nonneg 0 r x))

lemma packetSecondMoment_integrable {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : Space => ‖x‖^2*packetDensity 0 r x) :=
  ((continuous_norm.pow 2).mul (packetDensity_continuous 0 r)).integrable_of_hasCompactSupport
    (packetDensity_compact 0 hr).mul_left

lemma packetSecondMoment_le {r : ℝ} (hr : 0 < r) : packetSecondMoment r ≤ r^2 := by
  calc
    _ ≤ ∫ x : Space, r^2*packetDensity 0 r x := by
      apply integral_mono (packetSecondMoment_integrable hr) ((packetDensity_integrable 0 hr).const_mul _)
      intro x
      by_cases hx : packetDensity 0 r x = 0
      · simp [hx]
      · apply mul_le_mul_of_nonneg_right _ (packetDensity_nonneg 0 r x)
        exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [sub_zero] using packetDensity_support 0 hr hx) _
    _ = r^2 := by rw [integral_const_mul,packetDensity_mass 0 hr,mul_one]

lemma packetSecondMoment_pos {r : ℝ} (hr : 0 < r) : 0 < packetSecondMoment r := by
  by_contra hh
  have he := le_antisymm (le_of_not_gt hh) (packetSecondMoment_nonneg r)
  have hz := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun x => mul_nonneg (sq_nonneg ‖x‖) (packetDensity_nonneg 0 r x))
    (packetSecondMoment_integrable hr)).mp he
  have hd : packetDensity 0 r =ᵐ[volume] 0 := by
    filter_upwards [hz,ae_ne_point (0 : Space)] with x hx hn
    exact (mul_eq_zero.mp hx).resolve_left (pow_ne_zero _ (norm_ne_zero_iff.mpr hn))
  have hm := integral_congr_ae hd
  rw [packetDensity_mass 0 hr] at hm
  simp only [Pi.zero_apply,integral_zero] at hm
  norm_num at hm

lemma newtonComparisonTest_integral {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    6*(∫ x, newtonComparisonTest r R x) = 4*Real.pi*(packetSecondMoment R-packetSecondMoment r) := by
  have he := compact_laplacian_green (contDiff_norm_sq ℝ)
    (newtonComparisonTest_smooth hr hR) (newtonComparisonTest_compact hr hR)
  have hl : Δ (fun x : Space => ‖x‖^2) = fun _ => (6 : ℝ) := by
    funext x
    have h := CoulombPDE.laplacian_norm_sq x
    norm_num [Space,finrank_euclideanSpace_fin] at h
    exact h
  rw [hl,newtonComparisonTest_laplacian hr hR] at he
  simp only at he
  rw [←integral_const_mul,←he]
  calc
    _ = ∫ x : Space, 4*Real.pi*(‖x‖^2*packetDensity 0 R x-‖x‖^2*packetDensity 0 r x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = _ := by rw [integral_const_mul,integral_sub (packetSecondMoment_integrable hR)
      (packetSecondMoment_integrable hr)]; rfl

end CoulombAnalysis

end

end OAI
