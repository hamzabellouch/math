import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.SquareCompletion
import OAI.Analysis.CoulombIonization.ThomasFermi.TfEulerDensity
import OAI.Analysis.CoulombIonization.RadialBounds.RadialPotentialSqrtDeriv
import OAI.Analysis.CoulombIonization.FieldAnalysis.FiniteProfile

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
section
open CoulombAtom CoulombPDE

def tfReactionCoefficient : ℝ := 4 * Real.pi * (((5 / 3 : ℝ) * tfKinetic) ^ (3 / 2 : ℝ))⁻¹

lemma tfReactionCoefficient_pos : 0 < tfReactionCoefficient := by
  unfold tfReactionCoefficient
  have ht := tfKinetic_pos
  positivity

lemma tfField_finiteProfile {M Z : ℝ} (hZ : 0 < Z) {ρ : TFSpace → ℝ}
    (ha : TFAdmissible M ρ) (hr : IsRadial ρ)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x)
    (hs : ∀ x, Z ≤ ‖x‖ → ρ x = 0)
    (he : ∀ x, ρ x = tfEulerDensity Z ρ x) :
    FiniteProfile tfReactionCoefficient Z (tfField Z ρ) := by
  have hs' : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ Z := fun y hy => le_of_lt (lt_of_not_ge (fun hh => hy (hs y hh)))
  have hp := tfAdmissible_memLp ha
  have hreg (x : TFSpace) (hx : x ≠ 0) := tfPotential_poisson ha.2.1 hp hr hc hZ.le hs' hx
  have hn (x : TFSpace) (hx : x ≠ 0) : ContDiffAt ℝ 2 (fun y : TFSpace => Z / ‖y‖) x := by
    exact contDiffAt_const.div (contDiffAt_norm ℝ hx) (norm_ne_zero_iff.mpr hx)
  refine ⟨fun x hx => (hn x hx).sub (hreg x hx).1, ?_, ?_, ?_⟩
  · intro x hx
    change Δ ((fun y : TFSpace => Z / ‖y‖) - tfPotential ρ) x =
      reaction tfReactionCoefficient (tfField Z ρ x)
    rw [(hn x hx).laplacian_sub (hreg x hx).1, (hreg x hx).2]
    have heq : (fun y : TFSpace => Z / ‖y‖) = Z • radialPower (-(1/2)) := by
      funext y
      change Z / ‖y‖ = Z * radialPower (-(1/2 : ℝ)) y
      rw [radialPower_half_inv, div_eq_mul_inv]
    rw [heq, laplacian_smul Z (radialPower_contDiffAt _ hx), radial_laplacian_three _ hx]
    norm_num only
    rw [he x]
    unfold reaction tfReactionCoefficient tfEulerDensity
    rw [Real.div_rpow (le_max_right _ _) (mul_pos (by norm_num) tfKinetic_pos).le]
    ring
  · intro ε hε
    obtain ⟨R, hR, hu⟩ := tfPotential_compact_decay ha.2.1 hp hs' (ε/4) (by positivity)
    refine ⟨max R (4*Z/ε), hR.trans_le (le_max_left _ _), ?_⟩
    intro x hx
    have hxn := hR.trans_le ((le_max_left _ _).trans hx)
    have hz : Z / ‖x‖ ≤ ε/4 := by
      have hh := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hx)
      apply (div_le_iff₀ hxn).mpr
      linarith
    have hab := abs_sub (Z/‖x‖) (tfPotential ρ x)
    rw [abs_of_nonneg (div_nonneg hZ.le (norm_nonneg _))] at hab
    unfold tfField
    linarith [hu x ((le_max_left _ _).trans hx)]
  · have hab := ((tfPotential_continuous ha.2.1 hp).abs).continuousAt.eventually
      (eventually_lt_nhds (show |tfPotential ρ 0| < |tfPotential ρ 0| + 1 by linarith))
    obtain ⟨a, ha', hbound⟩ := Metric.eventually_nhds_iff.mp hab
    refine ⟨|tfPotential ρ 0|+1, by positivity, a/2, by positivity, ?_⟩
    intro x _hx hxa
    have hh' := hbound (show dist x 0 < a by simpa only [dist_zero_right] using (show ‖x‖ < a by linarith))
    simpa only [tfField, sub_sub_cancel_left, abs_neg] using hh'.le

theorem tf_finiteProfile_exists (Z : ℝ) (hZ : 0 < Z) :
    ∃ ρ : TFSpace → ℝ, ∃ M : ℝ, TFAdmissible M ρ ∧
      (∀ M' σ, TFAdmissible M' σ → tfFunctional Z ρ + M ≤ tfFunctional Z σ + M') ∧
      IsRadial ρ ∧ FiniteProfile tfReactionCoefficient Z (tfField Z ρ) := by
  obtain ⟨M, ρ, ha, hm, _hn, he, hr, hc, hs⟩ := tf_unit_price_exists_regular Z hZ
  exact ⟨ρ, M, ha, hm, hr, tfField_finiteProfile hZ ha hr hc hs he⟩

end

open MeasureTheory Filter Set Metric Topology
section
open CoulombAtom

structure TFUnitData (Z : ℝ) where
  mass : ℝ
  density : TFSpace → ℝ
  admissible : TFAdmissible mass density
  minimal : ∀ M σ, TFAdmissible M σ → tfFunctional Z density + mass ≤ tfFunctional Z σ + M
  nonneg : ∀ x, 0 ≤ density x
  euler : ∀ x, density x = tfEulerDensity Z density x
  radial : IsRadial density
  continuous : ∀ x, x ≠ 0 → ContinuousAt density x
  support : ∀ x, Z ≤ ‖x‖ → density x = 0

lemma tfUnitData_nonempty (Z : ℝ) (hZ : 0 < Z) : Nonempty (TFUnitData Z) := by
  obtain ⟨M, ρ, ha, hm, hn, he, hr, hc, hs⟩ := tf_unit_price_exists_regular Z hZ
  exact ⟨⟨M, ρ, ha, hm, hn, he, hr, hc, hs⟩⟩

def tfUnitData (Z : ℝ) (hZ : 0 < Z) : TFUnitData Z := Classical.choice (tfUnitData_nonempty Z hZ)

namespace TFUnitData
variable {Z : ℝ} (D : TFUnitData Z)

def field : TFSpace → ℝ := tfField Z D.density
def radialField (r : ℝ) : ℝ := Z/r - radialPotential D.density r
def charge (r : ℝ) : ℝ := Z - radialMass D.density r

lemma finiteProfile (hZ : 0 < Z) : CoulombPDE.FiniteProfile tfReactionCoefficient Z D.field :=
  tfField_finiteProfile hZ D.admissible D.radial D.continuous D.support D.euler

lemma support_le (x : TFSpace) (hx : D.density x ≠ 0) : ‖x‖ ≤ Z :=
  le_of_lt (lt_of_not_ge (fun hh => hx (D.support x hh)))

lemma ray_norm {r : ℝ} (hr : 0 < r) : ‖r • radialAxis‖ = r := by simp [norm_smul, abs_of_pos hr]

lemma ray_ne_zero {r : ℝ} (hr : 0 < r) : r • radialAxis ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [ray_norm hr]; exact hr.ne')

lemma field_radial : IsRadial D.field := by
  intro x y hxy
  unfold field tfField
  rw [hxy, tfPotential_radial D.radial x y hxy]

lemma radialField_eq (hZ : 0 < Z) {x : TFSpace} (hx : x ≠ 0) :
    D.radialField ‖x‖ = D.field x := by
  unfold radialField field tfField
  rw [tfPotential_eq_radialPotential D.admissible.2.1 (tfAdmissible_memLp D.admissible)
    D.radial hZ.le D.support_le hx]

lemma radialField_ray (hZ : 0 < Z) {r : ℝ} (hr : 0 < r) :
    D.radialField r = D.field (r • radialAxis) := by
  simpa only [ray_norm hr] using D.radialField_eq hZ (ray_ne_zero hr)

lemma radialField_nonneg (hZ : 0 < Z) {r : ℝ} (hr : 0 < r) : 0 ≤ D.radialField r := by
  rw [D.radialField_ray hZ hr]
  exact (D.finiteProfile hZ).nonneg hZ _ (ray_ne_zero hr)

lemma mass_le_charge (hZ : 0 < Z) : D.mass ≤ Z := by
  have he := tfPotential_newton_exterior_closed D.admissible.2.1 (tfAdmissible_memLp D.admissible)
    D.radial hZ D.support_le (x := Z • radialAxis) (by rw [ray_norm hZ])
  have hn := (D.finiteProfile hZ).nonneg hZ (Z • radialAxis) (ray_ne_zero hZ)
  rw [field, tfField, he, D.admissible.2.2.1, ray_norm hZ, ← sub_div] at hn
  have hh := mul_nonneg hn hZ.le
  rw [div_mul_cancel₀ _ hZ.ne'] at hh
  exact sub_nonneg.mp hh

lemma charge_nonneg (hZ : 0 < Z) (r : ℝ) : 0 ≤ D.charge r := by
  have hi := setIntegral_le_integral (s := {x : TFSpace | ‖x‖ ≤ r}) D.admissible.2.1
    (Eventually.of_forall D.nonneg)
  rw [D.admissible.2.2.1, ← radialMass_eq_integral D.radial] at hi
  unfold charge
  linarith [D.mass_le_charge hZ]

lemma charge_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt D.charge (-(4 * Real.pi * r^2 * radialTrace D.density r)) r := by
  exact (radialMass_hasDerivAt D.admissible.2.1 D.radial D.continuous hr).const_sub Z

lemma radialField_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt D.radialField (-(D.charge r)/r^2) r := by
  have hh := ((hasDerivAt_const r Z).div (hasDerivAt_id r) hr.ne').sub
    (radialPotential_hasDerivAt D.admissible.2.1 (tfAdmissible_memLp D.admissible)
      D.radial D.continuous hr)
  apply hh.congr_deriv
  simp only [id_eq, zero_mul, zero_sub, mul_one]
  unfold charge
  ring

lemma charge_antitone : AntitoneOn D.charge (Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    (fun r hr => (D.charge_hasDerivAt hr).continuousAt.continuousWithinAt)
    (fun r hr => (D.charge_hasDerivAt (interior_subset hr)).hasDerivWithinAt)
  intro r _hr
  exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (sq_nonneg _)) (D.nonneg _))

lemma radialField_antitone (hZ : 0 < Z) : AntitoneOn D.radialField (Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    (fun r hr => (D.radialField_hasDerivAt hr).continuousAt.continuousWithinAt)
    (fun r hr => (D.radialField_hasDerivAt (interior_subset hr)).hasDerivWithinAt)
  intro r _hr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (D.charge_nonneg hZ r)) (sq_nonneg r)

lemma charge_bound (hZ : 0 < Z) {r : ℝ} (hr : 0 < r) :
    D.charge r ≤ 2*r*D.radialField (r/2) := by
  obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_slope D.radialField
    (fun t => -(D.charge t)/t^2) (show r/2 < r by linarith)
    (fun t ht => (D.radialField_hasDerivAt (show 0 < t by linarith [ht.1])).continuousAt.continuousWithinAt)
    (fun t ht => D.radialField_hasDerivAt (show 0 < t by linarith [ht.1]))
  have hcp : 0 < c := by linarith [hc.1]
  have hq := D.charge_antitone hcp hr hc.2.le
  have hq0 := D.charge_nonneg hZ r
  have hq1 := D.charge_nonneg hZ c
  have hratio : D.charge r/r^2 ≤ D.charge c/c^2 :=
    (div_le_div_of_nonneg_right hq (sq_nonneg r)).trans
      (div_le_div_of_nonneg_left hq1 (sq_pos_of_pos hcp) (by nlinarith [hc.2]))
  have hs : (D.radialField (r/2) - D.radialField r)/(r-r/2) = D.charge c/c^2 := by
    calc
      _ = -((D.radialField r - D.radialField (r/2))/(r-r/2)) := by ring
      _ = -(-(D.charge c)/c^2) := congrArg Neg.neg he.symm
      _ = _ := by ring
  rw [← hs] at hratio
  have hh := (div_le_div_iff₀ (sq_pos_of_pos hr) (show 0 < r-r/2 by linarith)).mp hratio
  have hf := D.radialField_nonneg hZ hr
  nlinarith [mul_nonneg hf (sq_nonneg r)]

lemma radialField_upper (hZ : 0 < Z) {r : ℝ} (hr : 0 < r) :
    D.radialField r ≤ 1 + CoulombPDE.sommerfeldCoefficient tfReactionCoefficient / r^4 := by
  have hh := (D.finiteProfile hZ).upper tfReactionCoefficient_pos (r • radialAxis) (ray_ne_zero hr)
  rw [← D.radialField_ray hZ hr] at hh
  have he := CoulombPDE.norm_four_mul_radialPower (ray_ne_zero hr)
  rw [ray_norm hr] at he
  have he' : CoulombPDE.radialPower (-2) (r • radialAxis) = 1/r^4 := by
    apply (eq_div_iff (pow_ne_zero _ hr.ne')).mpr
    nlinarith
  rwa [he', ← div_eq_mul_one_div] at hh

lemma charge_equation {r : ℝ} (hr : 0 < r) (hZ : 0 < Z) :
    HasDerivAt D.charge (-r^2 * CoulombPDE.reaction tfReactionCoefficient (D.radialField r)) r := by
  have hh := D.charge_hasDerivAt hr
  convert hh using 1
  have hray : D.radialField r = tfField Z D.density (r • radialAxis) := D.radialField_ray hZ hr
  rw [radialTrace, D.euler, tfEulerDensity, ← hray]
  unfold CoulombPDE.reaction tfReactionCoefficient
  rw [Real.div_rpow (le_max_right _ _) (mul_pos (by norm_num) tfKinetic_pos).le]
  ring

lemma radialField_le_charge_div {r : ℝ} : D.radialField r ≤ D.charge r / r := by
  have ht : 0 ≤ radialTail D.density r := by
    unfold radialTail
    apply mul_nonneg (by positivity)
    apply setIntegral_nonneg measurableSet_Ioi
    intro s _hs
    unfold radialTailIntegrand
    by_cases hp : 0 < s
    · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hp)]
      exact mul_nonneg hp.le (D.nonneg _)
    · rw [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hp)]
  unfold radialField charge radialPotential
  rw [sub_div]
  linarith

def chargeCap (a : ℝ) : ℝ := 2*a*(1 + CoulombPDE.sommerfeldCoefficient tfReactionCoefficient / (a/2)^4)
def slopeCap (a : ℝ) : ℝ := chargeCap a / a^2

lemma chargeCap_pos {a : ℝ} (ha : 0 < a) : 0 < chargeCap a := by
  unfold chargeCap
  have hh := CoulombPDE.sommerfeldCoefficient_pos tfReactionCoefficient_pos
  positivity

lemma slopeCap_pos {a : ℝ} (ha : 0 < a) : 0 < slopeCap a :=
  div_pos (chargeCap_pos ha) (sq_pos_of_pos ha)

lemma charge_le_cap (hZ : 0 < Z) {a r : ℝ} (ha : 0 < a) (hr : a ≤ r) :
    D.charge r ≤ chargeCap a := by
  apply (D.charge_antitone ha (ha.trans_le hr) hr).trans
  exact (D.charge_bound hZ ha).trans (mul_le_mul_of_nonneg_left
    (D.radialField_upper hZ (show 0 < a/2 by positivity)) (by positivity))

lemma radialField_far_bound (hZ : 0 < Z) {a r : ℝ} (ha : 0 < a) (hr : a ≤ r) :
    D.radialField r ≤ chargeCap a / r :=
  D.radialField_le_charge_div.trans (div_le_div_of_nonneg_right
    (D.charge_le_cap hZ ha hr) (ha.trans_le hr).le)

lemma deriv_bound (hZ : 0 < Z) {a r : ℝ} (ha : 0 < a) (hr : a ≤ r) :
    ‖deriv D.radialField r‖ ≤ slopeCap a := by
  rw [(D.radialField_hasDerivAt (ha.trans_le hr)).deriv,
    norm_div, norm_neg, Real.norm_of_nonneg (D.charge_nonneg hZ r), Real.norm_of_nonneg (sq_nonneg r)]
  exact (div_le_div_of_nonneg_right (D.charge_le_cap hZ ha hr) (sq_nonneg r)).trans
    (div_le_div_of_nonneg_left (chargeCap_pos ha).le (sq_pos_of_pos ha) (by nlinarith))

lemma lipschitz (hZ : 0 < Z) {a : ℝ} (ha : 0 < a) :
    LipschitzOnWith ⟨slopeCap a, (slopeCap_pos ha).le⟩ D.radialField (Ici a) := by
  apply (convex_Ici a).lipschitzOnWith_of_nnnorm_deriv_le
    (fun r hr => (D.radialField_hasDerivAt (ha.trans_le hr)).differentiableAt)
  exact fun r hr => D.deriv_bound hZ ha hr

end TFUnitData
end

open MeasureTheory Filter Set Metric Topology

end CoulombAnalysis

end

end OAI
