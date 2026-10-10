import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CoulombNear

namespace OAI

noncomputable section

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
namespace CoulombAnalysis

def IsRadial (f : TFSpace → ℝ) : Prop := ∀ x y, ‖x‖ = ‖y‖ → f x = f y

lemma tfPotential_radial {ρ : TFSpace → ℝ} (hr : IsRadial ρ) : IsRadial (tfPotential ρ) := by
  intro x y hxy
  obtain ⟨e, he⟩ := exists_orthogonal_map_norm_eq x y hxy
  unfold tfPotential
  have hi := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun z => ρ z / ‖y - z‖)
  rw [← hi, ← he]
  apply integral_congr_ae (Eventually.of_forall fun z => ?_)
  rw [hr (e z) z (e.norm_map z), ← e.map_sub, e.norm_map]

lemma tfPotential_compact_bound {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hp : MemLp ρ (5 / 3))
    {R : ℝ} (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R) {x : TFSpace} (hx : R < ‖x‖) :
    |tfPotential ρ x| ≤ (∫ y, |ρ y|) / (‖x‖ - R) := by
  have hi := tfPotential_integrable h1 hp x
  calc
    _ ≤ ∫ y, |ρ y / ‖x - y‖| := by
      simpa only [tfPotential, Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => ρ y / ‖x - y‖)
    _ ≤ ∫ y, |ρ y| / (‖x‖ - R) := by
      apply integral_mono hi.norm (h1.abs.div_const _)
      intro y
      simp only [Real.norm_eq_abs]
      by_cases hy : ρ y = 0
      · simp [hy]
      · have hb := hs y hy
        have hn : ‖x‖ - R ≤ ‖x - y‖ := by
          have ht := norm_sub_le x y
          have ht' := norm_add_le (x - y) y
          rw [sub_add_cancel] at ht'
          linarith
        rw [abs_div, abs_norm]
        exact div_le_div_of_nonneg_left (abs_nonneg _) (sub_pos.mpr hx) hn
    _ = _ := by simp only [div_eq_mul_inv, integral_mul_const]

lemma tfPotential_compact_mass_bound {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hp : MemLp ρ (5 / 3))
    {R : ℝ} (hR : 0 ≤ R) (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R)
    {x : TFSpace} (hx : R < ‖x‖) :
    |‖x‖ * tfPotential ρ x - ∫ y, ρ y| ≤
      R / (‖x‖ - R) * (∫ y, |ρ y|) := by
  have hi := tfPotential_integrable h1 hp x
  have he : ‖x‖ * tfPotential ρ x - ∫ y, ρ y =
      ∫ y, (‖x‖ * (ρ y / ‖x - y‖) - ρ y) := by
    rw [integral_sub (hi.const_mul _) h1, integral_const_mul]
    rfl
  rw [he]
  calc
    _ ≤ ∫ y, |‖x‖ * (ρ y / ‖x - y‖) - ρ y| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun y => ‖x‖ * (ρ y / ‖x - y‖) - ρ y)
    _ ≤ ∫ y, R / (‖x‖ - R) * |ρ y| := by
      apply integral_mono ((hi.const_mul _).sub' h1).norm (h1.abs.const_mul _)
      intro y
      simp only [Real.norm_eq_abs]
      by_cases hy : ρ y = 0
      · simp [hy]
      · have hb := hs y hy
        have hn : ‖x‖ - R ≤ ‖x - y‖ := by
          have ht' := norm_add_le (x - y) y
          rw [sub_add_cancel] at ht'
          linarith
        have hnpos : 0 < ‖x - y‖ := (sub_pos.mpr hx).trans_le hn
        have hdiff : |‖x‖ - ‖x - y‖| ≤ R := by
          have ht := abs_norm_sub_norm_le x (x - y)
          simp only [sub_sub_cancel] at ht
          exact ht.trans hb
        have hdiv : |‖x‖ / ‖x - y‖ - 1| ≤ R / (‖x‖ - R) := by
          rw [← div_self hnpos.ne', ← sub_div, abs_div, abs_norm]
          exact (div_le_div_of_nonneg_right hdiff (norm_nonneg _)).trans
            (div_le_div_of_nonneg_left hR (sub_pos.mpr hx) hn)
        calc
          _ = |‖x‖ / ‖x - y‖ - 1| * |ρ y| := by rw [← abs_mul]; congr 1; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hdiv (abs_nonneg _)
    _ = _ := integral_const_mul _ _

lemma tfPotential_compact_decay {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hp : MemLp ρ (5 / 3))
    {R : ℝ} (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R) :
    ∀ ε > 0, ∃ S > 0, ∀ x, S ≤ ‖x‖ → |tfPotential ρ x| ≤ ε := by
  intro ε hε
  let A := ∫ y, |ρ y|
  have hA : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
  let S := max R 0 + 1 + A / ε
  have hS : 0 < S := by dsimp [S]; positivity
  refine ⟨S, hS, ?_⟩
  intro x hx
  have hxr : R < ‖x‖ := by
    have hmax := le_max_left R 0
    have hade := div_nonneg hA hε.le
    dsimp [S] at hx
    linarith
  apply (tfPotential_compact_bound h1 hp hs hxr).trans
  apply (div_le_iff₀ (sub_pos.mpr hxr)).mpr
  have hmax := le_max_left R 0
  have hbound : A / ε ≤ ‖x‖ - R := by dsimp [S] at hx; linarith
  have hh := (div_le_iff₀ hε).mp hbound
  linarith

lemma tfPotential_harmonic_outside {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    {R : ℝ} (hR : 0 ≤ R) (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R)
    {x : TFSpace} (hx : R < ‖x‖) :
    ContDiffAt ℝ 2 (tfPotential ρ) x ∧ Δ (tfPotential ρ) x = 0 := by
  apply tfPotential_harmonic_separated h1.locallyIntegrable (sub_pos.mpr hx)
    (show 0 ≤ ‖x‖ + R by positivity)
  intro y hy
  have hb := hs y hy
  have ht := norm_add_le (x - y) y
  rw [sub_add_cancel] at ht
  exact ⟨by linarith, (norm_sub_le x y).trans (by linarith)⟩

theorem tfPotential_newton_exterior {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R) {x : TFSpace} (hx : R < ‖x‖) :
    tfPotential ρ x = (∫ y, ρ y) / ‖x‖ := by
  let a := (R + ‖x‖) / 2
  have haR : R < a := by dsimp [a]; linarith
  have ha : 0 < a := hR.trans_lt haR
  have hax : a ≤ ‖x‖ := by dsimp [a]; linarith
  let e : TFSpace := EuclideanSpace.single 0 1
  have he : ‖e‖ = 1 := by simp [e]
  have hya : ‖a • e‖ = a := by simp [norm_smul, he, abs_of_pos ha]
  let q := a * tfPotential ρ (a • e)
  let G : TFSpace → ℝ := fun y => q * CoulombPDE.radialPower (-(1 / 2)) y
  have hg (y : TFSpace) : G y = q / ‖y‖ := by
    dsimp [G]; rw [CoulombPDE.radialPower_half_inv, div_eq_mul_inv]
  have hy0 (y : TFSpace) (hy : a ≤ ‖y‖) : y ≠ 0 := norm_pos_iff.mp (ha.trans_le hy)
  have hgreg (y : TFSpace) (hy : a ≤ ‖y‖) : ContDiffAt ℝ 2 G y :=
    contDiffAt_const.mul (CoulombPDE.radialPower_contDiffAt _ (hy0 y hy))
  have hglap (y : TFSpace) (hy : a ≤ ‖y‖) : Δ G y = 0 := by
    change (Δ (q • (CoulombPDE.radialPower (-(1 / 2)) : TFSpace → ℝ)) : TFSpace → ℝ) y = 0
    rw [laplacian_smul q (CoulombPDE.radialPower_contDiffAt _ (hy0 y hy)),
      CoulombPDE.radial_laplacian_three _ (hy0 y hy)]
    norm_num
  have hEq := CoulombPDE.exterior_harmonic_unique (a := a)
    (fun y hy => (tfPotential_harmonic_outside h1 hR hs (haR.trans_le hy)).1)
    hgreg (fun y hy => ((tfPotential_harmonic_outside h1 hR hs (haR.trans_le hy)).2).trans
      (hglap y hy).symm) (fun y hy => ?_) (fun ε hε => ?_)
  · have hqm : q = ∫ y, ρ y := by
      apply sub_eq_zero.mp
      apply abs_eq_zero.mp
      apply le_antisymm _ (abs_nonneg _)
      apply le_of_forall_pos_le_add
      intro ε hε
      let A := ∫ y, |ρ y|
      have hA : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
      let S := max a R + 1 + R * A / ε
      have hS : 0 < S := by dsimp [S]; have hh := le_max_left a R; positivity
      have hSa : a ≤ S := by
        dsimp [S]; have hh := le_max_left a R; have ht := div_nonneg (mul_nonneg hR hA) hε.le; linarith
      have hSR : R < S := by
        dsimp [S]; have hh := le_max_right a R; have ht := div_nonneg (mul_nonneg hR hA) hε.le; linarith
      have hSn : ‖S • e‖ = S := by simp [norm_smul, he, abs_of_pos hS]
      have ht := tfPotential_compact_mass_bound h1 hp hR hs (x := S • e) (by simpa only [hSn] using hSR)
      rw [hEq (S • e) (by simpa only [hSn] using hSa), hg, hSn, mul_div_cancel₀ _ hS.ne'] at ht
      apply ht.trans
      have hbound : R * A / ε ≤ S - R := by
        dsimp [S]; have hh := le_max_right a R; linarith
      have hh := (div_le_iff₀ hε).mp hbound
      rw [zero_add, div_mul_eq_mul_div]
      exact (div_le_iff₀ (sub_pos.mpr hSR)).mpr (by linarith)
    rw [hEq x hax, hg, hqm]
  · rw [hg, tfPotential_radial hr y (a • e) (hy.trans hya.symm)]
    dsimp [q]
    rw [hy, mul_div_cancel_left₀ _ ha.ne']
  · obtain ⟨S, hS, hdec⟩ := tfPotential_compact_decay h1 hp hs (ε / 2) (by positivity)
    refine ⟨max S (2 * |q| / ε), ?_⟩
    intro y hy
    have hyS := (le_max_left S (2 * |q| / ε)).trans hy
    have hyn := hS.trans_le hyS
    have hsmall : |q| / ‖y‖ ≤ ε / 2 := by
      have hh := (div_le_iff₀ hε).mp ((le_max_right S (2 * |q| / ε)).trans hy)
      apply (div_le_iff₀ hyn).mpr
      linarith
    have hab : |G y| ≤ ε / 2 := by rw [hg, abs_div, abs_norm]; exact hsmall
    exact (abs_sub _ _).trans (by linarith [hdec y hyS])

lemma tfPotential_harmonic_inside {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    {a R : ℝ} (hR : 0 ≤ R) (hs : ∀ y, ρ y ≠ 0 → a ≤ ‖y‖ ∧ ‖y‖ ≤ R)
    {x : TFSpace} (hx : ‖x‖ < a) :
    ContDiffAt ℝ 2 (tfPotential ρ) x ∧ Δ (tfPotential ρ) x = 0 := by
  apply tfPotential_harmonic_separated h1.locallyIntegrable (sub_pos.mpr hx)
    (show 0 ≤ ‖x‖ + R by positivity)
  intro y hy
  have hb := hs y hy
  have ht := norm_add_le (y - x) x
  rw [sub_add_cancel, norm_sub_rev y x] at ht
  exact ⟨by linarith [hb.1], (norm_sub_le x y).trans (by linarith [hb.2])⟩

theorem tfPotential_newton_interior {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ) {a R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ y, ρ y ≠ 0 → a ≤ ‖y‖ ∧ ‖y‖ ≤ R) {x : TFSpace} (hx : ‖x‖ ≤ a)
    (ha : 0 < a) : tfPotential ρ x = tfPotential ρ 0 := by
  have hinner (z : TFSpace) (hz : ‖z‖ < a) : tfPotential ρ z = tfPotential ρ 0 := by
    let b := (‖z‖ + a) / 2
    have hb : 0 < b := by dsimp [b]; linarith [norm_nonneg z]
    have hba : b < a := by dsimp [b]; linarith
    have hzb : ‖z‖ ≤ b := by dsimp [b]; linarith
    let e : TFSpace := EuclideanSpace.single 0 1
    have he : ‖e‖ = 1 := by simp [e]
    have heb : ‖b • e‖ = b := by simp [norm_smul, he, abs_of_pos hb]
    let c := tfPotential ρ (b • e)
    have hlocal (y : TFSpace) (hy : ‖y‖ ≤ b) :=
      tfPotential_harmonic_inside h1 hR hs (hy.trans_lt hba)
    have hbound (y : TFSpace) (hy : ‖y‖ = b) : tfPotential ρ y = c :=
      tfPotential_radial hr y (b • e) (hy.trans heb.symm)
    have hle (s : ℝ) : ∀ y ∈ closedBall (0 : TFSpace) b,
        s * (tfPotential ρ y - c) ≤ 0 := by
      apply CoulombPDE.compact_maximum_principle (isCompact_closedBall 0 b)
      · exact (continuous_const.mul ((tfPotential_continuous h1 hp).sub continuous_const)).continuousOn
      · intro y hy
        have hyb : ‖y‖ ≤ b := by simpa using (interior_subset hy : y ∈ closedBall 0 b)
        exact contDiffAt_const.mul (hlocal y hyb |>.1.sub contDiffAt_const)
      · intro y hy _
        have hyb : ‖y‖ ≤ b := by simpa using (interior_subset hy : y ∈ closedBall 0 b)
        change 0 ≤ (Δ (s • (tfPotential ρ - fun _ => c)) : TFSpace → ℝ) y
        have hreg : ContDiffAt ℝ 2 (tfPotential ρ - fun _ => c) y :=
          (hlocal y hyb).1.sub contDiffAt_const
        rw [laplacian_smul s hreg,
          (hlocal y hyb).1.laplacian_sub (show ContDiffAt ℝ 2 (fun _ : TFSpace => c) y from contDiffAt_const),
          (hlocal y hyb).2, laplacian_const]
        simp
      · intro y hy hi
        have hyb : ‖y‖ ≤ b := by simpa using hy
        have hyge : b ≤ ‖y‖ := by
          by_contra! hlt
          exact hi (by rw [interior_closedBall 0 hb.ne']; simpa using hlt)
        simp [hbound y (le_antisymm hyb hyge)]
    have hall (y : TFSpace) (hy : ‖y‖ ≤ b) : tfPotential ρ y = c := by
      have hp' := hle 1 y (by simpa using hy)
      have hm' := hle (-1) y (by simpa using hy)
      linarith
    exact (hall z hzb).trans (hall 0 (by simpa using hb.le)).symm
  have heq : EqOn (tfPotential ρ) (fun _ => tfPotential ρ 0) (ball 0 a) :=
    fun y hy => hinner y (by simpa using hy)
  have hh := heq.closure (tfPotential_continuous h1 hp) continuous_const
  rw [closure_ball 0 ha.ne'] at hh
  exact hh (by simpa using hx)

lemma tfPotential_newton_exterior_closed {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ) {R : ℝ} (hR : 0 < R)
    (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R) {x : TFSpace} (hx : R ≤ ‖x‖) :
    tfPotential ρ x = (∫ y, ρ y) / ‖x‖ := by
  have he : EqOn (fun y => tfPotential ρ y * ‖y‖) (fun _ => ∫ y, ρ y)
      (closedBall (0 : TFSpace) R)ᶜ := by
    intro y hy
    have hyr : R < ‖y‖ := by simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hy
    change tfPotential ρ y * ‖y‖ = _
    rw [tfPotential_newton_exterior h1 hp hr hR.le hs hyr,
      div_mul_cancel₀ _ (hR.trans hyr).ne']
  have hclosure := he.closure ((tfPotential_continuous h1 hp).mul continuous_norm) continuous_const
  rw [closure_compl, interior_closedBall 0 hR.ne'] at hclosure
  have hmem : x ∈ (ball (0 : TFSpace) R)ᶜ := by
    simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hx
  exact (eq_div_iff (hR.trans_le hx).ne').mpr (hclosure hmem)

lemma IsRadial.indicator_norm_le {ρ : TFSpace → ℝ} (hr : IsRadial ρ) (r : ℝ) :
    IsRadial ({y | ‖y‖ ≤ r}.indicator ρ) := by
  intro x y hxy
  simp only [Set.indicator, mem_ofPred_eq, hxy, hr x y hxy]

lemma IsRadial.indicator_norm_gt {ρ : TFSpace → ℝ} (hr : IsRadial ρ) (r : ℝ) :
    IsRadial ({y | r < ‖y‖}.indicator ρ) := by
  intro x y hxy
  simp only [Set.indicator, mem_ofPred_eq, hxy, hr x y hxy]

theorem tfPotential_newton {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hp : MemLp ρ (5 / 3))
    (hr : IsRadial ρ) {R : ℝ} (hR : 0 ≤ R) (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R)
    {x : TFSpace} (hx : x ≠ 0) :
    tfPotential ρ x = (∫ y in {y | ‖y‖ ≤ ‖x‖}, ρ y) / ‖x‖ +
      ∫ y in {y | ‖x‖ < ‖y‖}, ρ y / ‖y‖ := by
  let r := ‖x‖
  have hri : 0 < r := norm_pos_iff.mpr hx
  let ρi := {y | ‖y‖ ≤ r}.indicator ρ
  let ρo := {y | r < ‖y‖}.indicator ρ
  have hmi : MeasurableSet {y : TFSpace | ‖y‖ ≤ r} := measurableSet_le measurable_norm measurable_const
  have hmo : MeasurableSet {y : TFSpace | r < ‖y‖} := measurableSet_lt measurable_const measurable_norm
  have hi1 : Integrable ρi := h1.indicator hmi
  have hip : MemLp ρi (5 / 3) := hp.indicator hmi
  have ho1 : Integrable ρo := h1.indicator hmo
  have hop : MemLp ρo (5 / 3) := hp.indicator hmo
  have hsum (y : TFSpace) : ρ y = ρi y + ρo y := by
    dsimp [ρi, ρo]
    by_cases hy : ‖y‖ ≤ r
    · simp [hy, not_lt.mpr hy]
    · simp [hy, lt_of_not_ge hy]
  have hinside := tfPotential_newton_exterior_closed hi1 hip (hr.indicator_norm_le r) hri
    (fun y hy => by by_contra hn; exact hy (by simp [ρi, hn])) (x := x) le_rfl
  have houtside := tfPotential_newton_interior ho1 hop (hr.indicator_norm_gt r) hR
    (fun y hy => by
      have hy' : r < ‖y‖ := by by_contra hn; exact hy (by simp [ρo, hn])
      have hyρ : ρ y ≠ 0 := by simpa [ρo, hy'] using hy
      exact ⟨hy'.le, hs y hyρ⟩) (x := x) le_rfl hri
  have hpot : tfPotential ρ x = tfPotential ρi x + tfPotential ρo x := by
    unfold tfPotential
    rw [← integral_add (tfPotential_integrable hi1 hip x) (tfPotential_integrable ho1 hop x)]
    apply integral_congr_ae (Eventually.of_forall fun y => ?_)
    rw [hsum y, add_div]
  rw [hpot, hinside, houtside]
  congr 1
  · rw [show ρi = {y | ‖y‖ ≤ r}.indicator ρ from rfl, integral_indicator hmi]
  · unfold tfPotential ρo
    simp only [zero_sub, norm_neg]
    rw [← integral_indicator hmo]
    apply integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : r < ‖y‖ <;> simp [hy]

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian

end

end OAI
