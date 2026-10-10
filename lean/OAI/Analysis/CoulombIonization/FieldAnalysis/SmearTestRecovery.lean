import Mathlib
import OAI.Analysis.CoulombIonization.Localization.CutOuterLaw

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators NNReal

namespace CoulombNeumann
open CoulombAtom CoulombAnalysis

lemma varthetaScaled_test_bound {b : ℝ} (hb : 0 < b) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (x z : Space) :
    ‖g z*varthetaScaled b (z-x)‖ ≤
      (‖g x‖+(L:ℝ)*(Real.sqrt 3*b))*varthetaScaled b (z-x) := by
  by_cases he : varthetaScaled b (z-x) = 0
  · simp [he]
  have hd : ‖z-x‖ ≤ Real.sqrt 3*b := by
    by_contra h
    exact he (varthetaScaled_support hb _ (le_of_not_ge h))
  have hl := hg.dist_le_mul z x
  rw [dist_eq_norm,dist_eq_norm] at hl
  have ht : ‖g z‖ ≤ ‖g x‖+(L:ℝ)*(Real.sqrt 3*b) :=
    calc
      ‖g z‖ ≤ ‖g x‖+‖g z-g x‖ := by simpa only [add_sub_cancel] using norm_add_le (g x) (g z-g x)
      _ ≤ _ := add_le_add_right (hl.trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)) _
  rw [norm_mul,Real.norm_of_nonneg (varthetaScaled_nonneg hb _)]
  exact mul_le_mul_of_nonneg_right ht (varthetaScaled_nonneg hb _)

lemma varthetaScaled_test_integrable {b : ℝ} (hb : 0 < b) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (x : Space) :
    Integrable (fun z => g z*varthetaScaled b (z-x)) := by
  apply (((varthetaScaled_integrable hb).comp_sub_right x).const_mul
    (‖g x‖+(L:ℝ)*(Real.sqrt 3*b))).mono'
    (hg.continuous.aestronglyMeasurable.mul
      (((varthetaScaled_measurable b).comp (measurable_id.sub_const x)).aestronglyMeasurable))
  exact Eventually.of_forall (varthetaScaled_test_bound hb hg x)

theorem varthetaScaled_test_error {b : ℝ} (hb : 0 < b) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (x : Space) :
    ‖(∫ z, g z*varthetaScaled b (z-x))-g x‖ ≤ (L:ℝ)*(Real.sqrt 3*b) := by
  have hi := (varthetaScaled_integrable hb).comp_sub_right x
  have hm : (∫ z, varthetaScaled b (z-x)) = 1 := by
    rw [integral_sub_right_eq_self,integral_varthetaScaled hb]
  have he : (∫ z, g z*varthetaScaled b (z-x))-g x =
      ∫ z, (g z-g x)*varthetaScaled b (z-x) := by
    simp only [sub_mul]
    rw [integral_sub (varthetaScaled_test_integrable hb hg x) (hi.const_mul _),
      integral_const_mul,hm,mul_one]
  rw [he]
  calc
    _ ≤ ∫ z, ((L:ℝ)*(Real.sqrt 3*b))*varthetaScaled b (z-x) :=
      norm_integral_le_of_norm_le (hi.const_mul _) (Eventually.of_forall fun z => by
        by_cases he : varthetaScaled b (z-x) = 0
        · simp [he]
        have hd : ‖z-x‖ ≤ Real.sqrt 3*b := by
          by_contra h
          exact he (varthetaScaled_support hb _ (le_of_not_ge h))
        rw [norm_mul,Real.norm_of_nonneg (varthetaScaled_nonneg hb _)]
        have hl := hg.dist_le_mul z x
        rw [dist_eq_norm,dist_eq_norm] at hl
        exact mul_le_mul_of_nonneg_right
          (hl.trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)) (varthetaScaled_nonneg hb _))
    _ = _ := by rw [integral_const_mul,hm,mul_one]

lemma retainedSmear_test_integrable {N : ℕ} {b : ℝ} (hb : 0 < b)
    (S : Finset (Fin N)) (x : Configuration N) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) : Integrable (fun z => g z*retainedSmear b S x z) := by
  simp only [retainedSmear,Finset.mul_sum]
  exact integrable_finsetSum _ (fun i _ => varthetaScaled_test_integrable hb hg (x i))

lemma integral_retainedSmear_test {N : ℕ} {b : ℝ} (hb : 0 < b)
    (S : Finset (Fin N)) (x : Configuration N) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) :
    (∫ z, g z*retainedSmear b S x z) = ∑ i ∈ S, ∫ z, g z*varthetaScaled b (z-x i) := by
  simp only [retainedSmear,Finset.mul_sum]
  exact integral_finsetSum _ (fun i _ => varthetaScaled_test_integrable hb hg (x i))

theorem retainedSmear_test_error {N : ℕ} {b : ℝ} (hb : 0 < b)
    (S : Finset (Fin N)) (x : Configuration N) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) :
    ‖(∫ z, g z*retainedSmear b S x z)-(∑ i ∈ S, g (x i))‖ ≤
      (S.card:ℝ)*((L:ℝ)*(Real.sqrt 3*b)) := by
  rw [integral_retainedSmear_test hb S x hg,←Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum
    (fun i _ => varthetaScaled_test_error hb hg (x i))).trans_eq (by simp))

theorem retainedPatch_test_error {N : ℕ} {b R : ℝ} (hb : 0 < b)
    (S : Finset (Fin N)) (x : Configuration N) (y : Space)
    (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R)
    {g : Space → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g) :
    ‖(∫ z, g (y+z)*retainedPatchLp hb S x y R z ∂ballMeasure R)-
      (∑ i ∈ S, g (x i))‖ ≤ (S.card:ℝ)*((L:ℝ)*(Real.sqrt 3*b)) := by
  rw [retainedPatchLp_field hb S x y hmargin]
  exact retainedSmear_test_error hb S x hg

end CoulombNeumann

open MeasureTheory Filter Set Metric
open scoped BigOperators NNReal

namespace CoulombNeumann
open CoulombAtom CoulombAnalysis

lemma varthetaScaled_test_zero_of_far {b r : ℝ} (hb : 0 < b)
    {g : Space → ℝ} {y x : Space}
    (hs : Function.support g ⊆ closedBall y r)
    (hx : r+Real.sqrt 3*b < ‖x-y‖) :
    (∀ z, g z*varthetaScaled b (z-x) = 0) ∧ g x = 0 := by
  have hb0 : 0 ≤ Real.sqrt 3*b := by positivity
  constructor
  · intro z
    by_cases hg : g z = 0
    · simp [hg]
    by_cases he : varthetaScaled b (z-x) = 0
    · simp [he]
    have hz : ‖z-y‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hs hg
    have hd : ‖z-x‖ ≤ Real.sqrt 3*b := by
      by_contra h
      exact he (varthetaScaled_support hb _ (le_of_not_ge h))
    have ht := dist_triangle x z y
    simp only [dist_eq_norm] at ht
    rw [norm_sub_rev x z] at ht
    exfalso; linarith
  · by_contra hg
    have hz : ‖x-y‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hs hg
    linarith

theorem retainedSmear_local_test_error {N : ℕ} {b r : ℝ} (hb : 0 < b)
    (S : Finset (Fin N)) (x : Configuration N) (y : Space)
    {g : Space → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hs : Function.support g ⊆ closedBall y r) :
    ‖(∫ z, g z*retainedSmear b S x z)-(∑ i ∈ S, g (x i))‖ ≤
      ((S.filter (fun i => ‖x i-y‖ ≤ r+Real.sqrt 3*b)).card:ℝ)*
        ((L:ℝ)*(Real.sqrt 3*b)) := by
  classical
  rw [integral_retainedSmear_test hb S x hg,←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i ∈ S, if ‖x i-y‖ ≤ r+Real.sqrt 3*b then (L:ℝ)*(Real.sqrt 3*b) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · exact varthetaScaled_test_error hb hg (x i)
      · obtain ⟨hz,hg0⟩ := varthetaScaled_test_zero_of_far hb hs (lt_of_not_ge hi)
        simp only [hz,integral_zero,hg0,sub_zero,norm_zero,le_refl]
    _ = _ := by rw [←Finset.sum_filter]; simp

end CoulombNeumann
namespace CoulombAtom
open CoulombNeumann CoulombAnalysis

lemma radialCut_core_distance {N : ℕ} (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (c : Fin N → Fin 2) (x : Configuration N)
    (hx : (spatialProduct (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) c).value x ≠ 0)
    (i : Fin N) (hi : c i = 0) : t ≤ ‖x i-y‖ := by
  classical
  change (∏ j, (coreFirstRadialCut y ht hb (c j)).value (x j)) ≠ 0 at hx
  have hf := (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)
  by_contra hn
  apply hf
  rw [hi]
  exact coreFirstRadialCut_core_zero y ht hb (x i) hn

theorem radialCut_retained_test_eq_raw {N : ℕ} (y : Space) {t b r : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hr : r < t-7*b)
    (c : Fin N → Fin 2) (x : Configuration N)
    (hx : (spatialProduct (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) c).value x ≠ 0)
    (s : Spins (cutOutNumber c)) {g : Space → ℝ}
    (hs : Function.support g ⊆ closedBall y r) :
    (∑ i ∈ radialPatchRetention N y t b c s (cutOutPositions c x),
      g (cutOutPositions c x i)) = ∑ i, g (x i) := by
  classical
  have he : (∑ i ∈ radialPatchRetention N y t b c s (cutOutPositions c x),
      g (cutOutPositions c x i)) = ∑ i, g (cutOutPositions c x i) := by
    unfold radialPatchRetention
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · rfl
    · symm
      apply Function.notMem_support.mp
      intro hg
      have hd : ‖cutOutPositions c x i-y‖ ≤ r := by
        simpa only [mem_closedBall,dist_eq_norm] using hs hg
      exact hi (hd.trans_lt hr)
  rw [he,sum_cutOutPositions]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · rfl
  · symm
    apply Function.notMem_support.mp
    intro hg
    have hd : ‖x i-y‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hs hg
    have hc := radialCut_core_distance y ht hb c x hx i (not_ne_iff.mp hi)
    linarith

theorem radialCut_local_smear_error {N : ℕ} (y : Space) {t b r : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hr : r < t-7*b)
    (c : Fin N → Fin 2) (x : Configuration N)
    (hx : (spatialProduct (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) c).value x ≠ 0)
    (s : Spins (cutOutNumber c)) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (hs : Function.support g ⊆ closedBall y r) :
    let u := cutOutPositions c x
    let S := radialPatchRetention N y t b c s u
    ‖(∫ z, g z*retainedSmear b S u z)-(∑ i, g (x i))‖ ≤
      ((S.filter (fun i => ‖u i-y‖ ≤ r+Real.sqrt 3*b)).card:ℝ)*
        ((L:ℝ)*(Real.sqrt 3*b)) := by
  dsimp only
  rw [←radialCut_retained_test_eq_raw y ht hb hr c x hx s hs]
  exact retainedSmear_local_test_error hb _ _ y hg hs

end CoulombAtom

end

end OAI
