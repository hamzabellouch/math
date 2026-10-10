import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.PuncturedGreenBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombAnalysis
open CoulombPDE

lemma reaction_continuous (d : ℝ) : Continuous (reaction d) := by
  unfold reaction
  exact continuous_const.mul (((continuous_id.sub continuous_const).max continuous_const).rpow_const
    (fun _ => Or.inr (by norm_num)))

lemma radialCombination_continuousOn (B e s c : ℝ) :
    ContinuousOn (radialCombination B e s c) {0}ᶜ :=
  fun _x hx => (radialCombination_contDiffAt B e s c hx).continuousAt.continuousWithinAt

def radialCombinationSource (B e s : ℝ) (x : Space) : ℝ :=
  radialPower (-3) x*(12*B+(12+14*s+4*s^2)*e*radialPower (-s) x)

lemma radialCombinationSource_continuousOn (B e s : ℝ) :
    ContinuousOn (radialCombinationSource B e s) {0}ᶜ := by
  intro x hx
  exact ((radialPower_contDiffAt (-3) hx).continuousAt.mul
    (continuousAt_const.add (continuousAt_const.mul
      (radialPower_contDiffAt (-s) hx).continuousAt))).continuousWithinAt

lemma radialCombination_poisson (B e s c : ℝ) :
    PuncturedPoisson (radialCombination B e s c) (radialCombinationSource B e s) :=
  (PuncturedPoisson.of_classical (fun _x hx => radialCombination_contDiffAt B e s c hx)).congr_source
    (fun _x hx => radialCombination_laplacian B e s c hx)

theorem weak_singular_upper_bound {F : Space → ℝ} {d C R B : ℝ}
    (hd : 0 < d) (hC : 0 ≤ C) (hR : 0 < R) (hB : 0 < B)
    (hq : 12 < d * B ^ (1 / 2 : ℝ))
    (hreg : ContinuousOn F {0}ᶜ)
    (hpde : PuncturedPoisson F (fun x => reaction d (F x)))
    (hupper : ∀ x, x ≠ 0 → ‖x‖ ≤ R → F x ≤ C * radialPower (-2) x) :
    ∀ x, x ≠ 0 → ‖x‖ ≤ R →
      F x ≤ B * radialPower (-2) x + C * (R ^ 2) ^ (-2 : ℝ) + 1 := by
  obtain ⟨s, hs, hκ⟩ := exists_small_exponent hq
  let c : ℝ := C * (R ^ 2) ^ (-2 : ℝ)
  have hc : 0 ≤ c := mul_nonneg hC (Real.rpow_nonneg (sq_nonneg R) _)
  have heBound (e : ℝ) (he : 0 < e) : ∀ x, x ≠ 0 → ‖x‖ ≤ R →
      F x ≤ radialCombination B e s (c + 1) x := by
    have hvc := radialCombination_continuousOn B e s (c+1)
    have hdiff := hpde.sub (radialCombination_poisson B e s (c+1)) hreg hvc
      ((reaction_continuous d).comp_continuousOn hreg) (radialCombinationSource_continuousOn B e s)
    have hm := weak_punctured_ball_maximum (R := R) (u := F-radialCombination B e s (c+1))
      (hreg.sub hvc) (fun g hg hcg hsg hgn => hdiff.nonneg_on
        (fun x hx => hx.1) (fun x hx => ?_) hg hcg hsg hgn) (fun x hx => ?_) ?_
    · intro x hx hr
      exact sub_nonpos.mp (hm x hx hr)
    · change 0 ≤ reaction d (F x)-radialCombinationSource B e s x
      have hu := upper_barrier_laplacian hd.le hB he.le (by linarith : 1 ≤ c+1) hq.le hκ hx.1
      rw [radialCombination_laplacian] at hu
      have hmon := reaction_monotone hd.le (show radialCombination B e s (c+1) x ≤ F x by
        exact le_of_lt (sub_pos.mp hx.2.2))
      change radialCombinationSource B e s x ≤ reaction d (radialCombination B e s (c+1) x) at hu
      linarith
      exact hx.1
    · have hx0 : x ≠ 0 := norm_pos_iff.mp (hx ▸ hR)
      have hu := hupper x hx0 hx.le
      have hrad : C * radialPower (-2) x = c := by simp only [radialPower, hx, c]
      rw [hrad] at hu
      have h1 := radialPower_nonneg (-2 : ℝ) x
      have h2 := radialPower_nonneg (-2 - s) x
      change F x - radialCombination B e s (c + 1) x ≤ 0
      unfold radialCombination
      nlinarith [mul_nonneg hB.le h1, mul_nonneg he.le h2]
    · obtain ⟨a, ha, hsmall⟩ := exists_small_radialPower_bound (E := Space) hs (C / e)
      refine ⟨min a R, lt_min ha hR, ?_⟩
      intro x hx hxa
      have ht := hsmall x hx (hxa.trans (min_le_left _ _))
      have hu := hupper x hx (hxa.trans (min_le_right _ _))
      have heC : C ≤ e * radialPower (-s) x := by
        have ht' := (div_le_iff₀ he).mp ht
        nlinarith
      change F x - radialCombination B e s (c + 1) x ≤ 0
      rw [radialCombination_factor _ _ _ _ hx]
      nlinarith [mul_nonneg (radialPower_nonneg (-2) x) (sub_nonneg.mpr heC),
        mul_nonneg hB.le (radialPower_nonneg (-2) x)]
  intro x hx hr
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hp := radialPower_pos (-2 - s) hx
  have h := heBound (δ / radialPower (-2 - s) x) (div_pos hδ hp) x hx hr
  unfold radialCombination at h
  rw [div_mul_cancel₀ _ hp.ne'] at h
  change F x ≤ B * radialPower (-2) x + c + 1 + δ
  linarith

theorem weak_singular_lower_bound {F : Space → ℝ} {d c₀ R B : ℝ}
    (hd : 0 < d) (hc₀ : 0 < c₀) (hR : 0 < R) (hB : 0 < B)
    (hq : d * B ^ (1 / 2 : ℝ) < 12)
    (hreg : ContinuousOn F {0}ᶜ)
    (hpde : PuncturedPoisson F (fun x => reaction d (F x)))
    (hlower : ∀ x, x ≠ 0 → ‖x‖ ≤ R → c₀ * radialPower (-2) x ≤ F x) :
    ∀ x, x ≠ 0 → ‖x‖ ≤ R →
      B * radialPower (-2) x - B * (R ^ 2) ^ (-2 : ℝ) ≤ F x := by
  let q := d * B ^ (1 / 2 : ℝ)
  have hgap : 0 < (12 - q) * c₀ / B := div_pos (mul_pos (sub_pos.mpr hq) hc₀) hB
  obtain ⟨s, hs, hsκ⟩ := exists_small_exponent (show 12 < 12 + (12 - q) * c₀ / B by linarith)
  have hκ : (14 * s + 4 * s ^ 2) * B ≤ (12 - q) * c₀ := by
    apply (le_div_iff₀ hB).mp
    linarith
  let c : ℝ := B * (R ^ 2) ^ (-2 : ℝ)
  have hc : 0 ≤ c := mul_nonneg hB.le (Real.rpow_nonneg (sq_nonneg R) _)
  have heBound (e : ℝ) (he : 0 < e) : ∀ x, x ≠ 0 → ‖x‖ ≤ R →
      radialCombination B (-e) s (-c) x ≤ F x := by
    have hvc := radialCombination_continuousOn B (-e) s (-c)
    have hdiff := (radialCombination_poisson B (-e) s (-c)).sub hpde hvc hreg
      (radialCombinationSource_continuousOn B (-e) s) ((reaction_continuous d).comp_continuousOn hreg)
    have hm := weak_punctured_ball_maximum (R := R) (u := radialCombination B (-e) s (-c)-F)
      (hvc.sub hreg) (fun g hg hcg hsg hgn => hdiff.nonneg_on
        (fun x hx => hx.1) (fun x hx => ?_) hg hcg hsg hgn) (fun x hx => ?_) ?_
    · intro x hx hr
      exact sub_nonpos.mp (hm x hx hr)
    · change 0 ≤ radialCombinationSource B (-e) s x-reaction d (F x)
      have ht := lower_barrier_laplacian hd.le he.le hs.le hc hc₀ hq.le hκ hx.1
        (hlower x hx.1 hx.2.1) (sub_pos.mp hx.2.2)
      rw [radialCombination_laplacian _ _ _ _ hx.1] at ht
      exact sub_nonneg.mpr ht
    · have hx0 : x ≠ 0 := norm_pos_iff.mp (hx ▸ hR)
      have hl := hlower x hx0 hx.le
      have hrad : B * radialPower (-2) x = c := by simp only [radialPower, hx, c]
      change radialCombination B (-e) s (-c) x - F x ≤ 0
      unfold radialCombination
      rw [hrad]
      nlinarith [mul_nonneg hc₀.le (radialPower_nonneg (-2) x),
        mul_nonneg he.le (radialPower_nonneg (-2 - s) x)]
    · obtain ⟨a, ha, hsmall⟩ := exists_small_radialPower_bound (E := Space) hs (B / e)
      refine ⟨min a R, lt_min ha hR, ?_⟩
      intro x hx hxa
      have ht := hsmall x hx (hxa.trans (min_le_left _ _))
      have hl := hlower x hx (hxa.trans (min_le_right _ _))
      have heB : B ≤ e * radialPower (-s) x := by
        have ht' := (div_le_iff₀ he).mp ht
        nlinarith
      change radialCombination B (-e) s (-c) x - F x ≤ 0
      rw [radialCombination_factor _ _ _ _ hx]
      nlinarith [mul_nonneg (radialPower_nonneg (-2) x) (sub_nonneg.mpr heB),
        mul_nonneg hc₀.le (radialPower_nonneg (-2) x)]
  intro x hx hr
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hp := radialPower_pos (-2 - s) hx
  have h := heBound (δ / radialPower (-2 - s) x) (div_pos hδ hp) x hx hr
  unfold radialCombination at h
  rw [neg_mul, div_mul_cancel₀ _ hp.ne'] at h
  change B * radialPower (-2) x - c ≤ F x + δ
  linarith

end CoulombAnalysis

end

end OAI
