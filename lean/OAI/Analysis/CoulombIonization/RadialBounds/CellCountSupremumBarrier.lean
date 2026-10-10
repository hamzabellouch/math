import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.RootMomentCauchyBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators

namespace CoulombAtom

lemma rawCountMoment_le_number {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) (R : ℝ) : rawCountMoment ψ y R ≤ (N:ℝ)^2*formMass ψ := by
  simp only [rawCountMoment,rawFormPair,formMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  rw [←integral_const_mul]
  apply integral_mono
    (rawFormPair_integrable hψ ((rawBallCount_measurable y R).pow_const 2)
      (fun _ => norm_sq_le_of_nonneg (rawBallCount_nonneg _ _ _) (rawBallCount_le _ _ _)) s)
    (((hψ.1 s).norm.integrable_sq).const_mul _)
  intro x
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (rawBallCount_nonneg _ _ _) (rawBallCount_le _ _ _) 2) (sq_nonneg _)

def localCountRatioSet {N : ℕ} (ψ : FormVector N) (D : ℝ) : Set ℝ :=
  {q | ∃ y : Space, y ≠ 0 ∧ q = rawCountMoment ψ y (localCellRadius y)/(localOffsetMass D y)^2}

def localCountSupremum {N : ℕ} (ψ : FormVector N) (D : ℝ) : ℝ :=
  max 1 (sSup (localCountRatioSet ψ D))

lemma localCountRatioSet_nonempty {N : ℕ} (ψ : FormVector N) (D : ℝ) :
    (localCountRatioSet ψ D).Nonempty := by
  obtain ⟨y,hy⟩ := exists_ne (0 : Space)
  exact ⟨_,y,hy,rfl⟩

lemma localCountRatioSet_bddAbove {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) (D : ℝ) :
    BddAbove (localCountRatioSet ψ D) := by
  refine ⟨(N:ℝ)^2*formMass ψ,?_⟩
  rintro q ⟨y,hy,rfl⟩
  have hm := localOffsetMass_one_le D y
  have hm2 : 1 ≤ (localOffsetMass D y)^2 := by nlinarith
  exact (div_le_self (rawCountMoment_nonneg ψ y _) hm2).trans (rawCountMoment_le_number hψ y _)

lemma localCountSupremum_one_le {N : ℕ} (ψ : FormVector N) (D : ℝ) :
    1 ≤ localCountSupremum ψ D := le_max_left _ _

lemma localCountMoment_le_supremum {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (D : ℝ) {y : Space} (hy : y ≠ 0) : rawCountMoment ψ y (localCellRadius y) ≤
      localCountSupremum ψ D*(localOffsetMass D y)^2 := by
  have hm := localOffsetMass_one_le D y
  have hp : 0 < (localOffsetMass D y)^2 := sq_pos_of_pos (by linarith)
  apply (div_le_iff₀ hp).mp
  exact (le_csSup (localCountRatioSet_bddAbove hψ D) (show _ ∈ localCountRatioSet ψ D from ⟨y,hy,rfl⟩)).trans
    (le_max_right _ _)

lemma localCountSupremum_le {N : ℕ} {ψ : FormVector N} (D : ℝ) {C : ℝ}
    (hC : 1 ≤ C) (h : ∀ y : Space, y ≠ 0 →
      rawCountMoment ψ y (localCellRadius y) ≤ C*(localOffsetMass D y)^2) :
    localCountSupremum ψ D ≤ C := by
  apply max_le hC
  apply csSup_le (localCountRatioSet_nonempty ψ D)
  rintro q ⟨y,hy,rfl⟩
  have hm := localOffsetMass_one_le D y
  exact (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < localOffsetMass D y))).mpr (h y hy)

def localCountCoverConstant : ℝ := 1+64*(localCountStencil.card:ℝ)^2
lemma localCountCoverConstant_one_le : 1 ≤ localCountCoverConstant := by
  unfold localCountCoverConstant
  nlinarith [sq_nonneg (localCountStencil.card:ℝ)]

theorem enlarged_cell_count_le {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {D : ℝ} (hD : 0 ≤ D) {y : Space} (hy : y ≠ 0) :
    rawCountMoment ψ y (32*localCellRadius y) ≤
      localCountCoverConstant*localCountSupremum ψ D*(localOffsetMass D y)^2 := by
  classical
  let a := localCellRadius y
  let T := localCountStencil.image (fun v => y+a • v)
  let P := localCountSupremum ψ D
  let m := localOffsetMass D y
  have ha : 0 < a := localCellRadius_pos hy
  have hP : 0 ≤ P := le_trans zero_le_one (localCountSupremum_one_le ψ D)
  have hm : 0 ≤ m := le_trans zero_le_one (localOffsetMass_one_le D y)
  have hcover : ∀ z : Space, ‖z-y‖ < 32*a → ∃ v ∈ T, ‖z-v‖ < localCellRadius v := by
    intro z hz
    obtain ⟨v,hv,hzv⟩ := localCountStencil_scaled_cover hy hz
    exact ⟨y+a • v,Finset.mem_image.mpr ⟨v,hv,rfl⟩,hzv⟩
  have hbound (z : Space) (hz : z ∈ T) :
      rawCountMoment ψ z (localCellRadius z) ≤ 64*P*m^2 := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    have hn := localCountStencil_norm hv
    have hr := (localCellRadius_near hy hn).1
    have hzp : 0 < localCellRadius (y+a • v) := lt_of_lt_of_le (by positivity : 0 < a/2) hr
    have hz0 : y+a • v ≠ 0 := by
      intro hz0
      rw [hz0] at hzp
      simp [localCellRadius] at hzp
    have hmc := localOffsetMass_near hD hy hn
    have hmsq := pow_le_pow_left₀ (le_trans zero_le_one (localOffsetMass_one_le D (y+a • v))) hmc 2
    have hh := (localCountMoment_le_supremum hψ D hz0).trans (mul_le_mul_of_nonneg_left hmsq hP)
    calc _ ≤ P*(8*m)^2 := hh
         _ = 64*P*m^2 := by ring
  have hh := rawCountMoment_le_cover hψ y (32*a) T localCellRadius hcover
  have hs := Finset.sum_le_sum (s := T) (fun z hz => hbound z hz)
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hb := hh.trans (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (T.card:ℝ)))
  have hcard : (T.card:ℝ) ≤ (localCountStencil.card:ℝ) := by
    exact_mod_cast Finset.card_image_le
  have hcardsq := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ T.card) hcard 2
  have hc : (T.card:ℝ)^2 ≤ localCountCoverConstant/64 := by
    unfold localCountCoverConstant
    linarith
  have ht := mul_le_mul_of_nonneg_right hc (show 0 ≤ 64*P*m^2 by positivity)
  change rawCountMoment ψ y (32*a) ≤ localCountCoverConstant*P*m^2
  nlinarith

end CoulombAtom

end

end OAI
