import Mathlib
import OAI.Analysis.CoulombIonization.Localization.CutOuterLaw
import OAI.Analysis.CoulombIonization.ThomasFermi.CutMomentBounds

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombAtom

lemma bounded_probability_first_le_second {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Measurable f)
    (hn : ∀ x, 0 ≤ f x) {C : ℝ} (hC : ∀ x, f x ≤ C) :
    (∫ x, f x ∂μ) ≤ (∫ x, f x^2 ∂μ)^(1/2:ℝ) := by
  have hm : MemLp f (ENNReal.ofReal 2) μ :=
    MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (hn x)]; exact hC x))
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
    (Real.holderConjugate_iff.mpr ⟨by norm_num,by norm_num⟩)
    (ae_of_all μ hn) (ae_of_all μ (fun _ => (by norm_num : (0:ℝ) ≤ 1))) hm
    (memLp_const (1:ℝ))
  simpa only [mul_one,Real.rpow_two,one_pow,integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,
    smul_eq_mul,Real.one_rpow] using hh

lemma weightedParticleCount_eq_rawLaw {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {w : Space → ℝ} (hw : Measurable w) {B : ℝ} (hB : ∀ x, ‖w x‖ ≤ B) :
    weightedParticleCount ψ w = ∫ x, (∑ i, w (x i)) ∂formRawLaw ψ := by
  have hm : Measurable (fun x : Configuration N => ∑ i, w (x i)) :=
    Finset.measurable_sum _ (fun i _ => hw.comp (measurable_pi_apply i))
  have hbnd (x : Configuration N) : ‖∑ i, w (x i)‖ ≤ N*B := by
    calc
      _ ≤ ∑ i, ‖w (x i)‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin N, B := Finset.sum_le_sum (fun i _ => hB (x i))
      _ = N*B := by simp
  rw [formRawLaw_integral_eq_spin_sum hψ hm hbnd]
  apply Finset.sum_congr rfl; intro s _
  simp only [Finset.sum_mul]
  exact (integral_finsetSum _ (fun i _ => weightedParticleCount_integrable hψ hw hB s i)).symm

lemma collar_count_le_strip_first {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (hb : 0 ≤ b) :
    weightedParticleCount ψ (fun z => if t ≤ ‖z-y‖ ∧ ‖z-y‖ ≤ t+b then 1 else 0) ≤
      ∫ x, rawStripCount y t b x ∂formRawLaw ψ := by
  let w : Space → ℝ := fun z => if t ≤ ‖z-y‖ ∧ ‖z-y‖ ≤ t+b then 1 else 0
  have hw : Measurable w := measurable_const.ite
    (((isClosed_le continuous_const ((continuous_id.sub continuous_const).norm)).inter
      (isClosed_le ((continuous_id.sub continuous_const).norm) continuous_const)).measurableSet)
    measurable_const
  have hB : ∀ x, ‖w x‖ ≤ 1 := by intro x; unfold w; split_ifs <;> norm_num
  change weightedParticleCount ψ w ≤ _
  rw [weightedParticleCount_eq_rawLaw hψ hw hB]
  have := formRawLaw_finite hψ
  have hi : Integrable (fun x : Configuration N => ∑ i, w (x i)) (formRawLaw ψ) := by
    apply Integrable.of_bound (Finset.measurable_sum _ (fun i _ => hw.comp (measurable_pi_apply i))).aestronglyMeasurable (N:ℝ)
    apply ae_of_all; intro x
    calc
      _ ≤ ∑ i, ‖w (x i)‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => hB (x i))
      _ = N := by simp
  have hj : Integrable (rawStripCount (N := N) y t b) (formRawLaw ψ) :=
    Integrable.of_bound (rawStripCount_measurable y t b).aestronglyMeasurable (N:ℝ)
      (ae_of_all _ (fun x => by
        rw [Real.norm_of_nonneg (rawStripCount_nonneg y t b x)]
        exact rawStripCount_le y t b x))
  apply integral_mono hi hj
  intro x
  rw [rawStripCount,CoulombRadialAveraging.slidingCount]
  apply Finset.sum_le_sum; intro i _
  unfold w CoulombRadialAveraging.slidingBit
  split_ifs with h1 h2 h2
  · norm_num
  · exfalso
    apply h2
    constructor <;> linarith [h1.1,h1.2]
  · norm_num
  · norm_num

theorem radial_fresh_selected_counts {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (hm : formMass ψ = 1) (y : Space) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    ∃ t ∈ Icc (5*a) (6*a), ∃ ht : 0 ≤ t,
      let p := coreFirstRadialCut y ht hb
      let hp := coreFirstRadialCut_partition y ht hb
      let B := ∫ x, rawBallCount y (7*a) x^2 ∂formRawLaw ψ
      (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        outerDeletedCount y t b u^2*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) ≤ (8*b/a)*B ∧
      (∑ c : Fin N → Fin 2, (cutOutNumber c:ℝ)*formMass (orderedCutForm p hp ψ c)) ≤ B^(1/2:ℝ) ∧
      (∑ c : Fin N → Fin 2, ((cutOutNumber c:ℝ)^(4/3:ℝ)+(cutOutNumber c:ℝ))*
        formMass (orderedCutForm p hp ψ c)) ≤ B^(2/3:ℝ)+B^(1/2:ℝ) ∧
      (1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight p) ≤
        (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2*((8*b/a)*B)^(1/2:ℝ) := by
  obtain ⟨t,ht,hdel⟩ := radial_raw_radius_selection hψ y ha hb.le hba
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hout := radialCut_out_lower_moments hψ hm y ht0 hb (R := 7*a) (by linarith [ht.2])
  refine ⟨t,ht,ht0,?_,hout.1,hout.2,?_⟩
  · rw [outerDeleted_second_moment_eq_cut _ _ hψ]
    exact (radialCut_deleted_second_moment hψ y ht0 hb).trans hdel
  · have := formRawLaw_probability hψ hm
    have hfirst := bounded_probability_first_le_second (formRawLaw ψ)
      (rawStripCount_measurable y t b) (rawStripCount_nonneg y t b) (rawStripCount_le y t b)
    have hh := (collar_count_le_strip_first hψ y hb.le).trans hfirst
    have hbnd := Real.rpow_le_rpow (integral_nonneg (fun x => sq_nonneg (rawStripCount y t b x))) hdel
      (by norm_num : (0:ℝ) ≤ 1/2)
    exact (radial_fresh_ims_bound hψ y ht0 hb).trans
      (mul_le_mul_of_nonneg_left (hh.trans hbnd) (by positivity))

end CoulombAtom

end

end OAI
