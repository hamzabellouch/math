import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.AnnularCellGeometryBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.CoulombTailStatistic

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter Set
open scoped BigOperators

def tailRadius (h : ℝ) (k : ℕ) : ℝ := (4:ℝ)^k*h
def tailWeight (k : ℕ) : ℝ := (1/2:ℝ)^k
lemma tailRadius_pos {h : ℝ} (hh : 0 < h) (k : ℕ) : 0 < tailRadius h k := by
  unfold tailRadius; positivity
lemma tailWeight_pos (k : ℕ) : 0 < tailWeight k := by unfold tailWeight; positivity
lemma tailRadius_succ (h : ℝ) (k : ℕ) : tailRadius h (k+1) = 4*tailRadius h k := by
  unfold tailRadius; rw [pow_succ]; ring
lemma tailRadius_zero (h : ℝ) : tailRadius h 0 = h := by simp [tailRadius]
lemma tailRadius_mono {h : ℝ} (hh : 0 ≤ h) (k : ℕ) : h ≤ tailRadius h k := by
  exact le_mul_of_one_le_left hh (one_le_pow₀ (by norm_num))
lemma sum_tailWeight_le (K : ℕ) : (∑ k ∈ Finset.range K, tailWeight k) ≤ 2 := by
  have h := geom_sum_mul_neg (x := (1/2:ℝ)) K
  have hp : 0 ≤ (1/2:ℝ)^K := by positivity
  simp only [tailWeight]
  nlinarith

lemma annularOffsetMass_sq_le {D u : ℝ} (hD : 0 ≤ D) (hu : 0 < u) :
    (annularOffsetMass D u)^2 ≤ 3*(1/u^6+1+D*u) := by
  have hs := Real.sq_sqrt (mul_nonneg hD hu.le)
  have hp : 0 ≤ 1/u^3 := by positivity
  have hq : 0 ≤ Real.sqrt (D*u) := Real.sqrt_nonneg _
  have hm : max (1/u^3) 1 ≤ 1/u^3+1 := max_le (by linarith) (by linarith)
  have ht := pow_le_pow_left₀ (by positivity : 0 ≤ max (1/u^3) 1+Real.sqrt (D*u))
    (add_le_add hm le_rfl) 2
  have he : (1/u^3)^2 = 1/u^6 := by ring
  unfold annularOffsetMass
  nlinarith only [ht,hs,he,sq_nonneg (1/u^3-1),sq_nonneg (1/u^3-Real.sqrt (D*u)),
    sq_nonneg (1-Real.sqrt (D*u))]

lemma tailRadius_weight_identity (h : ℝ) (k : ℕ) :
    tailRadius h k*(tailWeight k)^2 = h := by
  unfold tailRadius tailWeight
  have he : (4:ℝ)^k*((1/2:ℝ)^k)^2 = 1 := by
    rw [←pow_mul, Nat.mul_comm k 2, pow_mul, ←mul_pow]
    norm_num
  calc _ = (4^k*((1/2:ℝ)^k)^2)*h := by ring
       _ = h := by rw [he,one_mul]
lemma tailWeight_le_one (k : ℕ) : tailWeight k ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

lemma tail_annular_scale {D h : ℝ} (hD : 0 ≤ D) (hh : 0 < h) (k : ℕ) :
    (1/(tailRadius h k)^6+1+D*tailRadius h k)/((tailRadius h k)^2*tailWeight k) ≤
      tailWeight k*(1/h^8+1/h^2+D/h) := by
  let u := tailRadius h k
  let w := tailWeight k
  have hu : 0 < u := tailRadius_pos hh k
  have hw : 0 < w := tailWeight_pos k
  have hw1 : w ≤ 1 := tailWeight_le_one k
  have he : u*w^2 = h := tailRadius_weight_identity h k
  have huH : h ≤ u := tailRadius_mono hh.le k
  have h1 : 1/u^6 ≤ 1/h^6 := one_div_le_one_div_of_le (pow_pos hh 6)
    (pow_le_pow_left₀ hh.le huH 6)
  have h2 : 1/(u^2*w) ≤ w/h^2 := by
    apply (div_le_iff₀ (by positivity : 0 < u^2*w)).2
    rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hh 2)]
    have hw2 : w^2 ≤ w := by nlinarith
    nlinarith [sq_nonneg (u*w),mul_le_mul_of_nonneg_left hw2 (sq_nonneg u)]
  have h3 : D*u/(u^2*w) = w*(D/h) := by
    rw [←he]
    field_simp
  calc
    _ = (1/u^6+1)/(u^2*w)+D*u/(u^2*w) := by ring
    _ ≤ (1/h^6+1)*(w/h^2)+w*(D/h) := by
      apply add_le_add _ h3.le
      calc _ = (1/u^6+1)*(1/(u^2*w)) := by ring
           _ ≤ _ := mul_le_mul (add_le_add h1 le_rfl) h2 (by positivity) (by positivity)
    _ = _ := by dsimp [w]; field_simp

lemma finite_tail_cauchy (K : ℕ) (b : ℕ → ℝ) :
    (∑ k ∈ Finset.range K, b k)^2 ≤ 2*∑ k ∈ Finset.range K, (b k)^2/tailWeight k := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range K)
    (fun k _ => (tailWeight_pos k).le)
    (fun k _ => div_nonneg (sq_nonneg (b k)) (tailWeight_pos k).le)
    (r := b) (fun k _ => by apply le_of_eq; field_simp [(tailWeight_pos k).ne'])
  exact h.trans (mul_le_mul_of_nonneg_right (sum_tailWeight_le K)
    (Finset.sum_nonneg (fun k _ => div_nonneg (sq_nonneg _) (tailWeight_pos k).le)))

open MeasureTheory Filter Set
open scoped BigOperators
open CoulombObservation CoulombBarrier

def truncatedTailWeight (h : ℝ) (K : ℕ) (a : Space) : ℝ :=
  if h < ‖a‖ ∧ ‖a‖ ≤ tailRadius h K then ‖a‖⁻¹ else 0
lemma truncatedTailWeight_measurable (h : ℝ) (K : ℕ) : Measurable (truncatedTailWeight h K) :=
  continuous_norm.measurable.inv.ite
    ((measurableSet_lt measurable_const continuous_norm.measurable).inter
      (measurableSet_le continuous_norm.measurable measurable_const)) measurable_const
lemma truncatedTailWeight_nonneg (h : ℝ) (K : ℕ) (a : Space) : 0 ≤ truncatedTailWeight h K a := by
  unfold truncatedTailWeight; split_ifs <;> positivity
lemma truncatedTailWeight_le (h : ℝ) (K : ℕ) (a : Space) :
    truncatedTailWeight h K a ≤ coulombTailWeight h a := by
  unfold truncatedTailWeight coulombTailWeight
  split_ifs <;> first | positivity | (expose_names; tauto)
lemma truncatedTailWeight_zero (h : ℝ) (a : Space) : truncatedTailWeight h 0 a = 0 := by
  simp only [truncatedTailWeight,tailRadius_zero]
  rw [ite_eq_right (by intro hc; exact (not_le.mpr hc.1) hc.2)]
lemma truncatedTailWeight_step {h : ℝ} (hh : 0 < h) (K : ℕ) (a : Space) :
    truncatedTailWeight h (K+1) a ≤ truncatedTailWeight h K a+
      (if tailRadius h K ≤ ‖a‖ ∧ ‖a‖ ≤ 4*tailRadius h K then 1 else 0)/tailRadius h K := by
  have hu := tailRadius_pos hh K
  by_cases hi : ‖a‖ ≤ tailRadius h K
  · have hle : truncatedTailWeight h (K+1) a = truncatedTailWeight h K a := by
      unfold truncatedTailWeight
      rw [tailRadius_succ]
      have hupper : ‖a‖ ≤ 4*tailRadius h K := by linarith
      simp only [hi,hupper,and_true]
    rw [hle]
    have hb : 0 ≤ (if tailRadius h K ≤ ‖a‖ ∧ ‖a‖ ≤ 4*tailRadius h K then (1:ℝ) else 0)/tailRadius h K := by
      split_ifs <;> positivity
    linarith
  · have hlo : tailRadius h K ≤ ‖a‖ := (lt_of_not_ge hi).le
    have hz : truncatedTailWeight h K a = 0 := by
      unfold truncatedTailWeight
      exact ite_eq_right (by intro hc; exact hi hc.2)
    rw [hz,zero_add]
    unfold truncatedTailWeight
    rw [tailRadius_succ]
    split_ifs with hj hk hk
    · simpa only [one_div] using inv_anti₀ hu hlo
    · exact False.elim (hk ⟨hlo,hj.2⟩)
    · positivity
    · norm_num

lemma raw_truncated_tail_le_shells {N : ℕ} {h : ℝ} (hh : 0 < h) (K : ℕ)
    (x : Configuration N) :
    rawWeightedCount (truncatedTailWeight h K) x ≤
      ∑ k ∈ Finset.range K, rawAnnularCount (tailRadius h k) (4*tailRadius h k) x/tailRadius h k := by
  induction K with
  | zero => simp [rawWeightedCount,truncatedTailWeight_zero]
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hh' := Finset.sum_le_sum (s := Finset.univ)
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => truncatedTailWeight_step hh K (x i))
    simp only [Finset.sum_add_distrib,←Finset.sum_div] at hh'
    exact hh'.trans (add_le_add ih le_rfl)

lemma truncatedTailWeight_tendsto {h : ℝ} (hh : 0 < h) (a : Space) :
    Tendsto (fun K => truncatedTailWeight h K a) atTop (nhds (coulombTailWeight h a)) := by
  have ht : Tendsto (tailRadius h) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<4)).atTop_mul_const hh
  have hev : ∀ᶠ K in atTop, ‖a‖ ≤ tailRadius h K := (tendsto_atTop.1 ht) ‖a‖
  apply tendsto_const_nhds.congr'
  filter_upwards [hev] with K hK
  simp only [truncatedTailWeight,coulombTailWeight,hK,and_true]

lemma raw_truncated_tail_tendsto {N : ℕ} {h : ℝ} (hh : 0 < h) (x : Configuration N) :
    Tendsto (fun K => rawWeightedCount (truncatedTailWeight h K) x) atTop
      (nhds (rawWeightedCount (coulombTailWeight h) x)) := by
  exact tendsto_finsetSum _ (fun i _ => truncatedTailWeight_tendsto hh (x i))

lemma rawWeightedCount_sq_integrable {N : ℕ} {f : Space → ℝ}
    (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) {A : ℝ} (hb : ∀ z, f z ≤ A)
    (mu : Measure (Configuration N)) [IsFiniteMeasure mu] :
    Integrable (fun x => rawWeightedCount f x^2) mu := by
  apply (integrable_const (((N:ℝ)*A)^2)).mono'
    ((rawWeightedCount_measurable hm).pow_const 2).aestronglyMeasurable
  exact ae_of_all _ (fun x => norm_sq_le_of_nonneg (rawWeightedCount_nonneg hn x) (rawWeightedCount_le hb x))

lemma truncated_tail_moment_tendsto {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevVector psi) {h : ℝ} (hh : 0 < h) :
    Tendsto (fun K => rawWeightedMoment psi (truncatedTailWeight h K)) atTop
      (nhds (rawWeightedMoment psi (coulombTailWeight h))) := by
  let : IsFiniteMeasure (formRawLaw psi) := formRawLaw_finite hpsi
  have hb (K : ℕ) (a : Space) : truncatedTailWeight h K a ≤ 1/h :=
    (truncatedTailWeight_le h K a).trans (coulombTailWeight_le hh a)
  simp_rw [rawWeightedMoment_eq_integral hpsi (truncatedTailWeight_measurable h _)
    (truncatedTailWeight_nonneg h _) (hb _)]
  rw [rawWeightedMoment_eq_integral hpsi (coulombTailWeight_measurable h)
    (coulombTailWeight_nonneg h) (coulombTailWeight_le hh)]
  apply tendsto_integral_of_dominated_convergence (fun _ => ((N:ℝ)/h)^2)
    (fun K => ((rawWeightedCount_measurable (truncatedTailWeight_measurable h K)).pow_const 2).aestronglyMeasurable)
    (integrable_const _)
    (fun K => ae_of_all _ (fun x => ?_))
    (ae_of_all _ (fun x => (raw_truncated_tail_tendsto hh x).pow 2))
  convert norm_sq_le_of_nonneg (rawWeightedCount_nonneg (truncatedTailWeight_nonneg h K) x)
    (rawWeightedCount_le (hb K) x) using 1
  ring

end CoulombAtom

end

end OAI
