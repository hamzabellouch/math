import Mathlib

namespace OAI

/-! Stein Metric. -/

noncomputable section

open Set Filter

open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace CrouzeixHilbert.Metric

section StablePowers

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem eventually_norm_pow_le (a : A) (ha : spectralRadius ℂ a < 1)
    {r : ℝ} (hr : (spectralRadius ℂ a).toReal < r) :
    ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ r ^ n := by
  have ht : spectralRadius ℂ a ≠ ∞ := ne_of_lt (ha.trans (by simp))
  have hl : Tendsto (fun n : ℕ => ‖a ^ n‖ ^ (1 / (n : ℝ))) atTop
      (𝓝 (spectralRadius ℂ a).toReal) := by
    simpa only [Function.comp_def,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] using
      (ENNReal.tendsto_toReal ht).comp
        (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a)
  filter_upwards [hl.eventually (gt_mem_nhds hr), eventually_gt_atTop (0 : ℕ)]
    with n hn hn0
  have h := pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg (a ^ n)) _) hn.le n
  simpa only [one_div, Real.rpow_inv_natCast_pow (norm_nonneg (a ^ n))
    (Nat.ne_of_gt hn0)] using h

theorem summable_norm_pow (a : A) (ha : spectralRadius ℂ a < 1) :
    Summable (fun n : ℕ => ‖a ^ n‖) := by
  have ht : spectralRadius ℂ a ≠ ∞ := ne_of_lt (ha.trans (by simp))
  have hlt : (spectralRadius ℂ a).toReal < 1 := by
    exact (ENNReal.toReal_lt_toReal ht (by simp)).mpr ha
  obtain ⟨r, hr, hr1⟩ := exists_between hlt
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg.trans hr.le
  apply (summable_geometric_of_lt_one hr0 hr1).of_norm_bounded_eventually
  simpa only [Real.norm_of_nonneg (norm_nonneg _), Nat.cofinite_eq_atTop] using
    eventually_norm_pow_le a ha hr

end StablePowers

section Stein

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def steinSeries (T : A) : A := ∑' j : ℕ, star (T ^ j) * T ^ j

omit [PartialOrder A] [StarOrderedRing A] in
theorem summable_steinSeries (T : A) (hT : spectralRadius ℂ T < 1) :
    Summable (fun j : ℕ => star (T ^ j) * T ^ j) := by
  have hs := summable_norm_pow T hT
  have hsmall : ∀ᶠ j in atTop, ‖T ^ j‖ ≤ 1 := by
    exact (hs.tendsto_atTop_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun j hj => hj.le)
  apply hs.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hsmall] with j hj
  calc
    ‖star (T ^ j) * T ^ j‖ ≤ ‖star (T ^ j)‖ * ‖T ^ j‖ := norm_mul_le _ _
    _ = ‖T ^ j‖ * ‖T ^ j‖ := by rw [norm_star]
    _ ≤ ‖T ^ j‖ * 1 := mul_le_mul_of_nonneg_left hj (norm_nonneg _)
    _ = ‖T ^ j‖ := mul_one _

theorem steinSeries_nonneg (T : A) : 0 ≤ steinSeries T :=
  tsum_nonneg (fun _ => star_mul_self_nonneg _)

omit [PartialOrder A] [StarOrderedRing A] in
theorem steinSeries_eq_one_add (T : A) (hT : spectralRadius ℂ T < 1) :
    steinSeries T = 1 + star T * steinSeries T * T := by
  have hs := summable_steinSeries T hT
  have he : (fun j : ℕ => star (T ^ (j + 1)) * T ^ (j + 1)) =
      (fun j : ℕ => star T * (star (T ^ j) * T ^ j) * T) := by
    funext j
    rw [pow_succ, star_mul]
    simp only [mul_assoc]
  have hz := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, pow_zero, star_one, mul_one] at hz
  rw [he, (hs.mul_left (star T)).tsum_mul_right T, hs.tsum_mul_left (star T)] at hz
  exact hz.symm

theorem one_le_steinSeries (T : A) (hT : spectralRadius ℂ T < 1) :
    1 ≤ steinSeries T := by
  rw [steinSeries_eq_one_add T hT]
  exact le_add_of_nonneg_right (star_left_conjugate_nonneg (steinSeries_nonneg T) T)

omit [PartialOrder A] [StarOrderedRing A] in
theorem steinSeries_sub (T : A) (hT : spectralRadius ℂ T < 1) :
    steinSeries T - star T * steinSeries T * T = 1 := by
  nth_rw 1 [steinSeries_eq_one_add T hT]
  exact add_sub_cancel_right _ _

theorem exists_strict_stein_metric (T : A) (hT : spectralRadius ℂ T < 1) :
    ∃ (τ : ℝ) (H : A), IsStrictlyPositive (H - 1) ∧
      IsStrictlyPositive (algebraMap ℝ A τ - H) ∧
      IsStrictlyPositive (H - star T * H * T) := by
  let H := steinSeries T + steinSeries T
  have h0 := one_le_steinSeries T hT
  have h1 : (1 : A) ≤ H - 1 := by
    exact le_sub_iff_add_le.mpr (add_le_add h0 h0)
  have hH : 0 ≤ H := add_nonneg (steinSeries_nonneg T) (steinSeries_nonneg T)
  have hu : H ≤ algebraMap ℝ A ‖H‖ :=
    (CStarAlgebra.norm_le_iff_le_algebraMap H (norm_nonneg _) hH).mp le_rfl
  have hupper : (1 : A) ≤ algebraMap ℝ A (‖H‖ + 1) - H := by
    rw [map_add, map_one]
    exact le_sub_iff_add_le.mpr (by simpa only [add_comm] using add_le_add_right hu 1)
  have hslack : H - star T * H * T = (1 : A) + 1 := by
    dsimp only [H]
    rw [mul_add, add_mul, add_sub_add_comm, steinSeries_sub T hT]
  refine ⟨‖H‖ + 1, H, isStrictlyPositive_one.of_le h1,
    isStrictlyPositive_one.of_le hupper, ?_⟩
  rw [hslack]
  exact isStrictlyPositive_one.add_nonneg zero_le_one

end Stein

section Minimization

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

structure Feasible (T : A) (τ : ℝ) (H : A) : Prop where
  lower : 1 ≤ H
  upper : H ≤ algebraMap ℝ A τ
  stein : star T * H * T ≤ H

theorem Feasible.nonneg {T H : A} {τ : ℝ} (h : Feasible T τ H) : 0 ≤ H :=
  zero_le_one.trans h.lower

theorem Feasible.selfAdjoint {T H : A} {τ : ℝ} (h : Feasible T τ H) :
    IsSelfAdjoint H := .of_nonneg h.nonneg

theorem Feasible.isStrictlyPositive {T H : A} {τ : ℝ} (h : Feasible T τ H) :
    IsStrictlyPositive H := isStrictlyPositive_one.of_le h.lower

variable [Nontrivial A]

theorem Feasible.one_le {T H : A} {τ : ℝ} (h : Feasible T τ H) : 1 ≤ τ := by
  have he : algebraMap ℝ A 1 ≤ algebraMap ℝ A τ := by simpa using h.lower.trans h.upper
  exact algebraMap_le_algebraMap.mp he

theorem Feasible.norm_le {T H : A} {τ : ℝ} (h : Feasible T τ H) : ‖H‖ ≤ τ :=
  (CStarAlgebra.norm_le_iff_le_algebraMap H (zero_le_one.trans h.one_le) h.nonneg).mpr h.upper

omit [Nontrivial A] in
theorem steinSeries_feasible (T : A) (hT : spectralRadius ℂ T < 1) :
    Feasible T ‖steinSeries T‖ (steinSeries T) := by
  refine ⟨one_le_steinSeries T hT, ?_, ?_⟩
  · exact (CStarAlgebra.norm_le_iff_le_algebraMap _ (norm_nonneg _)
      (steinSeries_nonneg T)).mp le_rfl
  · exact sub_nonneg.mp (by rw [steinSeries_sub T hT]; exact zero_le_one)

theorem exists_minimizing_metric [FiniteDimensional ℂ A]
    (T : A) (hT : spectralRadius ℂ T < 1) :
    ∃ (τ : ℝ) (H : A), Feasible T τ H ∧ 1 ≤ τ ∧
      ∀ (τ' : ℝ) (H' : A), Feasible T τ' H' → τ ≤ τ' := by
  let : ProperSpace A := FiniteDimensional.proper ℂ A
  let H₀ := steinSeries T
  have h₀ := steinSeries_feasible T hT
  let M : Set A := {H | 1 ≤ H ∧ star T * H * T ≤ H}
  have hMc : IsClosed M := (isClosed_le continuous_const continuous_id).inter
    (isClosed_le ((continuous_const.mul continuous_id).mul continuous_const) continuous_id)
  let K := Metric.closedBall (0 : A) ‖H₀‖ ∩ M
  have hKc : IsCompact K := (isCompact_closedBall (0 : A) ‖H₀‖).inter_right hMc
  have hKne : K.Nonempty := by
    refine ⟨H₀, ?_⟩
    simp only [K, mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
    exact ⟨le_rfl, h₀.lower, h₀.stein⟩
  obtain ⟨H, hHK, hmin⟩ := hKc.exists_isMinOn hKne continuous_norm.continuousOn
  have hH0 : 0 ≤ H := zero_le_one.trans hHK.2.1
  refine ⟨‖H‖, H, ⟨hHK.2.1, ?_, hHK.2.2⟩, ?_, ?_⟩
  · exact (CStarAlgebra.norm_le_iff_le_algebraMap H (norm_nonneg H) hH0).mp le_rfl
  · have h : ‖(1 : A)‖ ≤ ‖H‖ :=
      CStarAlgebra.norm_le_norm_of_le_of_nonneg hHK.2.1 zero_le_one
    simpa only [norm_one] using h
  · intro τ' H' hH'
    by_cases hb : ‖H'‖ ≤ ‖H₀‖
    · have h'K : H' ∈ K := ⟨by simpa using hb, hH'.lower, hH'.stein⟩
      exact (hmin h'K).trans hH'.norm_le
    · have hbound : ‖H‖ ≤ ‖H₀‖ := by simpa using hHK.1
      exact (hbound.trans (le_of_not_ge hb)).trans hH'.norm_le

end Minimization

section Similarity

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem norm_le_one_iff_star_mul_self_le (a : A) :
    ‖a‖ ≤ 1 ↔ star a * a ≤ 1 := by
  rw [← CStarAlgebra.norm_le_one_iff_of_nonneg (star a * a)
    (star_mul_self_nonneg a), CStarRing.norm_star_mul_self]
  constructor <;> intro h <;> nlinarith [norm_nonneg a]

variable [Nontrivial A]

theorem Feasible.sqrt_similarity {T H : A} {τ : ℝ} (h : Feasible T τ H) :
    IsUnit (CFC.sqrt H) ∧
      ‖CFC.sqrt H * T * Ring.inverse (CFC.sqrt H)‖ ≤ 1 ∧
      ‖CFC.sqrt H‖ * ‖Ring.inverse (CFC.sqrt H)‖ ≤ Real.sqrt τ := by
  let S := CFC.sqrt H
  let R := Ring.inverse S
  have hS0 : 0 ≤ S := CFC.sqrt_nonneg H
  have hS1 : (1 : A) ≤ S := by
    simpa only [CFC.sqrt_one] using CFC.sqrt_le_sqrt (1 : A) H h.lower
  have hSpos : IsStrictlyPositive S := isStrictlyPositive_one.of_le hS1
  have hu : IsUnit S := hSpos.isUnit
  have hR0 : 0 ≤ R := (CFC.ringInverse_nonneg_iff_nonneg_of_isUnit hu).mpr hS0
  have hR1 : R ≤ (1 : A) := by
    simpa only [Ring.inverse_one] using CStarAlgebra.ringInverse_le_ringInverse hS1
  have hRS : R * S = 1 := Ring.inverse_mul_cancel S hu
  have hSR : S * R = 1 := Ring.mul_inverse_cancel S hu
  have hRSa : star R = R := (IsSelfAdjoint.of_nonneg hR0).star_eq
  have hSSa : star S = S := (IsSelfAdjoint.of_nonneg hS0).star_eq
  have hSS : S * S = H := CFC.sqrt_mul_sqrt_self H h.nonneg
  have hconj := star_left_conjugate_le_conjugate h.stein R
  have hright : star R * H * R = 1 := by
    rw [hRSa, ← hSS, ← mul_assoc, hRS, one_mul, hSR]
  have hleft : star R * (star T * H * T) * R =
      star (S * T * R) * (S * T * R) := by
    rw [star_mul, star_mul, hSSa, ← hSS]
    noncomm_ring
  rw [hleft, hright] at hconj
  refine ⟨hu, (norm_le_one_iff_star_mul_self_le _).mpr hconj, ?_⟩
  have hRn : ‖R‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg R hR0).mpr hR1
  change ‖S‖ * ‖R‖ ≤ Real.sqrt τ
  calc
    ‖S‖ * ‖R‖ ≤ ‖S‖ * 1 := mul_le_mul_of_nonneg_left hRn (norm_nonneg _)
    _ = Real.sqrt ‖H‖ := by simpa only [S, mul_one] using CFC.norm_sqrt H h.nonneg
    _ ≤ Real.sqrt τ := Real.sqrt_le_sqrt h.norm_le

theorem Feasible.sqrt_spectrum {T H : A} {τ : ℝ} (h : Feasible T τ H) :
    spectrum ℂ (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H)) = spectrum ℂ T := by
  obtain ⟨u, hu⟩ := h.sqrt_similarity.1
  rw [← hu]
  simpa only [Ring.inverse_unit] using spectrum.units_conjugate (R := ℂ) (a := T) (u := u)

omit [Nontrivial A] in
theorem feasible_of_contractive_similarity (R T : A) (hu : IsUnit R)
    (hc : ‖R * T * Ring.inverse R‖ ≤ 1) :
    Feasible T ((‖R‖ * ‖Ring.inverse R‖) ^ 2)
      ((‖Ring.inverse R‖ ^ 2) • (star R * R)) := by
  let Q := Ring.inverse R
  let D := R * T * Q
  have hRQ : R * Q = 1 := Ring.mul_inverse_cancel R hu
  have hQR : Q * R = 1 := Ring.inverse_mul_cancel R hu
  have hRn : star R * R ≤ algebraMap ℝ A (‖R‖ ^ 2) := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg _) (star_mul_self_nonneg R)).mp
    rw [CStarRing.norm_star_mul_self, sq]
  have hQn : star Q * Q ≤ algebraMap ℝ A (‖Q‖ ^ 2) := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg _) (star_mul_self_nonneg Q)).mp
    rw [CStarRing.norm_star_mul_self, sq]
  have hl := star_left_conjugate_le_conjugate hQn R
  have hll : star R * (star Q * Q) * R = 1 := by
    rw [← mul_assoc, ← star_mul, hQR, star_one, one_mul, hQR]
  have hlr : star R * algebraMap ℝ A (‖Q‖ ^ 2) * R = (‖Q‖ ^ 2) • (star R * R) := by
    simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one]
  rw [hll, hlr] at hl
  have hd := (norm_le_one_iff_star_mul_self_le D).mp hc
  have hs := star_left_conjugate_le_conjugate hd R
  have hsl : star R * (star D * D) * R = star T * (star R * R) * T := by
    have he : D * R = R * T := by simp only [D, mul_assoc, hQR, mul_one]
    calc
      star R * (star D * D) * R = star (D * R) * (D * R) := by
        simp only [star_mul, mul_assoc]
      _ = star T * (star R * R) * T := by rw [he, star_mul]; simp only [mul_assoc]
  rw [hsl, mul_one] at hs
  refine ⟨hl, ?_, ?_⟩
  · have h := smul_le_smul_of_nonneg_left hRn (sq_nonneg ‖Q‖)
    convert h using 1
    simp only [Algebra.algebraMap_eq_smul_one, smul_smul]
    congr 1
    dsimp only [Q]
    ring
  · simpa only [mul_smul_comm, smul_mul_assoc] using
      smul_le_smul_of_nonneg_left hs (sq_nonneg ‖Q‖)

theorem optimal_similarity {T H : A} {τ : ℝ} (h : Feasible T τ H)
    (hmin : ∀ (τ' : ℝ) (H' : A), Feasible T τ' H' → τ ≤ τ') :
    ‖CFC.sqrt H‖ * ‖Ring.inverse (CFC.sqrt H)‖ = Real.sqrt τ ∧
      ∀ R : A, IsUnit R → ‖R * T * Ring.inverse R‖ ≤ 1 →
        Real.sqrt τ ≤ ‖R‖ * ‖Ring.inverse R‖ := by
  have hbest : ∀ R : A, IsUnit R → ‖R * T * Ring.inverse R‖ ≤ 1 →
      Real.sqrt τ ≤ ‖R‖ * ‖Ring.inverse R‖ := by
    intro R hu hc
    have hτ := hmin _ _ (feasible_of_contractive_similarity R T hu hc)
    have hn : 0 ≤ ‖R‖ * ‖Ring.inverse R‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    simpa only [Real.sqrt_sq hn] using Real.sqrt_le_sqrt hτ
  exact ⟨le_antisymm h.sqrt_similarity.2.2
    (hbest _ h.sqrt_similarity.1 h.sqrt_similarity.2.1), hbest⟩

end Similarity

end CrouzeixHilbert.Metric

end

end OAI
