import OAI.Analysis.MarkovType.DyadicWeakAmplification

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

omit sectionNormedSpaceℝE in
theorem finiteMoment_nonneg [NormedSpace ℝ E] {I : Type*} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (a : ℝ) (φ : I → E) : 0 ≤ finiteMoment w a φ := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.rpow_nonneg (norm_nonneg _) _)

theorem finiteMoment_smul {I : Type*} [Fintype I] (w : I → ℝ)
    (a c : ℝ) (φ : I → E) :
    finiteMoment w a (c • φ) = |c| ^ a * finiteMoment w a φ := by
  unfold finiteMoment
  simp_rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dyadicInputWeight_pos {N : ℕ} (i : DyadicAtom N) :
    0 < dyadicInputWeight i := by
  cases i with
  | inl u => exact zero_lt_one
  | inr z =>
      change 0 < (dyadicLaw z.1.val).mass z.2
      rw [dyadicLaw_mass]
      exact pow_pos (inv_pos.mpr (by norm_num)) _

omit sectionNormedSpaceℝE in
theorem dyadic_eq_zero_of_inputMoment_eq_zero [NormedSpace ℝ E] {a : ℝ} (_ha : 0 < a)
    {N : ℕ} (φ : DyadicAtom N → E)
    (hφ : finiteMoment dyadicInputWeight a φ = 0) : φ = 0 := by
  classical
  funext i
  have hterm : dyadicInputWeight i * ‖φ i‖ ^ a ≤ 0 := by
    rw [← hφ]
    exact Finset.single_le_sum
      (fun j _ => mul_nonneg (dyadicInputWeight_nonneg j)
        (Real.rpow_nonneg (norm_nonneg _) _)) (Finset.mem_univ i)
  have hzero : dyadicInputWeight i * ‖φ i‖ ^ a = 0 :=
    le_antisymm hterm (mul_nonneg (dyadicInputWeight_nonneg i)
      (Real.rpow_nonneg (norm_nonneg _) _))
  have hp : ‖φ i‖ ^ a = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (dyadicInputWeight_pos i).ne'
  exact norm_eq_zero.mp ((Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg _)).mp hp).1

def dyadicCenter {N : ℕ} (φ : DyadicAtom N → E) : DyadicAtom N → E
  | .inl _ => 0
  | .inr z => φ (.inr z)

omit sectionNormedSpaceℝE in
@[simp] theorem dyadicRoot_center [NormedSpace ℝ E] {N : ℕ} (φ : DyadicAtom N → E) :
    dyadicRoot (dyadicCenter φ) = 0 := rfl

omit sectionNormedSpaceℝE in
@[simp] theorem dyadicCoefficient_center [NormedSpace ℝ E] {N : ℕ} (φ : DyadicAtom N → E)
    (j : Fin N) (α : DyadicWord j.val) :
    dyadicCoefficient (dyadicCenter φ) j α = dyadicCoefficient φ j α := rfl

theorem dyadicInputMoment_center {a : ℝ} (ha : 0 < a)
    {N : ℕ} (φ : DyadicAtom N → E) :
    finiteMoment dyadicInputWeight a φ = ‖dyadicRoot φ‖ ^ a +
      finiteMoment dyadicInputWeight a (dyadicCenter φ) := by
  rw [dyadicInputMoment_prefixes φ a, dyadicInputMoment_prefixes (dyadicCenter φ) a]
  simp only [dyadicRoot_center, norm_zero, Real.zero_rpow ha.ne', zero_add,
    dyadicCoefficient_center]

theorem dyadicProcess_center {N : ℕ} (φ : DyadicAtom N → E)
    (n : ℕ) (ω : DyadicWord N) :
    dyadicProcess φ n ω = dyadicRoot φ + dyadicProcess (dyadicCenter φ) n ω := by
  induction n with
  | zero => simp only [dyadicProcess_zero, dyadicRoot_center, add_zero]
  | succ n ih =>
      simp only [dyadicProcess, ih]
      by_cases hn : n < N
      · simp only [dite_eq_left hn, dyadicIncrement, dyadicCoefficient_center, add_assoc]
      · simp only [dite_eq_right hn, add_zero]

theorem dyadicSynthesis_center {N : ℕ} (φ : DyadicAtom N → E) (ω : DyadicWord N) :
    dyadicSynthesis N φ ω =
      dyadicRoot φ + dyadicSynthesis N (dyadicCenter φ) ω :=
  dyadicProcess_center φ N ω

theorem dyadic_zero_tail {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A)
    (hmax : DyadicNormalizedWeakMax E a A) {N : ℕ} (φ : DyadicAtom N → E)
    (hroot : dyadicRoot φ = 0) (t : ℝ) (ht : 0 < t) :
    (dyadicLaw N).prob (fun ω => t < ‖dyadicSynthesis N φ ω‖) ≤
      dyadicZeroWeakConstant a A * finiteMoment dyadicInputWeight a φ / t ^ a := by
  classical
  let S := finiteMoment dyadicInputWeight a φ
  have hS0 : 0 ≤ S := finiteMoment_nonneg _ dyadicInputWeight_nonneg _ _
  by_cases hS : S = 0
  · have hzero := dyadic_eq_zero_of_inputMoment_eq_zero ha φ hS
    rw [show finiteMoment dyadicInputWeight a φ = 0 from hS, mul_zero, zero_div]
    simp [hzero, FiniteLaw.prob, not_lt.mpr ht.le]
  · have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS)
    let R := S ^ (1 / a)
    have hR : 0 < R := Real.rpow_pos_of_pos hSpos _
    have hRa : R ^ a = S := by
      simpa only [R, one_div] using Real.rpow_inv_rpow hS0 ha.ne'
    have hc : 0 < R⁻¹ := inv_pos.mpr hR
    have hscaled : finiteMoment dyadicInputWeight a (R⁻¹ • φ) ≤ 1 := by
      rw [finiteMoment_smul, abs_of_pos hc, Real.inv_rpow hR.le, hRa]
      change S⁻¹ * S ≤ 1
      rw [inv_mul_cancel₀ hS]
    have hscaledroot : dyadicRoot (R⁻¹ • φ) = 0 := by
      change R⁻¹ • dyadicRoot φ = 0
      rw [hroot, smul_zero]
    have hevent : (fun ω => t < ‖dyadicSynthesis N φ ω‖) =
        (fun ω => R⁻¹ * t < ‖dyadicSynthesis N (R⁻¹ • φ) ω‖) := by
      funext ω
      apply propext
      change (t < ‖dyadicProcess φ N ω‖) ↔
        R⁻¹ * t < ‖dyadicProcess (R⁻¹ • φ) N ω‖
      rw [dyadicProcess_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      exact (mul_lt_mul_iff_right₀ hc).symm
    rw [hevent]
    calc
      _ ≤ dyadicZeroWeakConstant a A / (R⁻¹ * t) ^ a :=
        dyadic_normalized_zero_tail ha hA hmax _ hscaledroot hscaled _ (mul_pos hc ht)
      _ = dyadicZeroWeakConstant a A * finiteMoment dyadicInputWeight a φ / t ^ a := by
        rw [Real.mul_rpow hc.le ht.le, Real.inv_rpow hR.le, hRa]
        change _ = dyadicZeroWeakConstant a A * S / t ^ a
        have hta : t ^ a ≠ 0 := (Real.rpow_pos_of_pos ht a).ne'
        field_simp [hS, hta]

def dyadicWeakConstant (a A : ℝ) : ℝ := (2 : ℝ) ^ a * dyadicZeroWeakConstant a A

def dyadicWeakNorm (a A : ℝ) : ℝ := dyadicWeakConstant a A ^ (1 / a)

theorem dyadicWeakConstant_pos {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A) :
    0 < dyadicWeakConstant a A :=
  mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (lt_of_lt_of_le zero_lt_one (dyadicZeroWeakConstant_ge_one ha hA))

theorem dyadicWeakNorm_pos {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A) :
    0 < dyadicWeakNorm a A := Real.rpow_pos_of_pos (dyadicWeakConstant_pos ha hA) _

theorem dyadicWeakNorm_power {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A) :
    dyadicWeakNorm a A ^ a = dyadicWeakConstant a A := by
  simpa only [dyadicWeakNorm, one_div] using
    Real.rpow_inv_rpow (dyadicWeakConstant_pos ha hA).le ha.ne'

theorem dyadic_tail {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A)
    (hmax : DyadicNormalizedWeakMax E a A) {N : ℕ} (φ : DyadicAtom N → E)
    (t : ℝ) (ht : 0 < t) :
    (dyadicLaw N).prob (fun ω => t < ‖dyadicSynthesis N φ ω‖) ≤
      dyadicWeakConstant a A * finiteMoment dyadicInputWeight a φ / t ^ a := by
  have hta : 0 < t ^ a := Real.rpow_pos_of_pos ht _
  have htwo : 0 < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) _
  have hC : 1 ≤ dyadicZeroWeakConstant a A := dyadicZeroWeakConstant_ge_one ha hA
  have hwhole : 0 ≤ finiteMoment dyadicInputWeight a φ :=
    finiteMoment_nonneg _ dyadicInputWeight_nonneg _ _
  have hcenter : 0 ≤ finiteMoment dyadicInputWeight a (dyadicCenter φ) :=
    finiteMoment_nonneg _ dyadicInputWeight_nonneg _ _
  have hrootle : ‖dyadicRoot φ‖ ^ a ≤ finiteMoment dyadicInputWeight a φ := by
    rw [dyadicInputMoment_center ha φ]
    exact le_add_of_nonneg_right hcenter
  have hcenterle : finiteMoment dyadicInputWeight a (dyadicCenter φ) ≤
      finiteMoment dyadicInputWeight a φ := by
    rw [dyadicInputMoment_center ha φ]
    exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)
  by_cases hlarge : t / 2 < ‖dyadicRoot φ‖
  · have hp : (t / 2) ^ a ≤ ‖dyadicRoot φ‖ ^ a :=
      Real.rpow_le_rpow (by positivity) hlarge.le ha.le
    rw [Real.div_rpow ht.le (by norm_num) a] at hp
    have hrootpower : t ^ a ≤ (2 : ℝ) ^ a * ‖dyadicRoot φ‖ ^ a := by
      simpa only [mul_comm] using (div_le_iff₀ htwo).mp hp
    have hmul : finiteMoment dyadicInputWeight a φ ≤
        dyadicZeroWeakConstant a A * finiteMoment dyadicInputWeight a φ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hwhole
    calc
      _ ≤ 1 := (dyadicLaw N).prob_le_one _
      _ ≤ dyadicWeakConstant a A * finiteMoment dyadicInputWeight a φ / t ^ a := by
        apply (le_div_iff₀ hta).mpr
        simp only [one_mul, dyadicWeakConstant]
        calc
          t ^ a ≤ (2 : ℝ) ^ a * ‖dyadicRoot φ‖ ^ a := hrootpower
          _ ≤ (2 : ℝ) ^ a * finiteMoment dyadicInputWeight a φ :=
            mul_le_mul_of_nonneg_left hrootle htwo.le
          _ ≤ (2 : ℝ) ^ a * (dyadicZeroWeakConstant a A *
                finiteMoment dyadicInputWeight a φ) :=
            mul_le_mul_of_nonneg_left hmul htwo.le
          _ = _ := by ring
  · have hevent : ∀ ω, t < ‖dyadicSynthesis N φ ω‖ →
        t / 2 < ‖dyadicSynthesis N (dyadicCenter φ) ω‖ := by
      intro ω hω
      rw [dyadicSynthesis_center] at hω
      have hn := norm_add_le (dyadicRoot φ) (dyadicSynthesis N (dyadicCenter φ) ω)
      have hr := not_lt.mp hlarge
      linarith
    calc
      _ ≤ (dyadicLaw N).prob (fun ω => t / 2 < ‖dyadicSynthesis N (dyadicCenter φ) ω‖) :=
        (dyadicLaw N).prob_mono hevent
      _ ≤ dyadicZeroWeakConstant a A *
            finiteMoment dyadicInputWeight a (dyadicCenter φ) / (t / 2) ^ a :=
        dyadic_zero_tail ha hA hmax _ (dyadicRoot_center φ) _ (by positivity)
      _ = dyadicWeakConstant a A *
            finiteMoment dyadicInputWeight a (dyadicCenter φ) / t ^ a := by
        rw [Real.div_rpow ht.le (by norm_num) a]
        unfold dyadicWeakConstant
        field_simp [hta.ne', htwo.ne']
      _ ≤ dyadicWeakConstant a A * finiteMoment dyadicInputWeight a φ / t ^ a :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcenterle (dyadicWeakConstant_pos ha hA).le) hta.le

theorem dyadic_weak_type {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A)
    (hmax : DyadicNormalizedWeakMax E a A) (N : ℕ) :
    FiniteWeakType dyadicInputWeight (dyadicLaw N).mass (dyadicSynthesis (E := E) N)
      a (dyadicWeakNorm a A) := by
  intro φ t ht
  change (dyadicLaw N).prob (fun ω => t < ‖dyadicSynthesis N φ ω‖) ≤ _
  convert dyadic_tail ha hA hmax φ t ht using 1
  rw [Real.div_rpow (dyadicWeakNorm_pos ha hA).le ht.le,
    dyadicWeakNorm_power ha hA]
  ring

end MarkovSuperreflexivity

end

end OAI
