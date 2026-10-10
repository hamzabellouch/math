import Mathlib
import OAI.Probability.SKFluctuations.PhysicalCommonCutSwap

namespace OAI

/-! Physical Increment Moment. -/

noncomputable section


namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem physicalCutNormPower_integrable (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {c : ℝ} (ho : OrderedSteps c steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (k q : ℕ) : Integrable (fun p => ‖actualSpinPath n steps x k p‖^q)
      (physicalPathLaw μ n steps x hx) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps ho
  let : IsFiniteMeasure (physicalPathLaw μ n steps x hx) := by
    unfold physicalPathLaw
    infer_instance
  apply Integrable.of_bound ((actualSpinPath_measurable n steps ho x hx k).norm.pow_const q).aestronglyMeasurable 1
  exact Eventually.of_forall fun p => by
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact (pow_le_pow_left₀ (norm_nonneg _) (actualSpinPath_norm_le n steps ho x k p) q).trans_eq (one_pow q)

 theorem physicalCutIncrementNormPower_integrable (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {c : ℝ} (ho : OrderedSteps c steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (a b q : ℕ) : Integrable (fun p => ‖physicalCutIncrement n steps x a b p‖^q)
      (physicalPathLaw μ n steps x hx) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps ho
  let : IsFiniteMeasure (physicalPathLaw μ n steps x hx) := by
    unfold physicalPathLaw
    infer_instance
  apply Integrable.of_bound ((physicalCutIncrement_measurable n steps ho x hx a b).norm.pow_const q).aestronglyMeasurable (2^q)
  exact Eventually.of_forall fun p => by
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (physicalCutIncrement_norm_le n steps ho x a b p) q

 theorem physicalRawRatio_increment_moment (n l : ℕ) (hl : 0 < l)
    (steps : List (GaussianStep (FeatureIndex n))) {c xs : ℝ}
    (ho : OrderedSteps c steps) (hxs : 0 < xs)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsProbabilityMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ steps.length+1) :
    (∫ p, ‖physicalCutIncrement n steps x a b p‖^(2*l) ∂physicalPathLaw μ n steps x hx) ≤
      (2*physicalRawRatio n l steps c xs μ x hx)^(2*l)*(xs+physicalCutMass c steps b)^l := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps ho
  let ν := physicalPathLaw μ n steps x hx
  let : IsProbabilityMeasure ν := by
    dsimp [ν,physicalPathLaw]
    infer_instance
  let Q := physicalRawRatio n l steps c xs μ x hx
  let S := xs+physicalCutMass c steps b
  have hS : 0 ≤ S := add_nonneg hxs.le (physicalCutMass_mem steps ho b).1
  have hQ : 0 ≤ Q := le_trans zero_le_one (physicalRawRatio_one_le n l steps c xs μ x hx)
  have hA := physicalRawRatio_moment n l hl steps ho hxs μ x hx (hab.trans hb)
  have hB := physicalRawRatio_moment n l hl steps ho hxs μ x hx hb
  have hAB : (xs+physicalCutMass c steps a)^(2*l) ≤ S^(2*l) :=
    pow_le_pow_left₀ (add_nonneg hxs.le (physicalCutMass_mem steps ho a).1)
      (by simpa [S,add_comm] using add_le_add_left (physicalCutMass_monotone steps ho hab) xs) _
  have hA' : (∫ p, ‖actualSpinPath n steps x a p‖^(4*l) ∂ν) ≤ Q^(4*l)*S^(2*l) :=
    hA.trans (mul_le_mul_of_nonneg_left hAB (pow_nonneg hQ _))
  have hD : (∫ p, ‖physicalCutIncrement n steps x a b p‖^(4*l) ∂ν) ≤
      (2*Q)^(4*l)*S^(2*l) := by
    calc
      _ ≤ ∫ p, 2^(4*l-1)*(‖actualSpinPath n steps x b p‖^(4*l)+‖actualSpinPath n steps x a p‖^(4*l)) ∂ν := by
        apply integral_mono (physicalCutIncrementNormPower_integrable n steps ho μ x hx a b _)
          (((physicalCutNormPower_integrable n steps ho μ x hx b _).add
            (physicalCutNormPower_integrable n steps ho μ x hx a _)).const_mul _)
        intro p
        apply (pow_le_pow_left₀ (norm_nonneg _)
          (norm_sub_le (actualSpinPath n steps x b p) (actualSpinPath n steps x a p)) (4*l)).trans
        exact add_pow_le (norm_nonneg _) (norm_nonneg _) (4*l)
      _ = 2^(4*l-1)*((∫ p, ‖actualSpinPath n steps x b p‖^(4*l) ∂ν)+
          (∫ p, ‖actualSpinPath n steps x a p‖^(4*l) ∂ν)) := by
        rw [integral_const_mul,integral_add
          (physicalCutNormPower_integrable n steps ho μ x hx b _)
          (physicalCutNormPower_integrable n steps ho μ x hx a _)]
      _ ≤ 2^(4*l-1)*(Q^(4*l)*S^(2*l)+Q^(4*l)*S^(2*l)) :=
        mul_le_mul_of_nonneg_left (add_le_add hB hA') (by positivity)
      _ = (2*Q)^(4*l)*S^(2*l) := by
        have htwo : (2:ℝ)^(4*l) = (2:ℝ)^(4*l-1)*2 := by
          calc
            _ = (2:ℝ)^((4*l-1)+1) := by congr 1; omega
            _ = _ := pow_succ _ _
        rw [mul_pow,htwo]
        ring
  have hJ := integral_pow_le_mass ν
    (Eventually.of_forall fun p => pow_nonneg (norm_nonneg (physicalCutIncrement n steps x a b p)) (2*l))
    (physicalCutIncrementNormPower_integrable n steps ho μ x hx a b (2*l))
    (by omega : 0 < 2)
    (by simpa only [← pow_mul,show 2*l*2 = 4*l by omega] using
      physicalCutIncrementNormPower_integrable n steps ho μ x hx a b (4*l))
  have hsq : (∫ p, ‖physicalCutIncrement n steps x a b p‖^(2*l) ∂ν)^2 ≤
      ((2*Q)^(2*l)*S^l)^2 := by
    have he : ((2*Q)^(2*l)*S^l)^2 = (2*Q)^(4*l)*S^(2*l) := by
      rw [mul_pow,← pow_mul,← pow_mul]
      congr 1 <;> congr 1 <;> omega
    rw [he]
    apply le_trans ?_ hD
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one,one_pow,one_mul,← pow_mul,
      show 2*l*2=4*l by omega] using hJ
  exact (sq_le_sq₀ (integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _)
    (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hQ) _) (pow_nonneg hS _))).1 hsq

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators RealInnerProductSpace

 theorem projectionEuclideanNorm_coe (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    projectionEuclideanNorm n (fun i => v i) = ‖v‖ := by
  rw [projectionEuclideanNorm,EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs,sq_abs]

 theorem physicalCutIncrement_coe_measurable (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {c : ℝ} (ho : OrderedSteps c steps) {P : Type} [MeasurableSpace P]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (a b : ℕ) :
    Measurable (fun p i => physicalCutIncrement n steps x a b p i) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).continuous.measurable.comp
    (physicalCutIncrement_measurable n steps ho x hx a b)

 theorem physicalCutPairSquare_futurePair (n : ℕ)
    (common tail mid pre : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (a b : ℕ)
    (p : PhysicalPathState P n (common++(pre++(mid++tail)))) :
    physicalCutPairSquare n (common++(pre++(mid++tail))) x common.length a b
      (common.length+pre.length) (common.length+(pre.length+mid.length)) p =
    conditionalPathAverage (uniformWeight n) (finiteFeature n) (common++(pre++(mid++tail)))
      x common.length (fun q => (∑ i, physicalCutIncrement n (common++(pre++(mid++tail))) x a b p i *
        physicalFuturePairIncrement n common tail mid pre x q i)^2) p := by
  unfold physicalCutPairSquare
  simp_rw [show ∀ q, physicalCutIncrement n (common++(pre++(mid++tail))) x
      (common.length+pre.length) (common.length+(pre.length+mid.length)) q =
      WithLp.toLp 2 (physicalFuturePairIncrement n common tail mid pre x q) from
    fun q => (physicalFuturePairIncrement_eq_spinPath n common tail mid pre x q).symm]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,mul_comm]

 theorem root_le_of_even_projection {J A Q S : ℝ} {l : ℕ} (hl : 0 < l)
    (hI : 0 ≤ J) (hA : 0 ≤ A) (hQ : 0 ≤ Q) (hS : 0 ≤ S)
    (h : J ≤ A^(2*l)*(2*Q)^(2*l)*S^l) :
    J^((l:ℝ)⁻¹) ≤ A^2*(2*Q)^2*S := by
  have he : A^(2*l)*(2*Q)^(2*l)*S^l = (A^2*(2*Q)^2*S)^l := by
    simp only [mul_pow,← pow_mul]
  rw [he] at h
  have hh := Real.rpow_le_rpow hI h (inv_nonneg.2 (Nat.cast_nonneg l))
  have hnonneg : 0 ≤ A^2*(2*Q)^2*S :=
    mul_nonneg (mul_nonneg (pow_nonneg hA 2)
      (pow_nonneg (mul_nonneg (by norm_num) hQ) 2)) hS
  simpa only [Real.pow_rpow_inv_natCast hnonneg hl.ne'] using hh

 theorem eventually_cut_pair_moment (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (common tail mid pre skip : List (GaussianStep (FeatureIndex n)))
      (a c D xs : ℝ), 0 < a → 0 < D → D ≤ B → 0 < xs →
      OrderedSteps a (pre++(mid++tail)) →
      OrderedSteps c (common++((skip++pre)++(mid++tail))) →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (v w : ℕ),
      v ≤ w → w ≤ (common++((skip++pre)++(mid++tail))).length+1 →
      (∀ V : Fin n → ℝ, AlignedFieldClock (fieldProjectionDirection n V) D pre) →
    (∫ p, (physicalCutPairSquare n (common++((skip++pre)++(mid++tail))) x common.length v w
      (common.length+(skip++pre).length)
      (common.length+((skip++pre).length+mid.length)) p)^(k+1)
      ∂physicalPathLaw μ n (common++((skip++pre)++(mid++tail))) x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^2 *
        (2*physicalRawRatio n (k+1) (common++((skip++pre)++(mid++tail))) c xs μ x hx)^2 *
        (xs+physicalCutMass c (common++((skip++pre)++(mid++tail))) w) := by
  filter_upwards [eventually_common_cut_conditional_square_projection k B] with n hn
  intro P _ common tail mid pre skip a c D xs ha hD hDB hxs ho hs μ _ x hx v w hvw hw hc
  let steps := common++((skip++pre)++(mid++tail))
  let V := fun p i => physicalCutIncrement n steps x v w p i
  have hV : Measurable V := physicalCutIncrement_coe_measurable n steps hs x hx v w
  have hR : ∀ p, projectionEuclideanNorm n (V p) ≤ 2 := fun p => by
    dsimp only [V]
    rw [projectionEuclideanNorm_coe]
    exact physicalCutIncrement_norm_le n steps hs x v w p
  have hh := hn P common tail mid pre skip a c D ha hD hDB ho hs μ x hx V hV 2 hR (fun p => hc (V p))
  dsimp only [V,steps] at hh
  simp_rw [projectionEuclideanNorm_coe,← physicalCutPairSquare_futurePair] at hh
  let A := projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D))
  let Q := physicalRawRatio n (k+1) steps c xs μ x hx
  let S := xs+physicalCutMass c steps w
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (projectionLpConstant_pos k).le (sq_nonneg _))
    (mul_nonneg ha.le (Real.sqrt_nonneg _))
  have hQ : 0 ≤ Q := le_trans zero_le_one (physicalRawRatio_one_le n (k+1) steps c xs μ x hx)
  have hS : 0 ≤ S := add_nonneg hxs.le (physicalCutMass_mem steps hs w).1
  apply root_le_of_even_projection (Nat.succ_pos k)
    (integral_nonneg fun p => pow_nonneg (physicalCutPairSquare_nonneg n steps x _ _ _ _ _ p) _) hA hQ hS
  apply hh.trans
  have hM := mul_le_mul_of_nonneg_left
    (physicalRawRatio_increment_moment n (k+1) (Nat.succ_pos k) steps hs hxs μ x hx hvw hw)
    (pow_nonneg hA (2*k+2))
  simpa only [show 2*(k+1) = 2*k+2 by omega,mul_assoc] using hM

end SKFluctuations

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators RealInnerProductSpace

 theorem physicalCutPairSquare_futureTerminal (n : ℕ)
    (common tail pre : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (a b : ℕ)
    (p : PhysicalPathState P n (common++(pre++tail))) :
    physicalCutPairSquare n (common++(pre++tail)) x common.length a b
      (common.length+pre.length) ((common++(pre++tail)).length+1) p =
    conditionalPathAverage (uniformWeight n) (finiteFeature n) (common++(pre++tail))
      x common.length (fun q => (∑ i, physicalCutIncrement n (common++(pre++tail)) x a b p i *
        physicalFutureTerminalIncrement n common tail pre x q i)^2) p := by
  unfold physicalCutPairSquare
  simp_rw [show ∀ q, physicalCutIncrement n (common++(pre++tail)) x
      (common.length+pre.length) ((common++(pre++tail)).length+1) q =
      WithLp.toLp 2 (physicalFutureTerminalIncrement n common tail pre x q) from
    fun q => by
      simpa only [physicalCutIncrement,List.length_append,Nat.add_assoc] using
        (physicalFutureTerminalIncrement_eq_spinPath n common tail pre x q).symm]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,mul_comm]

 theorem eventually_cut_pair_terminal_moment (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (common tail pre skip : List (GaussianStep (FeatureIndex n)))
      (a c D xs : ℝ), 0 < a → 0 < D → D ≤ B → 0 < xs →
      OrderedSteps a (pre++tail) →
      OrderedSteps c (common++((skip++pre)++tail)) →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (v w : ℕ),
      v ≤ w → w ≤ (common++((skip++pre)++tail)).length+1 →
      (∀ V : Fin n → ℝ, AlignedFieldClock (fieldProjectionDirection n V) D pre) →
    (∫ p, (physicalCutPairSquare n (common++((skip++pre)++tail)) x common.length v w
      (common.length+(skip++pre).length)
      ((common++((skip++pre)++tail)).length+1) p)^(k+1)
      ∂physicalPathLaw μ n (common++((skip++pre)++tail)) x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^2 *
        (2*physicalRawRatio n (k+1) (common++((skip++pre)++tail)) c xs μ x hx)^2 *
        (xs+physicalCutMass c (common++((skip++pre)++tail)) w) := by
  filter_upwards [eventually_common_cut_terminal_conditional_square_projection k B] with n hn
  intro P _ common tail pre skip a c D xs ha hD hDB hxs ho hs μ _ x hx v w hvw hw hc
  let steps := common++((skip++pre)++tail)
  let V := fun p i => physicalCutIncrement n steps x v w p i
  have hV : Measurable V := physicalCutIncrement_coe_measurable n steps hs x hx v w
  have hR : ∀ p, projectionEuclideanNorm n (V p) ≤ 2 := fun p => by
    dsimp only [V]
    rw [projectionEuclideanNorm_coe]
    exact physicalCutIncrement_norm_le n steps hs x v w p
  have hh := hn P common tail pre skip a c D ha hD hDB ho hs μ x hx V hV 2 hR (fun p => hc (V p))
  dsimp only [V,steps] at hh
  simp_rw [projectionEuclideanNorm_coe,← physicalCutPairSquare_futureTerminal] at hh
  let A := projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D))
  let Q := physicalRawRatio n (k+1) steps c xs μ x hx
  let S := xs+physicalCutMass c steps w
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (projectionLpConstant_pos k).le (sq_nonneg _))
    (mul_nonneg ha.le (Real.sqrt_nonneg _))
  have hQ : 0 ≤ Q := le_trans zero_le_one (physicalRawRatio_one_le n (k+1) steps c xs μ x hx)
  have hS : 0 ≤ S := add_nonneg hxs.le (physicalCutMass_mem steps hs w).1
  apply root_le_of_even_projection (Nat.succ_pos k)
    (integral_nonneg fun p => pow_nonneg (physicalCutPairSquare_nonneg n steps x _ _ _ _ _ p) _) hA hQ hS
  apply hh.trans
  have hM := mul_le_mul_of_nonneg_left
    (physicalRawRatio_increment_moment n (k+1) (Nat.succ_pos k) steps hs hxs μ x hx hvw hw)
    (pow_nonneg hA (2*k+2))
  simpa only [show 2*(k+1) = 2*k+2 by omega,mul_assoc] using hM

end SKFluctuations

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators RealInnerProductSpace

 theorem physicalCutPairSquare_futurePair_observed (n : ℕ)
    (common tail mid pre : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (a b : ℕ)
    (p : PhysicalPathState P n (common++(pre++(mid++tail)))) :
    physicalCutPairSquare n (common++(pre++(mid++tail))) x common.length
      (common.length+pre.length) (common.length+(pre.length+mid.length)) a b p =
    conditionalPathAverage (uniformWeight n) (finiteFeature n) (common++(pre++(mid++tail)))
      x common.length (fun q => (∑ i, physicalCutIncrement n (common++(pre++(mid++tail))) x a b q i *
        physicalFuturePairIncrement n common tail mid pre x p i)^2) p := by
  unfold physicalCutPairSquare
  rw [show physicalCutIncrement n (common++(pre++(mid++tail))) x
      (common.length+pre.length) (common.length+(pre.length+mid.length)) p =
      WithLp.toLp 2 (physicalFuturePairIncrement n common tail mid pre x p) from
    (physicalFuturePairIncrement_eq_spinPath n common tail mid pre x p).symm]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]

 theorem eventually_cut_pair_observed_moment (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (common tail mid pre skip : List (GaussianStep (FeatureIndex n)))
      (a c D xs : ℝ), 0 < a → 0 < D → D ≤ B → 0 < xs →
      OrderedSteps a (pre++(mid++tail)) →
      OrderedSteps c (common++((skip++pre)++(mid++tail))) →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (v w : ℕ),
      v ≤ w → w ≤ (common++((skip++pre)++(mid++tail))).length+1 →
      (∀ V : Fin n → ℝ, AlignedFieldClock (fieldProjectionDirection n V) D pre) →
    (∫ p, (physicalCutPairSquare n (common++((skip++pre)++(mid++tail))) x common.length
      (common.length+(skip++pre).length)
      (common.length+((skip++pre).length+mid.length)) v w p)^(k+1)
      ∂physicalPathLaw μ n (common++((skip++pre)++(mid++tail))) x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^2 *
        (2*physicalRawRatio n (k+1) (common++((skip++pre)++(mid++tail))) c xs μ x hx)^2 *
        (xs+physicalCutMass c (common++((skip++pre)++(mid++tail))) w) := by
  filter_upwards [eventually_common_cut_observed_square_projection k B] with n hn
  intro P _ common tail mid pre skip a c D xs ha hD hDB hxs ho hs μ _ x hx v w hvw hw hc
  let steps := common++((skip++pre)++(mid++tail))
  let V := fun p i => physicalCutIncrement n steps x v w p i
  have hV : Measurable V := physicalCutIncrement_coe_measurable n steps hs x hx v w
  have hR : ∀ p, projectionEuclideanNorm n (V p) ≤ 2 := fun p => by
    dsimp only [V]
    rw [projectionEuclideanNorm_coe]
    exact physicalCutIncrement_norm_le n steps hs x v w p
  have hh := hn P common tail mid pre skip a c D ha hD hDB ho hs μ x hx V hV 2 hR (fun p => hc (V p))
  dsimp only [V,steps] at hh
  simp_rw [projectionEuclideanNorm_coe,← physicalCutPairSquare_futurePair_observed] at hh
  let A := projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D))
  let Q := physicalRawRatio n (k+1) steps c xs μ x hx
  let S := xs+physicalCutMass c steps w
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (projectionLpConstant_pos k).le (sq_nonneg _))
    (mul_nonneg ha.le (Real.sqrt_nonneg _))
  have hQ : 0 ≤ Q := le_trans zero_le_one (physicalRawRatio_one_le n (k+1) steps c xs μ x hx)
  have hS : 0 ≤ S := add_nonneg hxs.le (physicalCutMass_mem steps hs w).1
  apply root_le_of_even_projection (Nat.succ_pos k)
    (integral_nonneg fun p => pow_nonneg (physicalCutPairSquare_nonneg n steps x _ _ _ _ _ p) _) hA hQ hS
  apply hh.trans
  have hM := mul_le_mul_of_nonneg_left
    (physicalRawRatio_increment_moment n (k+1) (Nat.succ_pos k) steps hs hxs μ x hx hvw hw)
    (pow_nonneg hA (2*k+2))
  simpa only [show 2*(k+1) = 2*k+2 by omega,mul_assoc] using hM

end SKFluctuations

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators RealInnerProductSpace

 theorem physicalCutPairSquare_futureTerminal_observed (n : ℕ)
    (common tail pre : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (a b : ℕ)
    (p : PhysicalPathState P n (common++(pre++tail))) :
    physicalCutPairSquare n (common++(pre++tail)) x common.length
      (common.length+pre.length) ((common++(pre++tail)).length+1) a b p =
    conditionalPathAverage (uniformWeight n) (finiteFeature n) (common++(pre++tail))
      x common.length (fun q => (∑ i, physicalCutIncrement n (common++(pre++tail)) x a b q i *
        physicalFutureTerminalIncrement n common tail pre x p i)^2) p := by
  unfold physicalCutPairSquare
  rw [show physicalCutIncrement n (common++(pre++tail)) x
      (common.length+pre.length) ((common++(pre++tail)).length+1) p =
      WithLp.toLp 2 (physicalFutureTerminalIncrement n common tail pre x p) from
    by
      simpa only [physicalCutIncrement,List.length_append,Nat.add_assoc] using
        (physicalFutureTerminalIncrement_eq_spinPath n common tail pre x p).symm]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]

 theorem eventually_cut_pair_terminal_observed_moment (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (common tail pre skip : List (GaussianStep (FeatureIndex n)))
      (a c D xs : ℝ), 0 < a → 0 < D → D ≤ B → 0 < xs →
      OrderedSteps a (pre++tail) →
      OrderedSteps c (common++((skip++pre)++tail)) →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (v w : ℕ),
      v ≤ w → w ≤ (common++((skip++pre)++tail)).length+1 →
      (∀ V : Fin n → ℝ, AlignedFieldClock (fieldProjectionDirection n V) D pre) →
    (∫ p, (physicalCutPairSquare n (common++((skip++pre)++tail)) x common.length
      (common.length+(skip++pre).length)
      ((common++((skip++pre)++tail)).length+1) v w p)^(k+1)
      ∂physicalPathLaw μ n (common++((skip++pre)++tail)) x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^2 *
        (2*physicalRawRatio n (k+1) (common++((skip++pre)++tail)) c xs μ x hx)^2 *
        (xs+physicalCutMass c (common++((skip++pre)++tail)) w) := by
  filter_upwards [eventually_common_cut_terminal_observed_square_projection k B] with n hn
  intro P _ common tail pre skip a c D xs ha hD hDB hxs ho hs μ _ x hx v w hvw hw hc
  let steps := common++((skip++pre)++tail)
  let V := fun p i => physicalCutIncrement n steps x v w p i
  have hV : Measurable V := physicalCutIncrement_coe_measurable n steps hs x hx v w
  have hR : ∀ p, projectionEuclideanNorm n (V p) ≤ 2 := fun p => by
    dsimp only [V]
    rw [projectionEuclideanNorm_coe]
    exact physicalCutIncrement_norm_le n steps hs x v w p
  have hh := hn P common tail pre skip a c D ha hD hDB ho hs μ x hx V hV 2 hR (fun p => hc (V p))
  dsimp only [V,steps] at hh
  simp_rw [projectionEuclideanNorm_coe,← physicalCutPairSquare_futureTerminal_observed] at hh
  let A := projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D))
  let Q := physicalRawRatio n (k+1) steps c xs μ x hx
  let S := xs+physicalCutMass c steps w
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (projectionLpConstant_pos k).le (sq_nonneg _))
    (mul_nonneg ha.le (Real.sqrt_nonneg _))
  have hQ : 0 ≤ Q := le_trans zero_le_one (physicalRawRatio_one_le n (k+1) steps c xs μ x hx)
  have hS : 0 ≤ S := add_nonneg hxs.le (physicalCutMass_mem steps hs w).1
  apply root_le_of_even_projection (Nat.succ_pos k)
    (integral_nonneg fun p => pow_nonneg (physicalCutPairSquare_nonneg n steps x _ _ _ _ _ p) _) hA hQ hS
  apply hh.trans
  have hM := mul_le_mul_of_nonneg_left
    (physicalRawRatio_increment_moment n (k+1) (Nat.succ_pos k) steps hs hxs μ x hx hvw hw)
    (pow_nonneg hA (2*k+2))
  simpa only [show 2*(k+1) = 2*k+2 by omega,mul_assoc] using hM

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

inductive PhysicalProjectionClock (n : ℕ) :
    List (GaussianStep (FeatureIndex n)) → ℕ → ℕ → ℕ → ℝ → ℝ → Prop
  | gaussian (common tail mid pre skip : List (GaussianStep (FeatureIndex n))) (a D : ℝ)
      (order : OrderedSteps a (pre++(mid++tail)))
      (clock : ∀ V : Fin n → ℝ, AlignedFieldClock (fieldProjectionDirection n V) D pre) :
      PhysicalProjectionClock n (common++((skip++pre)++(mid++tail))) common.length
        (common.length+(skip++pre).length) (common.length+((skip++pre).length+mid.length)) a D
  | terminal (common tail pre skip : List (GaussianStep (FeatureIndex n))) (a D : ℝ)
      (order : OrderedSteps a (pre++tail))
      (clock : ∀ V : Fin n → ℝ, AlignedFieldClock (fieldProjectionDirection n V) D pre) :
      PhysicalProjectionClock n (common++((skip++pre)++tail)) common.length
        (common.length+(skip++pre).length) ((common++((skip++pre)++tail)).length+1) a D

theorem eventually_physical_clock_pair_moment (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (a c D xs : ℝ),
      0 < a → 0 < D → D ≤ B → 0 < xs → OrderedSteps c steps →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (fork v w d e : ℕ),
      v ≤ w → w ≤ steps.length+1 →
      PhysicalProjectionClock n steps fork d e a D →
    (∫ p, (physicalCutPairSquare n steps x fork v w d e p)^(k+1)
      ∂physicalPathLaw μ n steps x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^2 *
        (2*physicalRawRatio n (k+1) steps c xs μ x hx)^2 *
        (xs+physicalCutMass c steps w) := by
  filter_upwards [eventually_cut_pair_moment k B,eventually_cut_pair_terminal_moment k B] with n hn ht
  intro P _ steps a c D xs ha hD hDB hxs hs μ _ x hx fork v w d e hvw hw hc
  cases hc with
  | gaussian common tail mid pre skip a D ho hc =>
    exact hn P common tail mid pre skip a c D xs ha hD hDB hxs ho hs μ x hx v w hvw hw hc
  | terminal common tail pre skip a D ho hc =>
    exact ht P common tail pre skip a c D xs ha hD hDB hxs ho hs μ x hx v w hvw hw hc

theorem eventually_physical_clock_pair_observed_moment (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (a c D xs : ℝ),
      0 < a → 0 < D → D ≤ B → 0 < xs → OrderedSteps c steps →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (fork v w d e : ℕ),
      v ≤ w → w ≤ steps.length+1 →
      PhysicalProjectionClock n steps fork d e a D →
    (∫ p, (physicalCutPairSquare n steps x fork d e v w p)^(k+1)
      ∂physicalPathLaw μ n steps x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^2 *
        (2*physicalRawRatio n (k+1) steps c xs μ x hx)^2 *
        (xs+physicalCutMass c steps w) := by
  filter_upwards [eventually_cut_pair_observed_moment k B,
    eventually_cut_pair_terminal_observed_moment k B] with n hn ht
  intro P _ steps a c D xs ha hD hDB hxs hs μ _ x hx fork v w d e hvw hw hc
  cases hc with
  | gaussian common tail mid pre skip a D ho hc =>
    exact hn P common tail mid pre skip a c D xs ha hD hDB hxs ho hs μ x hx v w hvw hw hc
  | terminal common tail pre skip a D ho hc =>
    exact ht P common tail pre skip a c D xs ha hD hDB hxs ho hs μ x hx v w hvw hw hc

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 def cutSlice {α : Type*} (xs : List α) (a b : ℕ) : List α := (xs.drop a).take (b-a)

 theorem cutSlice_append_drop {α : Type*} (xs : List α) {a b : ℕ} (hab : a ≤ b) :
    cutSlice xs a b ++ xs.drop b = xs.drop a := by
  simpa only [cutSlice,List.drop_drop,Nat.add_sub_of_le hab] using
    List.take_append_drop (b-a) (xs.drop a)

 theorem length_cutSlice {α : Type*} (xs : List α) {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ xs.length) : (cutSlice xs a b).length = b-a := by
  simp only [cutSlice,List.length_take,List.length_drop]
  exact Nat.min_eq_left (by omega)

 theorem take_append_slices {α : Type*} (xs : List α) {c q d e : ℕ}
    (hcq : c ≤ q) (hqd : q ≤ d) (hde : d ≤ e) :
    xs.take c ++ ((cutSlice xs c q ++ cutSlice xs q d)++(cutSlice xs d e ++ xs.drop e)) = xs := by
  rw [List.append_assoc,cutSlice_append_drop xs hde,
    cutSlice_append_drop xs hqd,cutSlice_append_drop xs hcq,List.take_append_drop]

end SKFluctuations.Hierarchy
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem orderedSteps_drop_cutMass {ι : Type} (steps : List (GaussianStep ι))
    {c : ℝ} (hc : OrderedSteps c steps) (k : ℕ) :
    OrderedSteps (physicalCutMass c steps k) (steps.drop k) := by
  induction steps generalizing c k with
  | nil => cases k <;> simp_all [physicalCutMass,OrderedSteps]
  | cons st steps ih =>
    cases k with
    | zero => exact hc
    | succ k => exact ih hc.2.2.2 k

 theorem physicalProjectionClock_of_gaussian_cuts (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c a D : ℝ}
    (hc : OrderedSteps c steps) (ha : 0 ≤ a) {fork q d e : ℕ}
    (hf : fork ≤ q) (hqd : q ≤ d) (hde : d ≤ e) (he : e ≤ steps.length)
    (ham : a ≤ physicalCutMass c steps q)
    (hclock : ∀ V : Fin n → ℝ, AlignedFieldClock (fieldProjectionDirection n V) D (cutSlice steps q d)) :
    PhysicalProjectionClock n steps fork d e a D := by
  have horder : OrderedSteps a (cutSlice steps q d++(cutSlice steps d e++steps.drop e)) := by
    rw [cutSlice_append_drop steps hde,cutSlice_append_drop steps hqd]
    exact (orderedSteps_drop_cutMass steps hc q).lower ha ham
  have hh := PhysicalProjectionClock.gaussian (steps.take fork) (steps.drop e)
    (cutSlice steps d e) (cutSlice steps q d) (cutSlice steps fork q) a D horder hclock
  have hlen : (steps.take fork).length = fork := List.length_take_of_le (by omega)
  have hskip : (cutSlice steps fork q ++ cutSlice steps q d).length = d-fork := by
    rw [List.length_append,length_cutSlice steps hf (by omega),length_cutSlice steps hqd (by omega)]
    omega
  rw [take_append_slices steps hf hqd hde,hlen,hskip,length_cutSlice steps hde he] at hh
  convert hh using 1 <;> omega

 theorem physicalProjectionClock_of_terminal_cuts (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c a D : ℝ}
    (hc : OrderedSteps c steps) (ha : 0 ≤ a) {fork q d : ℕ}
    (hf : fork ≤ q) (hqd : q ≤ d) (hd : d ≤ steps.length)
    (ham : a ≤ physicalCutMass c steps q)
    (hclock : ∀ V : Fin n → ℝ, AlignedFieldClock (fieldProjectionDirection n V) D (cutSlice steps q d)) :
    PhysicalProjectionClock n steps fork d (steps.length+1) a D := by
  have horder : OrderedSteps a (cutSlice steps q d++steps.drop d) := by
    rw [cutSlice_append_drop steps hqd]
    exact (orderedSteps_drop_cutMass steps hc q).lower ha ham
  have hh := PhysicalProjectionClock.terminal (steps.take fork) (steps.drop d)
    (cutSlice steps q d) (cutSlice steps fork q) a D horder hclock
  have hfull : steps.take fork ++ ((cutSlice steps fork q++cutSlice steps q d)++steps.drop d) = steps := by
    rw [List.append_assoc,cutSlice_append_drop steps hqd,cutSlice_append_drop steps hf,List.take_append_drop]
  have hlen : (steps.take fork).length = fork := List.length_take_of_le (by omega)
  have hskip : (cutSlice steps fork q++cutSlice steps q d).length = d-fork := by
    rw [List.length_append,length_cutSlice steps hf (by omega),length_cutSlice steps hqd hd]
    omega
  rw [hfull,hlen,hskip] at hh
  convert hh using 1
  omega

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def physicalFieldDuration {ι : Type} (d : GaussianStep ι → ℝ≥0)
    (steps : List (GaussianStep ι)) : ℝ := ((steps.map d).sum : ℝ≥0)

theorem physicalFieldDuration_nonneg {ι : Type} (d : GaussianStep ι → ℝ≥0)
    (steps : List (GaussianStep ι)) : 0 ≤ physicalFieldDuration d steps := NNReal.coe_nonneg _

@[simp] theorem physicalFieldDuration_append {ι : Type} (d : GaussianStep ι → ℝ≥0)
    (steps tail : List (GaussianStep ι)) :
    physicalFieldDuration d (steps++tail) = physicalFieldDuration d steps+physicalFieldDuration d tail := by
  simp [physicalFieldDuration]

theorem physicalFieldDuration_take_le {ι : Type} (d : GaussianStep ι → ℝ≥0)
    (steps : List (GaussianStep ι)) (k : ℕ) :
    physicalFieldDuration d (steps.take k) ≤ physicalFieldDuration d steps := by
  have hh := physicalFieldDuration_append d (steps.take k) (steps.drop k)
  rw [List.take_append_drop] at hh
  linarith [physicalFieldDuration_nonneg d (steps.drop k)]

theorem physicalFieldDuration_drop_le {ι : Type} (d : GaussianStep ι → ℝ≥0)
    (steps : List (GaussianStep ι)) (k : ℕ) :
    physicalFieldDuration d (steps.drop k) ≤ physicalFieldDuration d steps := by
  have hh := physicalFieldDuration_append d (steps.take k) (steps.drop k)
  rw [List.take_append_drop] at hh
  linarith [physicalFieldDuration_nonneg d (steps.take k)]

theorem physicalFieldDuration_slice_le {ι : Type} (d : GaussianStep ι → ℝ≥0)
    (steps : List (GaussianStep ι)) (a b : ℕ) :
    physicalFieldDuration d (cutSlice steps a b) ≤ physicalFieldDuration d steps :=
  (physicalFieldDuration_take_le d (steps.drop a) (b-a)).trans (physicalFieldDuration_drop_le d steps a)

theorem physicalFieldDuration_slice_eq {ι : Type} (d : GaussianStep ι → ℝ≥0)
    (steps : List (GaussianStep ι)) {a b : ℕ} (hab : a ≤ b) :
    physicalFieldDuration d (cutSlice steps a b) =
      physicalFieldDuration d (steps.take b)-physicalFieldDuration d (steps.take a) := by
  have hh : steps.take b = steps.take a++cutSlice steps a b := by
    simpa only [Nat.add_sub_of_le hab,cutSlice] using (List.take_add (l := steps) (i := a) (j := b-a))
  rw [hh,physicalFieldDuration_append]
  ring

theorem physicalFieldDuration_prefix_monotone {ι : Type} (d : GaussianStep ι → ℝ≥0)
    (steps : List (GaussianStep ι)) : Monotone (fun k => physicalFieldDuration d (steps.take k)) := by
  intro a b hab
  have hh := physicalFieldDuration_slice_eq d steps hab
  linarith [physicalFieldDuration_nonneg d (cutSlice steps a b)]

theorem alignedFieldClock_slice (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (d : GaussianStep (FeatureIndex n) → ℝ≥0)
    (hd : ∀ st ∈ steps, ∀ i : Fin n, st.2 (Sum.inl i) = d st)
    (a b : ℕ) (V : Fin n → ℝ) :
    AlignedFieldClock (fieldProjectionDirection n V)
      (physicalFieldDuration d (cutSlice steps a b)) (cutSlice steps a b) := by
  let L : List (ClockedStep (FeatureIndex n)) := (cutSlice steps a b).map fun st => (d st,st)
  have hal : ClockAligned (fieldProjectionDirection n V) L := by
    intro p hp i hi
    obtain ⟨st,hst,rfl⟩ := List.mem_map.mp hp
    have hmem : st ∈ steps := List.mem_of_mem_drop (List.mem_of_mem_take hst)
    rcases i with i | i
    · exact hd st hmem i
    · exact (hi rfl).elim
  have hh := hal.toAligned
  have hforget : forgetClock L = cutSlice steps a b := by
    simp only [L,forgetClock,List.map_map]
    exact List.map_id' _
  have hduration : (clockDuration L : ℝ) = physicalFieldDuration d (cutSlice steps a b) := by
    simp only [L,clockDuration,physicalFieldDuration,List.map_map]
    rfl
  rw [hforget,hduration] at hh
  exact hh

end SKFluctuations

end

end OAI
