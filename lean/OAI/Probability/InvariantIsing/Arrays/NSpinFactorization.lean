import OAI.Probability.InvariantIsing.Arrays.NSpinCascade
import OAI.Probability.InvariantIsing.Fields.SpinFactorization
import OAI.Probability.InvariantIsing.Fields.CascadeTilt
import OAI.Probability.InvariantIsing.Fields.FieldCascade

namespace OAI

/-! Site factorization through the finite Gaussian backward recursion. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

theorem vectorCascade_logCosh_sum (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (c z : Fin N → ℝ) :
    IsingPerceptron.cascadeRecursion n b (fun i => vectorGaussianLaw N (v i))
      (fun _ p => p.1 + p.2) (fun y => ∑ i, Real.log (Real.cosh (c i + y i))) z =
    ∑ i, IsingPerceptron.cascadeRecursion n b (fun j => gaussianCascadeMarks (v := v) j)
      (fun _ p => p.1 + p.2) (fun y => Real.log (Real.cosh y)) (c i + z i) := by
  induction n generalizing b v z with
  | zero => rfl
  | succ n ih =>
    let bs := fun j => b (j + 1)
    let vs := fun j => v (j + 1)
    let F := IsingPerceptron.cascadeRecursion n bs (fun j => gaussianCascadeMarks vs j)
      (fun _ p => p.1 + p.2) (fun y => Real.log (Real.cosh y))
    have hbs : ∀ j < n, 0 < bs j := fun j hj => hb (j + 1) (by omega)
    have hm : Measurable F := IsingPerceptron.measurable_cascadeRecursion n bs
      (fun j => gaussianCascadeMarks vs j) (fun _ => measurable_fst.add measurable_snd)
      IsingPerceptron.measurable_logCosh
    have hg : IsingPerceptron.HasLinearGrowth F :=
      IsingPerceptron.cascadeRecursion_linearGrowth n bs (fun j => gaussianCascadeMarks vs j)
        (fun j _ => IsingPerceptron.gaussianReal_exponentialNormMoments 0 (vs j))
        IsingPerceptron.measurable_logCosh IsingPerceptron.logCosh_linearGrowth hbs
    have he : (fun g : Fin N → ℝ => IsingPerceptron.cascadeRecursion n bs
        (fun j => vectorGaussianLaw N (vs j)) (fun _ p => p.1 + p.2)
        (fun y => ∑ i, Real.log (Real.cosh (c i + y i))) (z + g)) =
        (fun g => ∑ i, F ((c i + z i) + g i)) := by
      funext g
      rw [ih bs vs hbs]
      simp only [F, Pi.add_apply, add_assoc]
    change IsingPerceptron.logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ))
      (fun g => IsingPerceptron.cascadeRecursion n bs
        (fun j => vectorGaussianLaw N (vs j)) (fun _ p => p.1 + p.2)
        (fun y => ∑ i, Real.log (Real.cosh (c i + y i))) (z + g)) =
      ∑ i, IsingPerceptron.logMean (b 0) (gaussianReal 0 (v 0))
        (fun g => F ((c i + z i) + g))
    rw [he]
    exact IsingPerceptron.logMean_independent_sum (fun _ : Fin N => gaussianReal 0 (v 0))
      (fun i g => F ((c i + z i) + g)) (hb 0 (by omega)).ne'
      (fun _ => hm.comp (measurable_const.add measurable_id))
      (fun i => IsingPerceptron.integrable_exp_of_linearGrowth _
        (IsingPerceptron.gaussianReal_exponentialNormMoments 0 (v 0))
        (hm.comp (measurable_const.add measurable_id)) (hg.add_left (c i + z i)) (b 0))

theorem rotatedCascadeValue_zero_interaction {N : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → ℝ≥0) (hb : IsingPerceptron.CascadeExponents n b)
    (U : Rotation N) (c z : Fin N → ℝ) :
    rotatedCascadeValue n b v (fun _ => 0) U c z =
      ∑ i, ((List.ofFn (fun j : Fin n => (b j, (v j : ℝ)))).foldr
        (fun av f => gaussianOperator av.1 av.2 f) (fun y => Real.log (Real.cosh y)))
        (c i + z i) := by
  have ht : rotatedFieldTerminal (fun _ : Fin N => 0) U c =
      (fun y => ∑ i, Real.log (Real.cosh (c i + y i))) := by
    funext y
    simp only [rotatedFieldTerminal, rotatedEnergy_constant, zero_mul, zero_div, zero_add]
    simpa only [Pi.add_apply] using logPartition_fieldEnergy (c + y)
  unfold rotatedCascadeValue
  rw [ht, vectorCascade_logCosh_sum N n b v (fun i hi => (hb.1 i hi).1)]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (gaussianCascadeRecursion_eq_fold n b v
    (fun j hj => (hb.1 j hj).1.ne') IsingPerceptron.measurable_logCosh) (c i + z i)

lemma integrable_gaussianReal_of_linearGrowth (v : ℝ≥0) {F : ℝ → ℝ}
    (hF : Measurable F) (hg : IsingPerceptron.HasLinearGrowth F) :
    Integrable F (gaussianReal 0 v) := by
  obtain ⟨C, L, _, hL, hbound⟩ := hg
  have hi := (integrable_const C).add
    ((IsingPerceptron.gaussianReal_exponentialNormMoments 0 v 1).const_mul L)
  apply hi.mono' hF.aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change |F z| ≤ C + L * Real.exp (1 * ‖z‖)
    rw [one_mul]
    exact (hbound z).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp ‖z‖)) hL))

theorem rotatedEnrichedPressure_zero_interaction {N : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → ℝ≥0) (root : ℝ≥0) (hb : IsingPerceptron.CascadeExponents n b)
    (U : Rotation N) (c : Fin N → ℝ) :
    rotatedEnrichedPressure n b v root (fun _ => 0) U c =
      (N : ℝ)⁻¹ * ∑ i, gaussianOperator 0 root
        ((List.ofFn (fun j : Fin n => (b j, (v j : ℝ)))).foldr
          (fun av f => gaussianOperator av.1 av.2 f) (fun y => Real.log (Real.cosh y))) (c i) := by
  let F := IsingPerceptron.cascadeRecursion n b (fun j => gaussianCascadeMarks v j)
    (fun _ p => p.1 + p.2) (fun y => Real.log (Real.cosh y))
  have hm : Measurable F := IsingPerceptron.measurable_cascadeRecursion n b
    (fun j => gaussianCascadeMarks v j) (fun _ => measurable_fst.add measurable_snd)
    IsingPerceptron.measurable_logCosh
  have hg : IsingPerceptron.HasLinearGrowth F :=
    IsingPerceptron.cascadeRecursion_linearGrowth n b (fun j => gaussianCascadeMarks v j)
      (fun j _ => IsingPerceptron.gaussianReal_exponentialNormMoments 0 (v j))
      IsingPerceptron.measurable_logCosh IsingPerceptron.logCosh_linearGrowth
      (fun j hj => (hb.1 j hj).1)
  have hfi (i : Fin N) : Integrable (fun g => F (c i + g)) (gaussianReal 0 root) :=
    integrable_gaussianReal_of_linearGrowth root (hm.comp (measurable_const.add measurable_id))
      (hg.add_left (c i))
  have hF : F = (List.ofFn (fun j : Fin n => (b j, (v j : ℝ)))).foldr
      (fun av f => gaussianOperator av.1 av.2 f) (fun y => Real.log (Real.cosh y)) :=
    gaussianCascadeRecursion_eq_fold n b v (fun j hj => (hb.1 j hj).1.ne')
      IsingPerceptron.measurable_logCosh
  unfold rotatedEnrichedPressure
  congr 1
  calc
    _ = ∫ z : Fin N → ℝ, (∑ i, F (c i + z i))
        ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        rw [rotatedCascadeValue_zero_interaction n b v hb U c z]
        simp only [hF]
    _ = ∑ i, ∫ z : Fin N → ℝ, F (c i + z i)
        ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ)) :=
      integral_finsetSum _ (fun i _ =>
        (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 root) i).integrable_comp
          (hfi i).aestronglyMeasurable |>.mpr (hfi i))
    _ = ∑ i, ∫ g, F (c i + g) ∂gaussianReal 0 root := by
      apply Finset.sum_congr rfl
      intro i _
      exact (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 root) i).hasLaw.integral_comp
        ((hm.comp (measurable_const.add measurable_id)).aestronglyMeasurable)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hs : Measurable (fun g : ℝ => F (c i + g)) :=
        hm.comp (measurable_const.add measurable_id)
      rw [integral_gaussianReal_zero_eq_standard root hs, hF]
      simp [gaussianOperator]

/-- The exact zero-time normalization in `up:zero-time`, before perturbations. -/
theorem rotatedEnrichedPressure_field_zero_time {N : ℕ} (hN : 0 < N)
    (h : FieldStep) (U : Rotation N) :
    rotatedEnrichedPressure h.depth (IsingPerceptron.chainExponent h.cut) (fieldCascadeVariance h)
      (NNReal.mk (h.height 0) (h.nonneg 0)) (fun _ => 0) U (fun _ => 0) -
      h.height (Fin.last h.depth) / 2 = fieldValue h 0 := by
  rw [rotatedEnrichedPressure_zero_interaction h.depth (IsingPerceptron.chainExponent h.cut)
    (fieldCascadeVariance h) _
    (IsingPerceptron.chainExponent_admissible h.ordered_cut h.first h.last) U (fun _ => 0)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul, fieldCascadeFold_eq_magneticRecursion]
  simp only [gaussianOperator, zero_add, NNReal.coe_mk]
  rw [ite_true]
  rw [fieldValue_eq_magneticFieldValue]
  unfold IsingPerceptron.magneticFieldValue
  have hroot : IsingPerceptron.pathAmplitude (heightSequence h) 0 = Real.sqrt (h.height 0) := by
    simp [IsingPerceptron.pathAmplitude, IsingPerceptron.pathIncrement, heightSequence]
  have hlast : heightSequence h h.depth = h.height (Fin.last h.depth) :=
    heightSequence_eq h _ le_rfl
  rw [hroot, hlast]

/-- The unperturbed contact objective cannot be negative at zero interaction. -/
theorem zero_time_contact_nonneg {N : ℕ} (hN : 0 < N) (h : FieldStep)
    (U : Rotation N) (p : OverlapPath) {S : ℝ} (hS : entropyFunctional p ≤ (S : EReal)) :
    0 ≤ -(rotatedEnrichedPressure h.depth (IsingPerceptron.chainExponent h.cut)
      (fieldCascadeVariance h) (NNReal.mk (h.height 0) (h.nonneg 0))
      (fun _ => 0) U (fun _ => 0) - h.height (Fin.last h.depth) / 2) -
      fieldPairing p h / 2 + S := by
  rw [rotatedEnrichedPressure_field_zero_time hN h U]
  have he : ((fieldValue h 0 + fieldPairing p h / 2 : ℝ) : EReal) ≤ (S : EReal) :=
    (le_iSup (fun g : FieldStep =>
      ((fieldValue g 0 + fieldPairing p g / 2 : ℝ) : EReal)) h).trans hS
  have hr : fieldValue h 0 + fieldPairing p h / 2 ≤ S := by exact_mod_cast he
  linarith

end InvariantIsing

end

end OAI
