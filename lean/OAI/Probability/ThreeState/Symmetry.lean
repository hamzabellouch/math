import Mathlib
import OAI.Probability.ThreeState.FixedPoints

namespace OAI

/-! Spin symmetry and measure identities for posterior fixed points. -/

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

lemma pmf_map_equiv_apply {α β : Type*} (p : PMF α) (e : α ≃ β) (a : α) :
    p.map e (e a) = p a := by simp [PMF.map_apply]

lemma uniformSpin_map (π : Equiv.Perm Spin) : uniformSpin.map π = uniformSpin := by
  apply PMF.ext
  intro j
  obtain ⟨i,rfl⟩ := π.surjective j
  rw [pmf_map_equiv_apply]
  simp [uniformSpin, PMF.ofFintype_apply]

lemma channelPMF_map (lam : ℝ) (h : Admissible lam) (π : Equiv.Perm Spin) (i : Spin) :
    (channelPMF lam h i).map π = channelPMF lam h (π i) := by
  apply PMF.ext
  intro j
  obtain ⟨k,rfl⟩ := π.surjective j
  rw [pmf_map_equiv_apply]
  simp [channelPMF, PMF.ofFintype_apply, channel]

noncomputable def permMessage (π : Equiv.Perm Spin) (m : Message) : Message :=
  ⟨fun i => m (π.symm i), by
    constructor
    · intro i; exact Message.nonneg m _
    · rw [Equiv.sum_comp π.symm]
      exact Message.sum m⟩

lemma continuous_permMessage (π : Equiv.Perm Spin) : Continuous (permMessage π) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_apply (π.symm i)).comp continuous_subtype_val

noncomputable def renameOrdered : (n : ℕ) → Equiv.Perm Spin → Equiv.Perm (OrderedObservation n)
  | 0, π => π
  | n+1, π => Equiv.sigmaCongrRight (fun k => Equiv.piCongrRight (fun _ : Fin k => renameOrdered n π))

lemma orderedLaw_rename (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (π : Equiv.Perm Spin) (n : ℕ) (i : Spin) :
    (orderedLaw offspring lam h n i).map (renameOrdered n π) = orderedLaw offspring lam h n (π i) := by
  induction n generalizing i with
  | zero => exact PMF.pure_map _ _
  | succ n ih =>
    simp only [orderedLaw, PMF.map_bind, PMF.map_comp]
    apply congrArg (PMF.bind offspring)
    funext k
    change (iidVector ((channelPMF lam h i).bind (orderedLaw offspring lam h n)) k).map
      ((Sigma.mk (β := fun k => Fin k → OrderedObservation n) k) ∘
        (fun v : Fin k → OrderedObservation n => renameOrdered n π ∘ v)) = _
    rw [← PMF.map_comp, iidVector_map]
    congr 2
    rw [PMF.map_bind]
    simp_rw [ih]
    change (channelPMF lam h i).bind ((orderedLaw offspring lam h n) ∘ π) = _
    rw [← PMF.bind_map, channelPMF_map]

lemma marginal_equivariant {α : Type*} (law : Spin → PMF α) (π : Equiv.Perm Spin)
    (e : Equiv.Perm α) (he : ∀ i, (law i).map e = law (π i)) :
    (marginal law).map e = marginal law := by
  rw [marginal, PMF.map_bind]
  simp_rw [he]
  change uniformSpin.bind (law ∘ π) = _
  rw [← PMF.bind_map, uniformSpin_map]

lemma posterior_equivariant {α : Type*} (law : Spin → PMF α) (π : Equiv.Perm Spin)
    (e : Equiv.Perm α) (he : ∀ i, (law i).map e = law (π i)) (y : α) (i : Spin) :
    posterior law (e y) (π i) = posterior law y i := by
  have hm : marginal law (e y) = marginal law y := by
    calc
      marginal law (e y) = (marginal law).map e (e y) := by rw [marginal_equivariant law π e he]
      _ = _ := pmf_map_equiv_apply _ _ _
  have hi : law (π i) (e y) = law i y := by
    rw [← he i]
    exact pmf_map_equiv_apply _ _ _
  simp only [posterior, hm, hi]

lemma likelihood_equivariant {α : Type*} (law : Spin → PMF α) (π : Equiv.Perm Spin)
    (e : Equiv.Perm α) (he : ∀ i, (law i).map e = law (π i)) (y : α) :
    likelihood law (e y) = permMessage π (likelihood law y) := by
  apply Subtype.ext
  funext i
  have hh := posterior_equivariant law π e he y (π.symm i)
  simp only [Equiv.apply_symm_apply] at hh
  change 3*posterior law (e y) i = 3*posterior law y (π.symm i)
  rw [hh]

lemma likelihoodPMF_equivariant {α : Type*} (law : Spin → PMF α) (π : Equiv.Perm Spin)
    (e : Equiv.Perm α) (he : ∀ i, (law i).map e = law (π i)) :
    (likelihoodPMF law).map (permMessage π) = likelihoodPMF law := by
  rw [likelihoodPMF, PMF.map_comp]
  have hh : permMessage π ∘ likelihood law = likelihood law ∘ e := by
    funext y
    exact (likelihood_equivariant law π e he y).symm
  rw [hh, ← PMF.map_comp, marginal_equivariant law π e he]

 
def SpinSymmetric (Q : ProbabilityMeasure Message) : Prop :=
  ∀ π : Equiv.Perm Spin, Q.map (permMessage π) = Q

lemma ordered_likelihood_symmetric (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) : SpinSymmetric (likelihoodLaw (orderedLaw offspring lam h n)) := by
  intro π
  apply Subtype.ext
  change (likelihoodPMF (orderedLaw offspring lam h n)).toMeasure.map (permMessage π) = _
  rw [PMF.toMeasure_map _ _ (continuous_permMessage π).measurable]
  rw [likelihoodPMF_equivariant _ π (renameOrdered n π)
    (fun i => orderedLaw_rename offspring lam h π n i)]
  rfl

lemma symmetric_limit {Qn : ℕ → ProbabilityMeasure Message} {Q : ProbabilityMeasure Message}
    (hn : ∀ n, SpinSymmetric (Qn n)) (hlim : Tendsto Qn atTop (𝓝 Q)) : SpinSymmetric Q := by
  intro π
  have hh := ((ProbabilityMeasure.continuous_map (continuous_permMessage π)).tendsto Q).comp hlim
  have he : (fun n => (Qn n).map (permMessage π)) = Qn :=
    funext (fun n => hn n π)
  simp only [Function.comp_def, he] at hh
  exact tendsto_nhds_unique hh hlim

lemma ordered_exists_symmetric_fixedpoint (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    ∃ Q : ProbabilityMeasure Message, IsPosteriorFixedPoint offspring lam h Q ∧ SpinSymmetric Q ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => likelihoodLaw (orderedLaw offspring lam h (φ n))) atTop (𝓝 Q) := by
  obtain ⟨Q,hQ,φ,hφ,hlim⟩ := ordered_exists_fixedpoint offspring lam h
  exact ⟨Q,hQ,symmetric_limit (fun n => ordered_likelihood_symmetric offspring lam h (φ n)) hlim,φ,hφ,hlim⟩

end ThreeState

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

lemma measurable_combineMessage (lam : ℝ) (h : Admissible lam) (n : ℕ) :
    Measurable (combineMessage lam h : (Fin n → Message) → Message) := by
  apply Measurable.subtype_mk
  apply Measurable.of_eval
  intro i
  have he : (fun m : Fin n → Message => combineMessage lam h m i) =
      (fun m => if normalizer lam h m = 0 then uninformative i else
        productWeight lam h m i / normalizer lam h m) := by
    funext m
    by_cases hm : normalizer lam h m = 0 <;> simp [combineMessage, hm]
  change Measurable (fun m : Fin n → Message => combineMessage lam h m i)
  rw [he]
  exact Measurable.ite ((continuous_normalizer lam h n).measurable (measurableSet_singleton 0))
    measurable_const ((continuous_productWeight lam h n i).measurable.div
      (continuous_normalizer lam h n).measurable)

 
noncomputable def degreeInput (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message) (n : ℕ) :
    Measure (Fin n → Message) :=
  (iidMeasure Q n : Measure (Fin n → Message)).withDensity (fun m => ENNReal.ofReal (normalizer lam h m))

lemma degreeInput_probability (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message)
    (hQ : Balanced Q) (n : ℕ) : IsProbabilityMeasure (degreeInput lam h Q n) := by
  constructor
  rw [degreeInput, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((continuous_normalizer lam h n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (Eventually.of_forall (normalizer_nonneg lam h)), integral_normalizer lam h Q hQ n]
  simp

noncomputable def degreeOutput (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message) (n : ℕ) :
    Measure Message := Measure.map (combineMessage lam h) (degreeInput lam h Q n)

lemma degreeOutput_probability (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message)
    (hQ : Balanced Q) (n : ℕ) : IsProbabilityMeasure (degreeOutput lam h Q n) := by
  let := degreeInput_probability lam h Q hQ n
  constructor
  rw [degreeOutput, Measure.map_apply (measurable_combineMessage lam h n) MeasurableSet.univ]
  simp

 
noncomputable def densityEvolution (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (Q : ProbabilityMeasure Message) : Measure Message :=
  Measure.sum (fun n => offspring n • degreeOutput lam h Q n)

lemma densityEvolution_probability (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) : IsProbabilityMeasure (densityEvolution offspring lam h Q) := by
  constructor
  rw [densityEvolution, Measure.sum_apply _ MeasurableSet.univ]
  convert offspring.tsum_coe using 1
  apply tsum_congr
  intro n
  let := degreeOutput_probability lam h Q hQ n
  simp

lemma integral_degreeOutput (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message) (n : ℕ)
    (f : Message → ℝ) (hf : Measurable f) :
    ∫ m, f m ∂degreeOutput lam h Q n =
      ∫ m, normalizer lam h m * f (combineMessage lam h m) ∂(iidMeasure Q n : Measure (Fin n → Message)) := by
  rw [degreeOutput, integral_map (measurable_combineMessage lam h n).aemeasurable hf.aestronglyMeasurable,
    degreeInput, integral_withDensity_eq_integral_toReal_smul
    ((continuous_normalizer lam h n).measurable.ennreal_ofReal)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with m
  simp [ENNReal.toReal_ofReal (normalizer_nonneg lam h m)]

lemma integral_densityEvolution_continuous (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) (f : C(Message,ℝ)) :
    ∫ m, f m ∂densityEvolution offspring lam h Q =
      mean offspring (fun n => degreeTest lam h n f Q) := by
  let := densityEvolution_probability offspring lam h Q hQ
  have hi : Integrable f (densityEvolution offspring lam h Q) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [densityEvolution, integral_sum_measure hi]
  unfold mean
  apply tsum_congr
  intro n
  rw [integral_smul_measure, integral_degreeOutput lam h Q n f f.continuous.measurable]
  rfl

lemma fixedpoint_measure (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint offspring lam h Q) :
    (Q : Measure Message) = densityEvolution offspring lam h Q := by
  let := densityEvolution_probability offspring lam h Q hQ.1
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  change (∫ m, f.toContinuousMap m ∂(Q : Measure Message)) =
    ∫ m, f.toContinuousMap m ∂densityEvolution offspring lam h Q
  rw [integral_densityEvolution_continuous offspring lam h Q hQ.1 f.toContinuousMap]
  exact hQ.2 f.toContinuousMap

end ThreeState

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

lemma ae_degreeOutput_of_forall (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message) (n : ℕ)
    (P : Message → Prop) (hP : MeasurableSet {m | P m})
    (hp : ∀ m : Fin n → Message, P (combineMessage lam h m)) :
    ∀ᵐ m ∂degreeOutput lam h Q n, P m := by
  exact (ae_map_iff (measurable_combineMessage lam h n).aemeasurable hP).mpr
    (Eventually.of_forall hp)

lemma ae_fixedpoint_of_output (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint offspring lam h Q)
    (P : Message → Prop) (hP : MeasurableSet {m | P m})
    (hp : ∀ n (m : Fin n → Message), P (combineMessage lam h m)) :
    ∀ᵐ m ∂(Q : Measure Message), P m := by
  rw [fixedpoint_measure offspring lam h Q hQ, densityEvolution]
  apply Measure.ae_sum_iff.mpr
  intro n
  exact Measure.ae_smul_measure (ae_degreeOutput_of_forall lam h Q n P hP (hp n)) (offspring n)

lemma integrable_degreeOutput_bound (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message)
    (hQ : Balanced Q) (n : ℕ) (f : Message → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ m : Fin n → Message, |f (combineMessage lam h m)| ≤ C) :
    Integrable f (degreeOutput lam h Q n) ∧
      (∫ m, ‖f m‖ ∂degreeOutput lam h Q n) ≤ C := by
  let := degreeOutput_probability lam h Q hQ n
  have hb : ∀ᵐ m ∂degreeOutput lam h Q n, ‖f m‖ ≤ C :=
    ae_degreeOutput_of_forall lam h Q n _ (measurableSet_le hf.norm measurable_const)
      (fun m => by simpa only [Real.norm_eq_abs] using hC m)
  have hi : Integrable f (degreeOutput lam h Q n) :=
    (integrable_const C).mono' hf.aestronglyMeasurable hb
  refine ⟨hi,?_⟩
  calc
    (∫ m, ‖f m‖ ∂degreeOutput lam h Q n) ≤ ∫ _, C ∂degreeOutput lam h Q n :=
      integral_mono_ae hi.norm (integrable_const C) hb
    _ = C := by simp

lemma integrable_fixedpoint_of_growth (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint offspring lam h Q)
    (f : Message → ℝ) (hf : Measurable f) (C : ℕ → ℝ) (hC : HasMean offspring C)
    (hb : ∀ n (m : Fin n → Message), |f (combineMessage lam h m)| ≤ C n) :
    Integrable f (Q : Measure Message) := by
  rw [fixedpoint_measure offspring lam h Q hQ, densityEvolution]
  apply integrable_sum_measure
  · intro n
    exact (integrable_degreeOutput_bound lam h Q hQ.1 n f hf (C n) (hb n)).1.smul_measure (offspring.apply_ne_top n)
  · apply hC.of_norm_bounded
    intro n
    rw [integral_smul_measure, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (ENNReal.toReal_nonneg)]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left
      (integrable_degreeOutput_bound lam h Q hQ.1 n f hf (C n) (hb n)).2 (mass_nonneg offspring n)

lemma integral_fixedpoint (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint offspring lam h Q)
    (f : Message → ℝ) (hf : Measurable f) (hi : Integrable f (Q : Measure Message)) :
    ∫ m, f m ∂(Q : Measure Message) = mean offspring (fun n =>
      ∫ m, normalizer lam h m * f (combineMessage lam h m) ∂(iidMeasure Q n : Measure (Fin n → Message))) := by
  rw [fixedpoint_measure offspring lam h Q hQ] at hi ⊢
  rw [densityEvolution, integral_sum_measure hi]
  unfold mean
  apply tsum_congr
  intro n
  rw [integral_smul_measure, integral_degreeOutput lam h Q n f hf]
  rfl

end ThreeState

end OAI
