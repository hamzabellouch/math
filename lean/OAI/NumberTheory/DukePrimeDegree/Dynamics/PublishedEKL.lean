import OAI.NumberTheory.PrimePackets.RootInvariance
import OAI.NumberTheory.DukePrimeDegree.MainConditional

namespace OAI

/-!
# Haar rigidity from root-leaf symmetries

Projective normalization can be removed from root-leaf symmetries, and
nontrivial root periods yield invariance under the corresponding
unipotent group. Haar measure follows from all root periods, or from
a single root and a transitive prime-degree symmetry group.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree

open PrimeDegreePackets

/-- A projective period of a leaf with zero logarithmic multiplier is an
ordinary period. -/
lemma leaf_period_of_projective_multiplier_zero
    (ν : Measure ℝ) (p : ℝ × ℝ) (hp : projectiveLeafPeriod ν p) (hzero : p.2 = 0) :
    p.1 ∈ realLeafPeriods ν := by
  change ν.map (fun x => x + p.1) = ν
  simpa only [projectiveLeafPeriod, hzero, Real.exp_zero, ENNReal.ofReal_one, one_smul] using hp

/-- Equality with a rebased normalized leaf yields a projective period.
The normalizing scalar is recovered from the unit-ball mass. -/
lemma projectivePeriod_of_based_fixed
    (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (hunit : ν (Metric.ball 0 1) = 1)
    (t : ℝ) (hfixed : basedRealMeasure ν t = ν) :
    projectiveLeafPeriod ν (-t, Real.log (ν (Metric.ball t 1)).toReal) := by
  let m := ν (Metric.ball t 1)
  have hmul : m⁻¹ * m = 1 := by
    have he := congrArg (fun ρ : Measure ℝ => ρ (Metric.ball 0 1)) hfixed
    simpa only [basedRealMeasure, anchorNormalize, Measure.smul_apply,
      smul_eq_mul, centerRealMeasure_ball, hunit] using he
  have hm0 : m ≠ 0 := by
    intro hm
    simp [hm] at hmul
  have hmT : m ≠ ∞ := measure_ball_lt_top.ne
  have hcenter : centerRealMeasure ν t = m • ν := by
    have hs := congrArg (fun ρ : Measure ℝ => m • ρ) hfixed
    simp only [basedRealMeasure, anchorNormalize, centerRealMeasure_ball] at hs
    change m • (m⁻¹ • centerRealMeasure ν t) = m • ν at hs
    rw [smul_smul, ENNReal.mul_inv_cancel hm0 hmT, one_smul] at hs
    exact hs
  change ν.map (fun x => x + -t) = ENNReal.ofReal (Real.exp (Real.log m.toReal)) • ν
  rw [Real.exp_log (ENNReal.toReal_pos hm0 hmT), ENNReal.ofReal_toReal hmT]
  simpa only [centerRealMeasure, Homeomorph.coe_subRight, sub_eq_add_neg] using hcenter

/-- For a finite invariant ambient measure, the full diagonal scaling
covariance forces every projective root-leaf period to have multiplier
one. This is the normalization step needed by the low-entropy argument. -/
theorem ae_intrinsic_projective_multiplier_zero
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, ∀ p : ℝ × ℝ,
      projectiveLeafPeriod (intrinsicRootLeaf hij μ x) p → p.2 = 0 := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let κ := intrinsicRootKernel hij μ hfree
  have heq : ∀ᵐ x ∂μ, κ x = intrinsicRootLeaf hij μ x :=
    ae_intrinsicRootKernel_eq hij μ hfree
  have hp : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r) := by
    filter_upwards [heq, ae_intrinsicRootLeaf_ball_pos hij μ hfree] with x hx hp
    rwa [hx]
  have H := ae_projectiveLeafPeriod_multiplier_zero μ κ hp (by
    intro c hc
    let T : X (d + 1) → X (d + 1) :=
      fun x => rightAction x (rootCanonicalFlow d j (Real.log c))
    have hT : MeasurePreserving T μ μ :=
      rootCanonicalFlow_preserving d j (Real.log c) μ hA
    refine ⟨T, hT, ?_⟩
    have heqmap : ∀ᵐ x ∂μ.map T, κ x = intrinsicRootLeaf hij μ x := by
      rw [hT.map_eq]
      exact heq
    have heqT : ∀ᵐ x ∂μ, κ (T x) = intrinsicRootLeaf hij μ (T x) :=
      ae_of_ae_map hT.measurable.aemeasurable heqmap
    filter_upwards [heq, heqT,
      ae_intrinsicRootLeaf_canonical d hij μ hA (Real.log c)] with x hx hTx hcq
    rw [hTx, hx]
    simpa only [Real.exp_log hc, T] using hcq)
  filter_upwards [heq, H] with x hx h
  simpa only [hx] using h

/-- Nontrivial projective root-leaf symmetries already imply exact
unipotent invariance; no multiplier has to be supplied separately. -/
theorem root_invariant_of_projective_leaf_symmetry
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hsym : ∀ᵐ x ∂μ, ∃ p : ℝ × ℝ, p.1 ≠ 0 ∧
      projectiveLeafPeriod (intrinsicRootLeaf hij μ x) p) (a : ℝ) :
    μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ := by
  apply root_invariant_of_nonzero_intrinsic_period d hij μ hA
  filter_upwards [hsym, ae_intrinsic_projective_multiplier_zero d hij μ hA] with x hx hzero
  obtain ⟨p, hp, hper⟩ := hx
  exact ⟨p.1, hp, leaf_period_of_projective_multiplier_zero _ p hper (hzero p hper)⟩

/-- Positive mean root information rules out the Dirac alternative in
an ergodic diagonal component. This supplies the nonatomic half of the
leafwise-constancy criterion from an entropy contribution. -/
theorem ae_atomless_of_positive_rootInformation
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hpos : 0 < rootInformationMean hij μ 1) :
    ∀ᵐ x ∂μ, NullSingletonClass (intrinsicRootLeaf hij μ x) := by
  rcases intrinsicRootLeaf_ergodic_alternative d hij μ with h | h
  · exact h
  · have hA (u : LogCoordinates d) :
        μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
      (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
    have hz := (rootInformationMean_eq_zero_iff_dirac d hij μ hA).mpr h
    exact (hpos.ne' hz).elim

/-- A non-atomic root leaf that is almost everywhere unchanged when
rebased has a nontrivial translation symmetry. -/
theorem root_invariant_of_leafwise_constant_nonatomic
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hatom : ∀ᵐ x ∂μ, NullSingletonClass (intrinsicRootLeaf hij μ x))
    (hfixed : ∀ᵐ x ∂μ, ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
      intrinsicRootLeaf hij μ (rightAction x
        (Matrix.SpecialLinearGroup.transvection hij t)) = intrinsicRootLeaf hij μ x)
    (a : ℝ) :
    μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ := by
  apply root_invariant_of_projective_leaf_symmetry d hij μ hA
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  filter_upwards [hatom, hfixed, ae_intrinsicRootLeaf_rebase hij μ hfree,
    ae_intrinsicRootLeaf_spec hij μ hfree] with x hatom hfixed hrebase hspec
  let ν := intrinsicRootLeaf hij μ x
  let : IsLocallyFiniteMeasure ν := hspec.1
  let : NullSingletonClass ν := hatom
  have hunit : ν (Metric.ball 0 1) = 1 := hspec.2
  let : NeZero ν := ⟨by
    intro he
    have hh := congrArg (fun ρ : Measure ℝ => ρ (Metric.ball 0 1)) he
    rw [hunit] at hh
    simp at hh⟩
  have hnzero : ∀ᵐ t ∂ν, t ≠ 0 := by
    rw [ae_iff]
    simp
  obtain ⟨t, ht, htfix, htzero⟩ := (hrebase.and (hfixed.and hnzero)).exists
  have hbased : basedRealMeasure ν t = ν := ht.symm.trans htfix
  refine ⟨(-t, Real.log (ν (Metric.ball t 1)).toReal), neg_ne_zero.mpr htzero, ?_⟩
  exact projectivePeriod_of_based_fixed ν hunit t hbased

/-- Full root-leaf symmetry identifies Haar probability directly through
the elementary-generation theorem for the special linear group. -/
theorem isHaar_of_projective_leaf_symmetries
    (d : ℕ) (hd : 1 ≤ d) (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hsym : ∀ (i j : Fin (d + 1)) (hij : i ≠ j),
      ∀ᵐ x ∂μ, ∃ p : ℝ × ℝ, p.1 ≠ 0 ∧
        projectiveLeafPeriod (intrinsicRootLeaf hij μ x) p) :
    IsHaarProbability μ := by
  refine ⟨inferInstance, right_invariant_of_all_roots (by omega) μ ?_⟩
  intro i j hij a
  exact root_invariant_of_projective_leaf_symmetry d hij μ hA (hsym i j hij) a

/-- In prime degree a transitive symmetry of the root-invariance relation
propagates one nontrivial projective leaf symmetry to Haar invariance. -/
theorem isHaar_of_prime_root_symmetries
    (d : ℕ) (hprime : (d + 1).Prime) (hd : 1 ≤ d)
    (J : Type*) [Group J] [MulAction J (Fin (d + 1))]
    [MulAction.IsPretransitive J (Fin (d + 1))]
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hperm : ∀ (g : J) i j, rootInvarianceRelation μ i j →
      rootInvarianceRelation μ (g • i) (g • j))
    {i j : Fin (d + 1)} (hij : i ≠ j)
    (hsym : ∀ᵐ x ∂μ, ∃ p : ℝ × ℝ, p.1 ≠ 0 ∧
      projectiveLeafPeriod (intrinsicRootLeaf hij μ x) p) :
    IsHaarProbability μ := by
  refine ⟨inferInstance, full_invariance_of_prime_root_symmetries
    (by omega) hprime J μ hperm ?_⟩
  refine ⟨i, j, hij, Or.inr ⟨hij, ?_⟩⟩
  intro a
  exact root_invariant_of_projective_leaf_symmetry d hij μ hA hsym a

end DukePrimeDegree

end OAI
