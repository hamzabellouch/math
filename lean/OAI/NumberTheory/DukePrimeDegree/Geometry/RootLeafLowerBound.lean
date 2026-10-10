import OAI.NumberTheory.DukePrimeDegree.Geometry.RealLeafDensity

namespace OAI

/-!
# Typical root leaves have a linear lower mass bound

The property is expressed at countably many exponential radii. This makes
it measurable and allows transfer through the actual root-box disintegration.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

/-- A finite constant bounds inverse small-ball mass along integer scales. -/
def HasDiscreteLinearLowerBound (ν : Measure ℝ) : Prop :=
  ∃ C N : ℕ, ∀ n : ℕ, N ≤ n →
    ENNReal.ofReal (Real.exp (-(n : ℝ))) ≤
      (C : ℝ≥0∞) * ν (ball 0 (Real.exp (-(n : ℝ))))

lemma measurableSet_hasDiscreteLinearLowerBound :
    MeasurableSet {ν : Measure ℝ | HasDiscreteLinearLowerBound ν} := by
  simp only [HasDiscreteLinearLowerBound, Set.ofPred_exists, Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro C
  apply MeasurableSet.iUnion
  intro N
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le measurable_const
    (measurable_const.mul (Measure.measurable_coe
      (isOpen_ball (x := (0 : ℝ)) (ε := Real.exp (-(n : ℝ)))).measurableSet))

lemma ae_basedRealMeasure_discrete_lower_bound (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    ∀ᵐ x ∂ν, HasDiscreteLinearLowerBound (basedRealMeasure ν x) := by
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop),
      Eventually.of_forall fun n => Real.exp_pos _⟩
  filter_upwards [ae_real_ball_linear_lower_bound ν, ν.support_mem_ae] with x hx hs
  obtain ⟨C, hC, hbound⟩ := hx
  have hm : 0 < ν (ball x 1) :=
    (ν.mem_support_iff_forall x).mp hs _ (ball_mem_nhds _ zero_lt_one)
  have hmT : ν (ball x 1) ≠ ∞ := measure_ball_lt_top.ne
  obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt (ENNReal.mul_ne_top hC hmT)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hexp.eventually hbound)
  refine ⟨K, N, ?_⟩
  intro n hn
  have hmass : basedRealMeasure ν x (ball 0 (Real.exp (-(n : ℝ)))) =
      (ν (ball x 1))⁻¹ * ν (ball x (Real.exp (-(n : ℝ)))) := by
    change (centerRealMeasure ν x (ball 0 1))⁻¹ *
      centerRealMeasure ν x (ball 0 (Real.exp (-(n : ℝ)))) = _
    rw [centerRealMeasure_ball, centerRealMeasure_ball]
  have heq : (C * ν (ball x 1)) *
      basedRealMeasure ν x (ball 0 (Real.exp (-(n : ℝ)))) =
      C * ν (ball x (Real.exp (-(n : ℝ)))) := by
    rw [hmass, mul_assoc, ← mul_assoc (ν (ball x 1)),
      ENNReal.mul_inv_cancel hm.ne' hmT, one_mul]
  calc
    ENNReal.ofReal (Real.exp (-(n : ℝ))) ≤
        C * ν (ball x (Real.exp (-(n : ℝ)))) := hN n hn
    _ = (C * ν (ball x 1)) *
        basedRealMeasure ν x (ball 0 (Real.exp (-(n : ℝ)))) := heq.symm
    _ ≤ (K : ℝ≥0∞) * basedRealMeasure ν x (ball 0 (Real.exp (-(n : ℝ)))) :=
      mul_le_mul_left hK.le _

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

lemma ae_basedLeaf_discrete_lower_bound (A : PrimeDegreePackets.RootBox hij k)
    (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ, HasDiscreteLinearLowerBound (A.basedLeaf R μ z) := by
  let κ := A.regularLeafKernel R hAR μ hfree
  have hmeas : MeasurableSet {z : RootSlice i j k × ℝ |
      HasDiscreteLinearLowerBound (basedRealMeasure (κ z.1) z.2)} :=
    measurableSet_hasDiscreteLinearLowerBound.preimage (basedRealKernel κ).measurable
  have hbase : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ᵐ t ∂A.conditionalKernel μ s,
      HasDiscreteLinearLowerBound (basedRealMeasure (κ s) t) := by
    filter_upwards [A.ae_regularLeafKernel_eq R hAR μ hfree,
      A.ae_leafMeasure_spec R hAR μ hfree] with s hs hspec
    have hle : A.conditionalKernel μ s ≤ κ s := by
      rw [hs, ← hspec.2.2.1]
      exact Measure.restrict_le_self
    exact (ae_basedRealMeasure_discrete_lower_bound (κ s)).filter_mono
      (ae_mono hle)
  have H := Measure.ae_compProd_of_ae_ae hmeas hbase
  have H' : ∀ᵐ z ∂A.coordinateMeasure μ,
      HasDiscreteLinearLowerBound (basedRealMeasure (κ z.1) z.2) := by
    simpa only [PrimeDegreePackets.RootBox.conditionalKernel, Measure.disintegrate] using H
  have he : ∀ᵐ z ∂A.coordinateMeasure μ, κ z.1 = A.leafMeasure R μ z.1 :=
    ae_of_ae_map measurable_fst.aemeasurable (A.ae_regularLeafKernel_eq R hAR μ hfree)
  filter_upwards [H', he] with z hz hez
  simpa only [PrimeDegreePackets.RootBox.basedLeaf, ← hez] using hz

lemma ae_intrinsicRootLeaf_discrete_lower_bound_restrict
    (A : PrimeDegreePackets.RootBox hij k) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ.restrict A.range, HasDiscreteLinearLowerBound (intrinsicRootLeaf hij μ x) := by
  apply A.ae_of_coordinate μ
  filter_upwards [A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree,
    ae_basedLeaf_discrete_lower_bound A R hAR μ hfree] with z he hz
  rwa [he]

end RootBox

/-- The actual intrinsic root leaf has a linear lower mass bound at almost
all base points. No entropy input is assumed. -/
theorem ae_intrinsicRootLeaf_discrete_lower_bound {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ, HasDiscreteLinearLowerBound (intrinsicRootLeaf hij μ x) := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H := (ae_restrict_iUnion_iff (μ := μ)
    (fun B : boundedRootAtlas hij => B.val.box.range) _).mpr
    (fun B => RootBox.ae_intrinsicRootLeaf_discrete_lower_bound_restrict
      B.val.box B.val.radius B.val.time_bound μ hfree)
  simpa only [boundedRootAtlas_iUnion, Measure.restrict_univ] using H

end DukePrimeDegree

end

end OAI
