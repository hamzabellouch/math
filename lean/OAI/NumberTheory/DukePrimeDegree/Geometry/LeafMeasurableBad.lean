import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafRationalRadii

namespace OAI

/-!
# Measurable bad sets for intrinsic leaf averages

Strict bad inequalities at rational radii define a measurable set.
Its complement controls every real radius, by continuity from above.
The diagonal scaling estimate bounds this set uniformly over all radii.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

def rootHitTimes {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (E : Set (X n)) (x : X n) : Set ℝ :=
  {u | rightAction x (Matrix.SpecialLinearGroup.transvection hij u) ∈ E}

lemma measurableSet_rootHitTimes {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {E : Set (X n)} (hE : MeasurableSet E) (x : X n) : MeasurableSet (rootHitTimes hij E x) :=
  hE.preimage (((continuous_rightAction_uncurry n).comp
    (continuous_const.prodMk (continuous_rootTransvection hij))).measurable)

lemma measurable_rootHitMass {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (κ : Kernel (X n) ℝ) [IsSFiniteKernel κ]
    {E : Set (X n)} (hE : MeasurableSet E) (r : ℝ) :
    Measurable (fun x => κ x (rootHitTimes hij E x ∩ closedBall 0 r)) := by
  have hcont : Continuous (fun z : X n × ℝ =>
      rightAction z.1 (Matrix.SpecialLinearGroup.transvection hij z.2)) :=
    (continuous_rightAction_uncurry n).comp
      (continuous_fst.prodMk ((continuous_rootTransvection hij).comp continuous_snd))
  exact Kernel.measurable_kernel_prodMk_left
    ((hE.preimage hcont.measurable).inter (measurable_snd isClosed_closedBall.measurableSet))

def rootRationalBad {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (κ : Kernel (X n) ℝ) (E : Set (X n)) (c : ℝ≥0∞) (R : ℝ) : Set (X n) :=
  {x | ∃ q : ℚ, (0 < (q : ℝ) ∧ (q : ℝ) ≤ R) ∧
    c * κ x (closedBall 0 (q : ℝ)) < κ x (rootHitTimes hij E x ∩ closedBall 0 (q : ℝ))}

lemma measurableSet_rootRationalBad {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (κ : Kernel (X n) ℝ) [IsSFiniteKernel κ]
    {E : Set (X n)} (hE : MeasurableSet E) (c : ℝ≥0∞) (R : ℝ) :
    MeasurableSet (rootRationalBad hij κ E c R) := by
  classical
  unfold rootRationalBad
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro q
  by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) ≤ R
  · simpa only [hq, true_and] using measurableSet_lt
      ((κ.measurable_coe isClosed_closedBall.measurableSet).const_mul c)
      (measurable_rootHitMass hij κ hE (q : ℝ))
  · simp only [hq, false_and, Set.ofPred_false]
    exact MeasurableSet.empty

theorem all_radii_rootRationalBad_bound
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ M : ℕ, ∀ (E : Set (X (d + 1))), MeasurableSet E → ∀ c : ℝ≥0∞,
      c * μ (⋃ m : ℕ, rootRationalBad hij (intrinsicRootKernel hij μ hfree) E c (m + 1)) ≤
        (M : ℝ≥0∞) * μ E + c * ε := by
  obtain ⟨M, hM⟩ := bounded_interval_intrinsic_maximal_bound d hij μ hA ε hε
  refine ⟨M, ?_⟩
  intro E hE c
  let κ := intrinsicRootKernel hij μ hfree
  have hmono : Monotone (fun m : ℕ => rootRationalBad hij κ E c (m + 1)) := by
    intro a b hab x hx
    obtain ⟨q, hq, hm⟩ := hx
    exact ⟨q, ⟨hq.1, hq.2.trans (by exact_mod_cast Nat.add_le_add_right hab 1)⟩, hm⟩
  rw [hmono.measure_iUnion, ENNReal.mul_iSup]
  apply iSup_le
  intro m
  apply hM (m + 1) _ E (measurableSet_rootRationalBad hij κ hE c _) hE c
  filter_upwards [ae_intrinsicRootKernel_eq hij μ hfree] with x hx hbad
  obtain ⟨q, hq, hm⟩ := hbad
  refine ⟨(q : ℝ), hq.1, hq.2, ?_⟩
  change c * κ x _ < κ x _ at hm
  rw [hx] at hm
  exact hm.le

theorem rootRationalBad_compl_all_radii
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (κ : Kernel (X n) ℝ) (x : X n) [IsLocallyFiniteMeasure (κ x)]
    {E : Set (X n)} (hE : MeasurableSet E) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (hx : x ∉ ⋃ m : ℕ, rootRationalBad hij κ E c (m + 1)) :
    ∀ r : ℝ, 0 < r → κ x (rootHitTimes hij E x ∩ closedBall 0 r) ≤
      c * κ x (closedBall 0 r) := by
  apply relative_closedBall_bound_of_rational (κ x) (rootHitTimes hij E x)
    (measurableSet_rootHitTimes hij hE x) c hc
  intro q hq
  apply le_of_not_gt
  intro h
  obtain ⟨m, hm⟩ := exists_nat_gt (q : ℝ)
  apply hx
  exact mem_iUnion.mpr ⟨m, q, ⟨hq, by linarith⟩, h⟩

end DukePrimeDegree

end

end OAI
