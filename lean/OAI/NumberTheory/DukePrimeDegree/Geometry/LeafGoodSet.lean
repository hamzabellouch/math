import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafMeasurableBad

namespace OAI

/-!
# Large good sets for all leafwise radii

For a sufficiently small exceptional ambient set, almost every base
point sees only a prescribed small fraction of that set in every
centered root interval. This is the maximal-inequality good set used
in EKL (2006), Section 4.3.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_large_rootLeaf_good_set
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ E : Set (X (d + 1)), MeasurableSet E →
      μ E < ENNReal.ofReal δ → ∃ G : Set (X (d + 1)), MeasurableSet G ∧
      μ Gᶜ < ENNReal.ofReal η ∧ ∀ x ∈ G, ∀ r : ℝ, 0 < r →
        intrinsicRootLeaf hij μ x (rootHitTimes hij E x ∩ closedBall 0 r) ≤
          ENNReal.ofReal c * intrinsicRootLeaf hij μ x (closedBall 0 r) := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let κ := intrinsicRootKernel hij μ hfree
  have heq : ∀ᵐ x ∂μ, κ x = intrinsicRootLeaf hij μ x := ae_intrinsicRootKernel_eq hij μ hfree
  obtain ⟨N, hNbad, hN, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp heq)
  obtain ⟨M, hM⟩ := all_radii_rootRationalBad_bound d hij μ hA hfree
    (ENNReal.ofReal (η / 2)) (by positivity)
  let δ : ℝ := c * η / (2 * ((M : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro E hE hsmall
  let B : Set (X (d + 1)) := ⋃ m : ℕ, rootRationalBad hij κ E (ENNReal.ofReal c) (m + 1)
  have hB : MeasurableSet B := MeasurableSet.iUnion fun m =>
    measurableSet_rootRationalBad hij κ hE (ENNReal.ofReal c) (m + 1)
  have hb : ENNReal.ofReal c * μ B ≤
      (M : ℝ≥0∞) * μ E + ENNReal.ofReal c * ENNReal.ofReal (η / 2) := hM E hE _
  have hreal := ENNReal.toReal_mono (by finiteness) hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le,
    ENNReal.toReal_add (by finiteness) (by finiteness)] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hc.le,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ η / 2)] at hreal
  have hsmallR : (μ E).toReal < δ := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top μ E) ENNReal.ofReal_ne_top).mpr hsmall
    simpa only [ENNReal.toReal_ofReal hδ.le] using h
  have hterm : (M : ℝ) * (μ E).toReal < c * η / 2 := by
    calc
      (M : ℝ) * (μ E).toReal ≤ ((M : ℝ) + 1) * (μ E).toReal :=
        mul_le_mul_of_nonneg_right (by linarith) ENNReal.toReal_nonneg
      _ < ((M : ℝ) + 1) * δ := mul_lt_mul_of_pos_left hsmallR (by positivity)
      _ = c * η / 2 := by dsimp [δ]; field_simp
  have hbadsmall : μ B < ENNReal.ofReal η := by
    apply (ENNReal.toReal_lt_toReal (measure_ne_top μ B) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hη.le]
    nlinarith
  refine ⟨(B ∪ N)ᶜ, (hB.union hN).compl, ?_, ?_⟩
  · rw [compl_compl]
    have hle : μ (B ∪ N) ≤ μ B := by
      simpa only [hNzero, add_zero] using (measure_union_le (μ := μ) B N)
    exact hle.trans_lt hbadsmall
  · intro x hx r hr
    have hxB : x ∉ B := fun h => hx (Or.inl h)
    have hxN : x ∉ N := fun h => hx (Or.inr h)
    have hxeq : κ x = intrinsicRootLeaf hij μ x := by
      by_contra h
      exact hxN (hNbad h)
    have h := rootRationalBad_compl_all_radii hij κ x hE (ENNReal.ofReal c)
      ENNReal.ofReal_ne_top hxB r hr
    simpa only [hxeq] using h

end DukePrimeDegree

end

end OAI
