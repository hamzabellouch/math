import OAI.Analysis.Pureness.States.FiniteRegularizationAddition

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped ENNReal NNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem finiteRegularizedValue_lowerSemicontinuous
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d) (n : ℕ) :
    LowerSemicontinuous (finiteRegularizedValue d n) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro r
  apply Metric.isOpen_iff.mpr
  intro M hM
  change r < finiteRegularizedValue d n M at hM
  obtain ⟨ε,hε⟩ := lt_iSup_iff.mp hM
  obtain ⟨hεpos,hcut⟩ := lt_iSup_iff.mp hε
  refine ⟨(ε : ℝ)/2, half_pos hεpos, ?_⟩
  intro N hN
  have hdist : dist M N < (ε : ℝ)/2 := by simpa only [Metric.mem_ball, dist_comm] using hN
  have hc := cut_cuntzBelow_cut_of_dist ε hεpos hdist
  have horder : finitePositiveClass n (Positive.cut ε M) ≤
      finitePositiveClass n (Positive.cut (ε/2) N) :=
    (finitePositiveClass_le_iff n _ _).mpr ((cuntzSubequiv_iff_shared _ _).mpr hc)
  exact hcut.trans_le ((hd horder).trans (cut_class_value_le_regularized d n N (ε/2) (by positivity)))

@[simp] theorem regularizedFiniteDimension_eval
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n)) :
    regularizedFiniteDimension d hd (finitePositiveClass n M) = finiteRegularizedValue d n M :=
  finiteRegularizedFunction_eval d hd n M

theorem regularizedFiniteDimension_le
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (x : finiteCuntzSubmonoid (A := A)) : regularizedFiniteDimension d hd x ≤ d x := by
  obtain ⟨⟨n,M⟩,rfl⟩ := finiteClass_has_representative x
  rw [regularizedFiniteDimension_eval]
  exact finiteRegularizedValue_le d hd n M

lemma cut_value_le_twice_regularized
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n)) (ε : ℝ≥0) (hε : 0 < ε) :
    d (finitePositiveClass n (Positive.cut ε M)) ≤
      finiteRegularizedValue (regularizedFiniteDimension d hd) n M := by
  apply le_iSup_of_le (ε/2)
  apply le_iSup_of_le (show 0 < ε/2 from by positivity)
  rw [regularizedFiniteDimension_eval]
  apply le_iSup_of_le (ε/2)
  apply le_iSup_of_le (show 0 < ε/2 from by positivity)
  rw [Positive.cut_cut, add_halves]

theorem regularizedFiniteDimension_idempotent
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d) :
    regularizedFiniteDimension (regularizedFiniteDimension d hd)
      (regularizedFiniteDimension_monotone d hd) = regularizedFiniteDimension d hd := by
  ext x
  apply le_antisymm (regularizedFiniteDimension_le _ _ x)
  obtain ⟨⟨n,M⟩,rfl⟩ := finiteClass_has_representative x
  rw [regularizedFiniteDimension_eval, regularizedFiniteDimension_eval]
  exact iSup_le fun ε => iSup_le fun hε => cut_value_le_twice_regularized d hd n M ε hε

theorem regularizedFiniteDimension_eq_of_lowerSemicontinuous
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M))) :
    regularizedFiniteDimension d hd = d := by
  ext x
  apply le_antisymm (regularizedFiniteDimension_le d hd x)
  obtain ⟨⟨n,M⟩,rfl⟩ := finiteClass_has_representative x
  rw [regularizedFiniteDimension_eval]
  let ε : ℕ → ℝ≥0 := fun j => 1 / ((j : ℝ≥0)+1)
  have hε : Filter.Tendsto (fun j => (ε j : ℝ)) Filter.atTop (nhds 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Filter.Tendsto (fun j : ℕ => 1 / ((j : ℝ)+1)) Filter.atTop (nhds 0))
  exact ((hlsc n).isClosed_preimage (finiteRegularizedValue d n M)).mem_of_tendsto
    (Positive.tendsto_cut ε hε M) (Filter.Eventually.of_forall fun j =>
      cut_class_value_le_regularized d n M (ε j) (by dsimp [ε]; positivity))
end CuntzPureness

end

end OAI
