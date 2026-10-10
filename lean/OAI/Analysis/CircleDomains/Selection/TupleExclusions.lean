import OAI.Analysis.CircleDomains.Selection.SparseTags

namespace OAI

/-! Excluding precisely the infinite tuple values makes every individual
slot integral finite. The exclusions remain Borel for a Borel metric. -/

open Set MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

def tupleInfiniteExclusions (f : LevelTuple → ℝ≥0∞) (n : ℕ)
    (l : Fin (n + 1) → ℕ) : Set (Fin (n + 1) → UnitAddCircle) :=
  {t | f ⟨n, l, t⟩ = ∞}

theorem measurableSet_tupleInfiniteExclusions {f : LevelTuple → ℝ≥0∞}
    (hf : Measurable f) (n : ℕ) (l : Fin (n + 1) → ℕ) :
    MeasurableSet (tupleInfiniteExclusions f n l) := by
  have hc : Continuous (fun t : Fin (n + 1) → UnitAddCircle =>
      (⟨n, l, t⟩ : LevelTuple)) :=
    continuous_sigmaMk.comp (continuous_const.prodMk continuous_id)
  exact (hf.comp (Continuous.measurable
    (α := Fin (n + 1) → UnitAddCircle) (γ := LevelTuple) hc)) (measurableSet_singleton ∞)

theorem active_mem_tupleInfiniteExclusions (f : LevelTuple → ℝ≥0∞) (q : TagData)
    (hq : f (tagDataTuple q) = ∞) :
    activeTagSlot q ∈ tagTupleExcluded (tupleInfiniteExclusions f) := by
  apply mem_iUnion.mpr
  refine ⟨q.1, mem_iUnion.mpr ⟨q.2.1, ?_⟩⟩
  refine ⟨q.2.2, ⟨hq, mem_univ _⟩, ?_⟩
  rfl

theorem slotIntegral_finite_of_excluded {f : LevelTuple → ℝ≥0∞} (hf : Measurable f)
    {s : TagSlot} (hs : s ∉ tagTupleExcluded (tupleInfiniteExclusions f)) :
    (∫⁻ t, f t ∂slotTupleMeasure s) < ∞ := by
  cases s with
  | inl u => simp [slotTupleMeasure]
  | inr q =>
    rw [slotTupleMeasure, Sum.elim_inr, lintegral_dirac' _ hf]
    exact lt_top_iff_ne_top.mpr fun hq => hs (active_mem_tupleInfiniteExclusions f q hq)

theorem tagRules_slotIntegral_finite {X : Type*} [MetricSpace X]
    {H : ℕ → Set (UnitAddCircle × X)} {f : LevelTuple → ℝ≥0∞}
    (hf : Measurable f) {Γ : TaggedPath X}
    (hΓ : TagRules H (tupleInfiniteExclusions f) Γ) (k : ℕ) :
    (∫⁻ t, f t ∂slotTupleMeasure (Γ.2 k)) < ∞ :=
  slotIntegral_finite_of_excluded hf (hΓ k).2.2

end CircleDomainRigidity

end

end OAI
