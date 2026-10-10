import OAI.Analysis.ProductSpaces.Resampling

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace IndependentProducts
section Tails
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (h₂ : MemLp (fun w : ℝ => w) 2 μ)

lemma path_generator_set_eq :
    {f : Lp ℝ 1 (productMeasure μ) | ∃ v : Vertex,
      (f : Sample → ℝ) =ᵐ[productMeasure μ] pathProduct v} = Set.range (pathL1 μ h₂) := by
  ext f
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    exact Lp.ext ((pathL1_ae μ h₂ v).trans hv.symm)
  · rintro ⟨v, rfl⟩
    exact ⟨v, pathL1_ae μ h₂ v⟩

lemma dense_pathVector_span :
    Dense ((Submodule.span ℝ (Set.range (pathVector μ h₂))) : Set (productSpan μ)) := by
  apply Subtype.dense_iff.mpr
  have he : ((↑) : productSpan μ → Lp ℝ 1 (productMeasure μ)) ''
      (Submodule.span ℝ (Set.range (pathVector μ h₂)) : Set (productSpan μ)) =
      (Submodule.span ℝ (Set.range (pathL1 μ h₂)) : Set (Lp ℝ 1 (productMeasure μ))) := by
    change (↑((Submodule.span ℝ (Set.range (pathVector μ h₂))).map (productSpan μ).subtype) :
      Set (Lp ℝ 1 (productMeasure μ))) = _
    rw [Submodule.map_span]
    congr 2
    rw [← Set.range_comp]
    rfl
  intro x hx
  change x ∈ closure (((↑) : productSpan μ → Lp ℝ 1 (productMeasure μ)) ''
    (Submodule.span ℝ (Set.range (pathVector μ h₂)) : Set (productSpan μ)))
  rw [he]
  simpa only [productSpan, path_generator_set_eq μ h₂, Submodule.topologicalClosure_coe] using hx

namespace FiniteHead
variable (T : FiniteHead)

def headSpan : Submodule ℝ (productSpan μ) :=
  Submodule.span ℝ (pathVector μ h₂ '' (T.vertices : Set Vertex))

instance headSpan_finiteDimensional : FiniteDimensional ℝ (T.headSpan μ h₂) :=
  FiniteDimensional.span_of_finite ℝ (T.vertices.finite_toSet.image _)

/-- Relative tail products, algebraically equal to sums of outside-head jumps. -/
def relativeVector (v : Vertex) : productSpan μ :=
  pathVector μ h₂ v - pathVector μ h₂ (T.ancestor v)

def tailAlgebraic : Submodule ℝ (productSpan μ) :=
  Submodule.span ℝ (T.relativeVector μ h₂ '' {v : Vertex | v ∉ T.vertices})

def tailSpace : Submodule ℝ (productSpan μ) := (T.tailAlgebraic μ h₂).topologicalClosure

lemma relativeVector_mem (v : Vertex) : T.relativeVector μ h₂ v ∈ T.tailAlgebraic μ h₂ := by
  by_cases hv : v ∈ T.vertices
  · simp [relativeVector, T.ancestor_of_mem hv]
  · exact Submodule.subset_span ⟨v, hv, rfl⟩

lemma headSpan_sup_tailSpace : T.tailSpace μ h₂ ⊔ T.headSpan μ h₂ = ⊤ := by
  have hclosed : IsClosed (↑(T.tailSpace μ h₂ ⊔ T.headSpan μ h₂) : Set (productSpan μ)) :=
    Submodule.isClosed_sup_finiteDimensional (T.tailSpace μ h₂) (T.headSpan μ h₂)
      (Submodule.isClosed_topologicalClosure (T.tailAlgebraic μ h₂))
  have hle : Submodule.span ℝ (Set.range (pathVector μ h₂)) ≤ T.tailSpace μ h₂ ⊔ T.headSpan μ h₂ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    have hg : T.relativeVector μ h₂ v ∈ T.tailSpace μ h₂ :=
      Submodule.le_topologicalClosure _ (T.relativeVector_mem μ h₂ v)
    have ha : pathVector μ h₂ (T.ancestor v) ∈ T.headSpan μ h₂ :=
      Submodule.subset_span ⟨T.ancestor v, T.ancestor_mem v, rfl⟩
    have hgg : T.relativeVector μ h₂ v ∈ T.tailSpace μ h₂ ⊔ T.headSpan μ h₂ :=
      (show T.tailSpace μ h₂ ≤ T.tailSpace μ h₂ ⊔ T.headSpan μ h₂ from le_sup_left) hg
    have haa : pathVector μ h₂ (T.ancestor v) ∈ T.tailSpace μ h₂ ⊔ T.headSpan μ h₂ :=
      (show T.headSpan μ h₂ ≤ T.tailSpace μ h₂ ⊔ T.headSpan μ h₂ from le_sup_right) ha
    have hh := (T.tailSpace μ h₂ ⊔ T.headSpan μ h₂).add_mem hgg haa
    change pathVector μ h₂ v ∈ T.tailSpace μ h₂ ⊔ T.headSpan μ h₂
    convert hh using 1
    simp only [relativeVector, sub_add_cancel]
  have hc := Submodule.topologicalClosure_minimal _ hle hclosed
  rw [Submodule.dense_iff_topologicalClosure_eq_top.mp (dense_pathVector_span μ h₂)] at hc
  exact top_le_iff.mp hc

lemma tailSpace_cofinite : T.tailSpace μ h₂ ∈ CofiniteSubspaces (productSpan μ) := by
  refine ⟨Submodule.isClosed_topologicalClosure _, ?_⟩
  refine FiniteDimensional.of_surjective (V := T.headSpan μ h₂)
    ((T.tailSpace μ h₂).mkQ.comp (T.headSpan μ h₂).subtype) ?_
  intro q
  obtain ⟨x, hx⟩ := (T.tailSpace μ h₂).mkQ_surjective q
  have hm : x ∈ T.tailSpace μ h₂ ⊔ T.headSpan μ h₂ := by rw [T.headSpan_sup_tailSpace μ h₂]; trivial
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hm
  refine ⟨⟨v, hv⟩, ?_⟩
  change (T.tailSpace μ h₂).mkQ v = q
  have hz : (T.tailSpace μ h₂).mkQ u = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hu
  rw [← hx, ← huv, map_add, hz, zero_add]

end FiniteHead
end Tails
end IndependentProducts

end

end OAI
