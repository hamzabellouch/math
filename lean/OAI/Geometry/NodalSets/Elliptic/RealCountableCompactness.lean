import OAI.Geometry.NodalSets.Elliptic.RealCompactLipschitzFamily

namespace OAI

namespace Yau.Geometry
open Set Metric Filter BoundedContinuousFunction
open scoped Topology NNReal
noncomputable section
variable {I : Type*} [Countable I] {X : I → Type*}
  [∀ i, PseudoMetricSpace (X i)] [∀ i, CompactSpace (X i)]

theorem real_countable_uniform_subsequence (F : ∀ i, ℕ → X i → ℝ)
    (B : I → ℝ) (L : I → ℝ≥0)
    (hb : ∀ i j x, |F i j x| ≤ B i) (hL : ∀ i j, LipschitzWith (L i) (F i j)) :
    ∃ f : ∀ i, X i → ℝ, (∀ i, Continuous (f i)) ∧
      ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ i,
        TendstoUniformly (fun j ↦ F i (nu j)) (f i) atTop := by
  let G : ∀ i, ℕ → X i →ᵇ ℝ := fun i j ↦
    BoundedContinuousFunction.mkOfCompact ⟨F i j,(hL i j).continuous⟩
  let S (i : I) := closure (range (G i))
  have hc (i : I) : IsCompact (S i) := real_bounded_lipschitz_compact (G i) (B i) (L i) (hb i) (hL i)
  let (i : I) : CompactSpace (S i) := isCompact_iff_compactSpace.mp (hc i)
  let seq : ℕ → ∀ i, S i := fun j i ↦ ⟨G i j,subset_closure (mem_range_self j)⟩
  obtain ⟨f,_,nu,hnu,ht⟩ := (isCompact_univ : IsCompact (univ : Set (∀ i, S i))).tendsto_subseq
    (fun _ ↦ mem_univ _ : ∀ j, seq j ∈ univ)
  refine ⟨fun i ↦ (f i).val,fun i ↦ (f i).val.continuous,nu,hnu,?_⟩
  intro i
  have hi := ((continuous_subtype_val.comp (continuous_apply i)).tendsto f).comp ht
  exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hi

end
end Yau.Geometry

end OAI
