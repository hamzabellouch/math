import OAI.Geometry.SurfaceImmersion.Geometry.FiniteGermSeparator

namespace OAI

/-! Smooth separators constant near each member of a finite disjoint
closed family. This freezes whole quadratic crosscap neighborhoods while
regularizing double pairs outside the corresponding diagonal squares. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

theorem closed_family_separator {ι : Type*} [Fintype ι]
    (A : ι → Set M) (hA : ∀ i, IsClosed (A i)) (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (p q : M) (hpq : p ≠ q) (hpair : ∀ i, ¬ (p ∈ A i ∧ q ∈ A i)) :
    ∃ χ : M → ℝ, ContMDiff planeModel 𝓘(ℝ) ∞ χ ∧
      (∀ x, χ x ∈ Icc 0 1) ∧ χ =ᶠ[𝓝 p] (fun _ => 1) ∧
      χ =ᶠ[𝓝 q] (fun _ => 0) ∧ ∀ i,
      (χ =ᶠ[𝓝ˢ (A i)] (fun _ => 0)) ∨ (χ =ᶠ[𝓝ˢ (A i)] (fun _ => 1)) := by
  classical
  let B₀ : Set M := {q} ∪ ⋃ i, if p ∈ A i then ∅ else A i
  let B₁ : Set M := {p} ∪ ⋃ i, if p ∈ A i then A i else ∅
  have hB₀ : IsClosed B₀ := isClosed_singleton.union (isClosed_iUnion_of_finite fun i => by
    split_ifs <;> first | exact isClosed_empty | exact hA i)
  have hB₁ : IsClosed B₁ := isClosed_singleton.union (isClosed_iUnion_of_finite fun i => by
    split_ifs <;> first | exact isClosed_empty | exact hA i)
  have hBdis : Disjoint B₀ B₁ := by
    apply Set.disjoint_left.mpr
    intro x hx₀ hx₁
    rcases hx₀ with hxq | hx₀
    · have hx : x = q := mem_singleton_iff.mp hxq
      subst x
      rcases hx₁ with hqp | hx₁
      · exact hpq (mem_singleton_iff.mp hqp).symm
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hx₁
        split_ifs at hi with hp
        · exact hpair i ⟨hp,hi⟩
        · exact hi
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx₀
      split_ifs at hi with hpi
      · exact hi
      rcases hx₁ with hxp | hx₁
      · exact hpi ((mem_singleton_iff.mp hxp) ▸ hi)
      · obtain ⟨j,hj⟩ := mem_iUnion.mp hx₁
        split_ifs at hj with hpj
        · by_cases hij : i = j
          · subst j; exact hpi hpj
          · exact Set.disjoint_left.mp (hdis hij) hi hj
        · exact hj
  obtain ⟨χ,hχ0,hχ1,hχr⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    planeModel hB₀ hB₁ hBdis (n := (⊤ : ℕ∞))
  have hpB : p ∈ B₁ := Or.inl (mem_singleton p)
  have hqB : q ∈ B₀ := Or.inl (mem_singleton q)
  refine ⟨χ,χ.contMDiff,hχr,
    hχ1.filter_mono (nhds_le_nhdsSet hpB),
    hχ0.filter_mono (nhds_le_nhdsSet hqB),?_⟩
  intro i
  by_cases hp : p ∈ A i
  · apply Or.inr
    apply hχ1.filter_mono
    apply nhdsSet_mono
    intro x hx
    exact Or.inr (mem_iUnion.mpr ⟨i,by simpa [hp] using hx⟩)
  · apply Or.inl
    apply hχ0.filter_mono
    apply nhdsSet_mono
    intro x hx
    exact Or.inr (mem_iUnion.mpr ⟨i,by simpa [hp] using hx⟩)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
