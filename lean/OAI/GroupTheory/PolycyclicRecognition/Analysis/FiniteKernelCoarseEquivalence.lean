import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarseEquivalence

namespace OAI

/-! # Finite kernels do not change the discrete group coarse structure -/
noncomputable section
namespace PolycyclicRecognition
variable {G Q : Type*} [Group G] [Group Q]

theorem finite_kernel_preimage_finite (q : G →* Q) [Finite q.ker]
    (S : Set Q) (hS : S.Finite) : (q ⁻¹' S).Finite := by
  apply hS.preimage'
  intro y _
  by_cases h : ∃ g, q g = y
  · obtain ⟨g, hg⟩ := h
    let f : (q ⁻¹' {y}) → q.ker := fun x => ⟨g⁻¹ * x,
      by change q (g⁻¹ * x) = 1; rw [map_mul, map_inv, hg, x.property]; exact inv_mul_cancel y⟩
    have hf : Function.Injective f := by
      intro x z hxz
      apply Subtype.ext
      exact mul_left_cancel (congrArg (fun a : q.ker => (a : G)) hxz)
    let : Finite (q ⁻¹' {y}) := Finite.of_injective f hf
    exact Set.toFinite _
  · have he : q ⁻¹' {y} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun hx => h ⟨x, hx⟩
    rw [he]
    exact Set.finite_empty

def finiteKernelCoarseEquivalence (q : G →* Q) (hq : Function.Surjective q)
    [Finite q.ker] : GroupCoarseEquivalence G Q := by
  let s := Function.surjInv hq
  have hs : ∀ x, q (s x) = x := Function.surjInv_eq hq
  refine ⟨q, s, groupBornologous_hom q, ?_, ?_, ?_⟩
  · intro S hS
    refine ⟨q ⁻¹' S, finite_kernel_preimage_finite q S hS, ?_⟩
    intro x y hxy
    change q ((s x)⁻¹ * s y) ∈ S
    simpa only [map_mul, map_inv, hs] using hxy
  · apply (Set.toFinite (q.ker : Set G)).subset
    rintro _ ⟨g, rfl⟩
    change q (g⁻¹ * s (q g)) = 1
    rw [map_mul, map_inv, hs, inv_mul_cancel]
  · apply (Set.finite_singleton (1 : Q)).subset
    rintro _ ⟨y, rfl⟩
    simp only [Set.mem_singleton_iff, hs, inv_mul_cancel]

end PolycyclicRecognition

end

end OAI
