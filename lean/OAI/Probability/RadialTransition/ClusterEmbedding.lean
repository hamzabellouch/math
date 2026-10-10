import OAI.Probability.RadialTransition.MultiConvolution

namespace OAI

universe uX

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
attribute [local instance] Classical.propDecidable

lemma configurationMultiset_fibers {X : Type uX} {ι I : Type} [Fintype ι] [Fintype I]
    (x : ι → X) (f : ι → I) :
    ∑ q : I, ((Finset.univ.filter (fun j => f j = q)).val.map x) = configurationMultiset x := by
  classical
  have hq (q : I) : ((Finset.univ.filter (fun j => f j=q)).val.map x) =
      ∑ j : ι, if f j=q then ({x j}:Multiset X) else 0 := by
    rw [← Finset.sum_filter]
    change _ = ((Finset.univ.filter (fun j => f j=q)).val.map (fun j => ({x j}:Multiset X))).sum
    simpa only [Multiset.map_map, Function.comp_def] using
      (Multiset.sum_map_singleton ((Finset.univ.filter (fun j => f j=q)).val.map x)).symm
  simp_rw [hq]
  rw [Finset.sum_comm]
  simp [configurationMultiset]

section Embed
variable {X : Type uX} {I Q : Type} [Fintype I] [Fintype Q]

lemma indexedClusterProduct_embedding (W : I → Multiset X → ℝ≥0∞)
    (h0 : ∀ i, 1 ≤ W i 0) (f : Q → I) (hf : Function.Injective f) (s : Q → Multiset X) :
    (∏ q, W (f q) (s q)) ≤ indexedClusterProduct W (∑ q, s q) := by
  classical
  let u (i : I) : Multiset X := ∑ q : Q, if f q=i then s q else 0
  have huv (q : Q) : u (f q) = s q := by
    simp [u, hf.eq_iff]
  have huz (i : I) (hi : i ∉ Finset.univ.image f) : u i = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    exact ite_eq_right (fun he => hi (Finset.mem_image.mpr ⟨q,Finset.mem_univ _,he⟩))
  have hsum : ∑ i, u i = ∑ q, s q := by
    simp only [u]
    rw [Finset.sum_comm]
    simp
  have hp : (∏ q, W (f q) (s q)) = ∏ i ∈ Finset.univ.image f, W i (u i) := by
    rw [Finset.prod_image (fun a _ b _ hab => hf hab)]
    simp_rw [huv]
  rw [hp]
  have hle : (∏ i ∈ Finset.univ.image f, W i (u i)) ≤ ∏ i, W i (u i) := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _) (fun _ _ => bot_le)
    intro i _ hi
    rw [huz i hi]
    exact h0 i
  apply hle.trans
  rw [← hsum]
  exact indexedClusterProduct_ge W u

end Embed
end RadialTransition
end

end OAI
