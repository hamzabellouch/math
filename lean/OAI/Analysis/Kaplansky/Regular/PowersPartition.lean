import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Regular.FreeWord

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

attribute [local instance] Classical.decEq Classical.propDecidable

lemma starts_index_unique {n m : ℤ} {v : FZ} (hn : Starts n v) (hm : Starts m v) : n=m := by
  obtain ⟨s,hs⟩ := hn
  obtain ⟨t,ht⟩ := hm
  exact (prefix_disjoint hs ht).1

lemma coordinate_genZ_inv (n : ℤ) : coordinate (genZ n)⁻¹ = (FreeGroup.of n)⁻¹ := by
  simp [coordinate,map_inv,action_genZ]
lemma coordinate_conjugate (n : ℤ) (w : F2) :
    coordinate (genZ n*w*(genZ n)⁻¹) = FreeGroup.of n*coordinate w*(FreeGroup.of (n+exponent w))⁻¹ := by
  simp [coordinate_mul,coordinate_genZ_inv,translate_zero]

theorem powers_partition (F : Finset F2) (hF : ∀ f ∈ F, f ≠ 1) (N : ℕ) :
    ∃ (u : F2) (D : F2 → Prop) (h : Fin N → F2),
      (∀ f ∈ F, ∀ w, D w → ¬ D (u*f*u⁻¹*w)) ∧
      (∀ i j w, ¬ D ((h i)⁻¹*w) → ¬ D ((h j)⁻¹*w) → i=j) := by
  let S : Finset ℤ := F.biUnion (fun f =>
    ((coordinate f).toWord.map Prod.fst).toFinset ∪
    ((coordinate f).toWord.map (fun z => z.1-exponent f)).toFinset)
  obtain ⟨n,hn⟩ := S.exists_notMem
  have h1 (f : F2) (hf : f ∈ F) (x : ℤ × Bool) (hx : x ∈ (coordinate f).toWord) : x.1 ≠ n := by
    intro he
    apply hn
    apply Finset.mem_biUnion.mpr
    refine ⟨f,hf,Finset.mem_union_left _ ?_⟩
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x,hx,he⟩)
  have h2 (f : F2) (hf : f ∈ F) (x : ℤ × Bool) (hx : x ∈ (coordinate f).toWord) : x.1 ≠ n+exponent f := by
    intro he
    apply hn
    apply Finset.mem_biUnion.mpr
    refine ⟨f,hf,Finset.mem_union_right _ ?_⟩
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x,hx,by omega⟩)
  let D : F2 → Prop := fun w => ¬ Starts n (coordinate w)
  let h : Fin N → F2 := fun i => genZ (n+(i.val:ℤ)+1)
  refine ⟨genZ n,D,h,?_,?_⟩
  · intro f hf w hw
    change ¬¬ Starts n (coordinate (genZ n*f*(genZ n)⁻¹*w))
    apply not_not.mpr
    rw [coordinate_mul,coordinate_conjugate]
    have hk : exponent (genZ n*f*(genZ n)⁻¹) = exponent f := by simp
    rw [hk]
    apply sandwich_multiply_starts n (exponent f) (coordinate f) (coordinate w) (h1 f hf) (h2 f hf) _ hw
    by_contra he
    push Not at he
    exact hF f hf (coordinate_exponent_separate f he.1 he.2)
  · intro i j w hi hj
    have hs (k : Fin N) (hk : ¬D ((h k)⁻¹*w)) : Starts (n+(k.val:ℤ)+1) (coordinate w) := by
      have hp : Starts n (coordinate ((h k)⁻¹*w)) := not_not.mp hk
      have hn' : ¬ Starts (n+(k.val:ℤ)+1) (coordinate ((h k)⁻¹*w)) := by
        intro ht
        have he := starts_index_unique ht hp
        have hk0 : (0:ℤ) ≤ k.val := Int.natCast_nonneg _
        omega
      have he := coordinate_genZ_mul (n+(k.val:ℤ)+1) ((h k)⁻¹*w)
      change coordinate (h k*((h k)⁻¹*w)) = _ at he
      simp only [mul_inv_cancel_left] at he
      rw [he]
      exact ⟨true,prefix_multiply_of_not_starts _ _ hn'⟩
    have he := starts_index_unique (hs i hi) (hs j hj)
    apply Fin.ext
    omega


end KaplanskyConsequences.Regular

end

end OAI
