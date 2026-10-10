import OAI.MeasureTheory.Falconer.Recursion.UniformProfileGain

namespace OAI

/-! The initial class inherits its lower profile from the actual leaf prefix
counts. The label-selection loss is explicit and paid only once. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem block_profile_ratios_from_prefix {N B : ℕ} (hB : 0 < B)
    {L : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N)
    (f : CellPath 2 → List ℕ) {p : CellPath 2} (hp : p ∈ L)
    {A D t : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hmass : (L.card:ℝ) ≤ D*((classLeaves L (blockLabel L N B f (N/B+1))
      (blockLabel L N B f (N/B+1) p)).card:ℝ))
    (hprefix : ∀ k ≤ N, ∀ q : CellPath 2,
      ((prefixFiber L k q).card:ℝ) ≤ A*(2:ℝ)^(-t*(k:ℝ))*(L.card:ℝ)) :
    ∀ i ≤ N/B+1,
      (blockProduct L (blockLabel L N B f (N/B+1)) N B i p:ℝ)/
        (blockProduct L (blockLabel L N B f (N/B+1)) N B (N/B+1) p:ℝ) ≤
      ((2:ℝ)^(N/B+1)*D*A)*(2:ℝ)^(-t*(blockDepth N B i:ℝ)) := by
  intro i hi
  let K := N/B+1
  let F := blockLabel L N B f K
  let C := classLeaves L F (F p)
  have hpC : p ∈ C := by simp [C,classLeaves,hp]
  have hCsub : C ⊆ L := Finset.filter_subset _ _
  have hc := blockClass_leaf_count hL B f K p hi (Finset.mem_image.mpr ⟨p,hpC,rfl⟩)
  have hr := blockClass_root_count hL hB f hp
  apply (div_le_iff₀ (Nat.cast_pos.mpr (blockProduct_pos L F N B K p))).2
  calc
    (blockProduct L F N B i p:ℝ) ≤ ((prefixFiber C (blockDepth N B i)
        (p.take (blockDepth N B i))).card:ℝ) := Nat.cast_le.mpr hc.1
    _ ≤ ((prefixFiber L (blockDepth N B i) (p.take (blockDepth N B i))).card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hCsub))
    _ ≤ A*(2:ℝ)^(-t*(blockDepth N B i:ℝ))*(L.card:ℝ) :=
      hprefix _ (Nat.sub_le N _) _
    _ ≤ A*(2:ℝ)^(-t*(blockDepth N B i:ℝ))*(D*(C.card:ℝ)) := by gcongr
    _ ≤ A*(2:ℝ)^(-t*(blockDepth N B i:ℝ))*(D*((2:ℝ)^K*
        (blockProduct L F N B K p:ℝ))) := by
      gcongr
      exact_mod_cast hr.2
    _ = _ := by ring

theorem exists_initial_profile_class {N B : ℕ} (hB : 0 < B)
    {L : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N) (hLne : L.Nonempty)
    {A t lam : ℝ} (hA : 0 ≤ A)
    (hprefix : ∀ k ≤ N, ∀ q : CellPath 2,
      ((prefixFiber L k q).card:ℝ) ≤ A*(2:ℝ)^(-t*(k:ℝ))*(L.card:ℝ))
    (hcost : (2:ℝ)^(N/B+1)*((2*B+1:ℕ):ℝ)^(N/B+1)*A ≤ (2:ℝ)^(lam*(N:ℝ))) :
    ∃ p ∈ L,
      (L.card:ℝ) ≤ ((2*B+1:ℕ):ℝ)^(N/B+1)*
        ((classLeaves L (blockLabel L N B (fun _ => []) (N/B+1))
          (blockLabel L N B (fun _ => []) (N/B+1) p)).card:ℝ) ∧
      ∀ i ≤ N/B+1,
        (blockProduct L (blockLabel L N B (fun _ => []) (N/B+1)) N B i p:ℝ)/
          (blockProduct L (blockLabel L N B (fun _ => []) (N/B+1)) N B (N/B+1) p:ℝ) ≤
        (2:ℝ)^(lam*(N:ℝ)-t*(blockDepth N B i:ℝ)) := by
  obtain ⟨p,hp,hmass⟩ := exists_large_planar_block_class hL hLne B (N/B+1)
  have hmassR : (L.card:ℝ) ≤ ((2*B+1:ℕ):ℝ)^(N/B+1)*
      ((classLeaves L (blockLabel L N B (fun _ => []) (N/B+1))
        (blockLabel L N B (fun _ => []) (N/B+1) p)).card:ℝ) := by exact_mod_cast hmass
  refine ⟨p,hp,hmassR,?_⟩
  have hh := block_profile_ratios_from_prefix hB hL (fun _ => []) hp hA (by positivity) hmassR hprefix
  intro i hi
  calc
    _ ≤ ((2:ℝ)^(N/B+1)*((2*B+1:ℕ):ℝ)^(N/B+1)*A)*
        (2:ℝ)^(-t*(blockDepth N B i:ℝ)) := hh i hi
    _ ≤ (2:ℝ)^(lam*(N:ℝ))*(2:ℝ)^(-t*(blockDepth N B i:ℝ)) :=
      mul_le_mul_of_nonneg_right hcost (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; congr 1; ring

end Falconer

end OAI
