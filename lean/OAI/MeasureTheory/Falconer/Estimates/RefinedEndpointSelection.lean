import OAI.MeasureTheory.Falconer.Estimates.EndpointSelectionLift
import OAI.MeasureTheory.Falconer.Estimates.ParentPrefixRetention
import OAI.MeasureTheory.Falconer.Estimates.PlanarTreeUniformization

namespace OAI

/-! Re-regularize the actual leaves of a retained endpoint selection.
Every later occupied prefix retains its original local mass. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_refine_endpoint_selection {N : ℕ} {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ) (p : CellPath 2)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) (p₀ : CellPath 2)
    (D : Finset (CellPath 2))
    (hD : D ⊆ prefixChildren
      (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
      (blockDepth N B i) (blockDepth N B j) p₀)
    (hDne : D.Nonempty) {H : ℝ} (hH : 0 ≤ H)
    (hsize : ((prefixChildren
      (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
      (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ) ≤ H*(D.card:ℝ)) :
    let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
    let M := (H*(2:ℝ)^j)*((2*B+1:ℕ):ℝ)^K
    ∃ E ⊆ prefixFiber C (blockDepth N B i) p₀, E ⊆ cubePaths 2 N ∧
      E.image (List.take (blockDepth N B j)) = D ∧
      ∃ q ∈ E,
        let T := classLeaves E (blockLabel E N B (fun _ => []) K)
          (blockLabel E N B (fun _ => []) K q)
        T ⊆ E ∧ T.Nonempty ∧
          ((prefixFiber C (blockDepth N B i) p₀).card:ℝ) ≤ M*(T.card:ℝ) ∧
          ∀ k, k ≤ K → blockDepth N B i ≤ blockDepth N B k →
            ∀ r ∈ T.image (List.take (blockDepth N B k)),
              ((prefixFiber C (blockDepth N B k) r).card:ℝ) ≤
                (M*(2:ℝ)^(2*k))*((prefixFiber T (blockDepth N B k) r).card:ℝ) := by
  let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
  let E := (prefixFiber C (blockDepth N B i) p₀).filter
    (fun r => r.take (blockDepth N B j) ∈ D)
  obtain ⟨hEsub,hEne,hEmass,hEimage⟩ :=
    blockClass_lift_endpoint_selection hL B f K p hji hi p₀ D hD hDne hH hsize
  have hEN : E ⊆ cubePaths 2 N :=
    hEsub.trans ((Finset.filter_subset _ _).trans ((Finset.filter_subset _ _).trans hL))
  obtain ⟨q,hq,hregular⟩ := exists_large_planar_block_class hEN hEne B K
  let T := classLeaves E (blockLabel E N B (fun _ => []) K)
    (blockLabel E N B (fun _ => []) K q)
  have hTsub : T ⊆ E := Finset.filter_subset _ _
  have hTne : T.Nonempty := ⟨q,by simp [T,classLeaves,hq]⟩
  have hreg : (E.card:ℝ) ≤ ((2*B+1:ℕ):ℝ)^K*(T.card:ℝ) := by exact_mod_cast hregular
  have hmass : ((prefixFiber C (blockDepth N B i) p₀).card:ℝ) ≤
      ((H*(2:ℝ)^j)*((2*B+1:ℕ):ℝ)^K)*(T.card:ℝ) := by
    calc
      _ ≤ (H*(2:ℝ)^j)*(E.card:ℝ) := hEmass
      _ ≤ (H*(2:ℝ)^j)*(((2*B+1:ℕ):ℝ)^K*(T.card:ℝ)) :=
        mul_le_mul_of_nonneg_left hreg (by positivity)
      _ = _ := by ring
  refine ⟨E,hEsub,hEN,hEimage,q,hq,hTsub,hTne,hmass,?_⟩
  intro k hk hik r hr
  exact blockClass_parent_prefix_retention hL hEN B f (fun _ => []) K p q p₀
    (hTsub.trans hEsub) (by positivity) hmass hk hik hr

theorem blockClass_refine_quarter_endpoint_subset {N : ℕ} {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ) (p : CellPath 2)
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) (p₀ : CellPath 2)
    (P : Finset (Space 2)) (hP : P.Nonempty)
    (hsub : P ⊆ quarterEndpointSet Q
      (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
      (blockDepth N B i) (blockDepth N B j) p₀)
    {H : ℝ} (hH : 0 ≤ H)
    (hsize : ((quarterEndpointSet Q
      (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
      (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ) ≤ H*(P.card:ℝ)) :
    let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
    let M := (H*(2:ℝ)^j)*((2*B+1:ℕ):ℝ)^K
    ∃ E ⊆ prefixFiber C (blockDepth N B i) p₀, E ⊆ cubePaths 2 N ∧
      ∃ q ∈ E,
        let T := classLeaves E (blockLabel E N B (fun _ => []) K)
          (blockLabel E N B (fun _ => []) K q)
        T ⊆ E ∧ T.Nonempty ∧
          ((prefixFiber C (blockDepth N B i) p₀).card:ℝ) ≤ M*(T.card:ℝ) ∧
          quarterEndpointSet Q T (blockDepth N B i) (blockDepth N B j) p₀ ⊆ P := by
  let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
  have hCN : C ⊆ cubePaths 2 N := (Finset.filter_subset _ _).trans hL
  obtain ⟨D,hD,himage,hcard⟩ := quarter_endpoint_subset_paths Q
    (by rw [hQ]; norm_num) C hCN (Nat.sub_le _ _) p₀ P hsub
  have hDne : D.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact hP.card_pos)
  have hcount := (quarterEndpointSet_geometry Q hQ C hCN
    (blockDepth_antitone N B hji) (Nat.sub_le _ _) p₀).1
  have hsizeD : ((prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ) ≤
      H*(D.card:ℝ) := by
    have hh : ((quarterEndpointSet Q C (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ) ≤
        H*(P.card:ℝ) := hsize
    simpa only [hcount,hcard] using hh
  obtain ⟨E,hE,hEN,hED,q,hq,hT,hTne,hmass,_⟩ :=
    blockClass_refine_endpoint_selection hL B f K p hji hi p₀ D hD hDne hH hsizeD
  let T := classLeaves E (blockLabel E N B (fun _ => []) K)
    (blockLabel E N B (fun _ => []) K q)
  refine ⟨E,hE,hEN,q,hq,hT,hTne,hmass,?_⟩
  have hprefix : prefixFiber T (blockDepth N B i) p₀ = T :=
    Finset.filter_eq_self.mpr fun r hr => (Finset.mem_filter.mp (hE (hT hr))).2
  change ((prefixFiber T (blockDepth N B i) p₀).image (List.take (blockDepth N B j))).image
    (quarterEndpointPoint Q (blockDepth N B i) p₀) ⊆ P
  rw [hprefix,← himage,← hED]
  exact Finset.image_subset_image (Finset.image_subset_image hT)

end Falconer

end OAI
