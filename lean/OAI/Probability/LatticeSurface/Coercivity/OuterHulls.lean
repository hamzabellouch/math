import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.FilledHull
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry
import OAI.Probability.LatticeSurface.Coercivity.HoleIncident
import OAI.Probability.LatticeSurface.Coercivity.HoleStar
import OAI.Probability.LatticeSurface.Coercivity.HullMore
import OAI.Probability.LatticeSurface.Coercivity.HullRims

namespace OAI

noncomputable section

open scoped BigOperators

namespace SparseHoles

noncomputable def outerHulls (J : Finset (Finset Vertex)) (lo hi : Vertex) :
    Finset (Finset Vertex) := by
  classical
  exact (J.image (fun C => filled C lo hi)).filter (fun H =>
    ∀ K∈J.image (fun C => filled C lo hi), H ⊆ K → K ⊆ H)

lemma outer_mem (J : Finset (Finset Vertex)) (lo hi : Vertex) (H : Finset Vertex) :
    H∈outerHulls J lo hi ↔ H∈J.image (fun C => filled C lo hi) ∧
    ∀ K∈J.image (fun C => filled C lo hi), H ⊆ K → K ⊆ H := by
  classical
  simp [outerHulls]

lemma hull_subset_outer (J : Finset (Finset Vertex)) (lo hi : Vertex)
    {C : Finset Vertex} (hC : C∈J) :
    ∃ H∈outerHulls J lo hi, filled C lo hi ⊆ H := by
  classical
  let S := J.image (fun C => filled C lo hi)
  have hCS : filled C lo hi∈S := Finset.mem_image_of_mem _ hC
  obtain ⟨H,hCH,hH,hmax⟩ := Finset.exists_le_maximal S hCS
  exact ⟨H,(outer_mem J lo hi H).mpr ⟨hH,hmax⟩,hCH⟩

lemma outer_origin (J : Finset (Finset Vertex)) (lo hi : Vertex)
    {H : Finset Vertex} (hH : H∈outerHulls J lo hi) :
    ∃ C∈J, filled C lo hi=H := Finset.mem_image.mp ((outer_mem J lo hi H).mp hH).1

structure ClusterFamily (J : Finset (Finset Vertex)) (lo hi : Vertex) : Prop where
  nonempty : ∀ C∈J, C.Nonempty
  bounded : ∀ C∈J, C ⊆ box lo hi
  connected : ∀ C∈J, (star.induce (C:Set Vertex)).Connected
  separated : ∀ C∈J, ∀ D∈J, C≠D → ∀ c∈C, ∀ d∈D, c≠d ∧ ¬star.Adj c d

lemma outer_disjoint (J : Finset (Finset Vertex)) (lo hi : Vertex)
    (hJ : ClusterFamily J lo hi) {H K : Finset Vertex}
    (hH : H∈outerHulls J lo hi) (hK : K∈outerHulls J lo hi) (hHK : H≠K) :
    Disjoint H K := by
  obtain ⟨C,hC,rfl⟩ := outer_origin J lo hi hH
  obtain ⟨D,hD,rfl⟩ := outer_origin J lo hi hK
  have hCD : C≠D := fun h => hHK (congrArg (fun C => filled C lo hi) h)
  rcases filled_laminar C D lo hi (hJ.bounded C hC) (hJ.bounded D hD)
    (hJ.nonempty C hC) (hJ.nonempty D hD) (hJ.connected C hC) (hJ.connected D hD)
    (hJ.separated C hC D hD hCD) with h|h|h
  · exact (hHK (Finset.Subset.antisymm h (((outer_mem J lo hi _).mp hH).2 _
      ((outer_mem J lo hi _).mp hK).1 h))).elim
  · exact (hHK (Finset.Subset.antisymm (((outer_mem J lo hi _).mp hK).2 _
      ((outer_mem J lo hi _).mp hH).1 h) h)).elim
  · exact h

lemma outer_rim_good (J : Finset (Finset Vertex)) (lo hi : Vertex)
    (hJ : ClusterFamily J lo hi) {H K : Finset Vertex}
    (hH : H∈outerHulls J lo hi) (hK : K∈outerHulls J lo hi) :
    Disjoint (rim H) (K:Set Vertex) := by
  by_cases he : H=K
  · subst K
    exact Set.disjoint_left.mpr (fun x hx hxH => hx.1 hxH)
  · have hd := outer_disjoint J lo hi hJ hH hK he
    obtain ⟨C,hC,rfl⟩ := outer_origin J lo hi hH
    obtain ⟨D,hD,rfl⟩ := outer_origin J lo hi hK
    exact disjoint_hulls_rim C D lo hi (hJ.bounded C hC) (hJ.bounded D hD)
      (hJ.separated C hC D hD (fun h => he (congrArg (fun C => filled C lo hi) h))) hd

lemma outer_separated (J : Finset (Finset Vertex)) (lo hi : Vertex)
    (hJ : ClusterFamily J lo hi) {H K : Finset Vertex}
    (hH : H∈outerHulls J lo hi) (hK : K∈outerHulls J lo hi) (hHK : H≠K) :
    ∀ x∈H, ∀ y∈K, x≠y ∧ ¬star.Adj x y := by
  have hd := outer_disjoint J lo hi hJ hH hK hHK
  obtain ⟨C,hC,rfl⟩ := outer_origin J lo hi hH
  obtain ⟨D,hD,rfl⟩ := outer_origin J lo hi hK
  exact disjoint_hulls_separated C D lo hi (hJ.bounded C hC) (hJ.bounded D hD)
    (hJ.separated C hC D hD (fun h => hHK (congrArg (fun C => filled C lo hi) h))) hd

lemma rim_nonempty (H : Finset Vertex) (hne : H.Nonempty) : (rim H).Nonempty := by
  obtain ⟨x,hx,hmax⟩ := Finset.exists_max_image H Prod.fst hne
  let y : Vertex := (x.1+1,x.2)
  have hy : y∉H := by
    intro hh
    have h := hmax y hh
    dsimp [y] at h;omega
  refine ⟨y,(mem_rim_iff_star H y).mpr ⟨hy,x,hx,?_⟩⟩
  exact grid_le_star (adj_right x.1 x.2).symm

theorem outer_hull_geometry (J : Finset (Finset Vertex)) (lo hi : Vertex)
    (hJ : ClusterFamily J lo hi) :
    (∀ C∈J, ∃ H∈outerHulls J lo hi, C ⊆ H) ∧
    (∀ H∈outerHulls J lo hi, ∀ K∈outerHulls J lo hi, H≠K → Disjoint H K) ∧
    (∀ H∈outerHulls J lo hi, ∀ K∈outerHulls J lo hi, Disjoint (rim H) (K:Set Vertex)) ∧
    (∀ H∈outerHulls J lo hi, (rim H).Nonempty ∧
      ∀ x∈rim H, ∀ y∈rim H, ∃ p : (rimNet H).Walk x y,
        (∀ z∈p.support, z∈rim H) ∧ p.length ≤ 8*H.card) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro C hC
    obtain ⟨H,hH,hCH⟩ := hull_subset_outer J lo hi hC
    exact ⟨H,hH,(subset_filled C lo hi (hJ.bounded C hC)).trans hCH⟩
  · intro H hH K hK hHK
    exact outer_disjoint J lo hi hJ hH hK hHK
  · intro H hH K hK
    exact outer_rim_good J lo hi hJ hH hK
  · intro H hH
    obtain ⟨C,hC,rfl⟩ := outer_origin J lo hi hH
    have hne := (hJ.nonempty C hC).mono (subset_filled C lo hi (hJ.bounded C hC))
    refine ⟨rim_nonempty _ hne,?_⟩
    exact incident_rim_paths _ hne
      (filled_star_connected C (hJ.nonempty C hC) lo hi (hJ.bounded C hC) (hJ.connected C hC))
      (filled_complement_connected C lo hi (hJ.bounded C hC))

end SparseHoles

end

end OAI
