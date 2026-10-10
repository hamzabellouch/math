import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.BadClusters
import OAI.Probability.LatticeSurface.Coercivity.FilledHull
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.GridSpreadTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTraceAnalytic
import OAI.Probability.LatticeSurface.Coercivity.GridTraceGeometry
import OAI.Probability.LatticeSurface.Coercivity.GridTraceKernel
import OAI.Probability.LatticeSurface.Coercivity.GridTraceMain
import OAI.Probability.LatticeSurface.Coercivity.GridTraceScale
import OAI.Probability.LatticeSurface.Coercivity.GridTraceTelescope
import OAI.Probability.LatticeSurface.Coercivity.HoleEdges
import OAI.Probability.LatticeSurface.Coercivity.HoleExtension
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry
import OAI.Probability.LatticeSurface.Coercivity.HoleIncident
import OAI.Probability.LatticeSurface.Coercivity.HoleLocal
import OAI.Probability.LatticeSurface.Coercivity.HoleSize
import OAI.Probability.LatticeSurface.Coercivity.HoleStar
import OAI.Probability.LatticeSurface.Coercivity.HullMore
import OAI.Probability.LatticeSurface.Coercivity.HullRims
import OAI.Probability.LatticeSurface.Coercivity.OuterHulls
import OAI.Probability.LatticeSurface.Convexity.WeightedHolder

namespace OAI

noncomputable section

open scoped BigOperators

namespace SparseHoles

noncomputable def squareEdges (N : ℕ) : Finset Edge := by
  classical
  exact (incidentEdges (box (0,0) (N,N))).filter (fun e => ∀ z∈e,z∈box (0,0) (N,N))

def buffer (N : ℕ) : Finset Vertex := box (-(2*N:ℤ),-(2*N:ℤ)) (3*N,3*N)

noncomputable def goodEnergy (L : Finset (Finset Vertex)) (N : ℕ) (u : Vertex → ℝ) : ℝ := by
  classical
  exact ∑ e∈(incidentEdges (buffer N)).filter (goodEdge L),(edgeAbs u e)^2

attribute [local instance] Classical.propDecidable

lemma horizontal_injective : Function.Injective (fun x : Vertex => s(x,(x.1+1,x.2))) := by
  intro x y h
  rcases Sym2.eq_iff.mp h with hh|hh
  · exact hh.1
  · have h1 := congrArg Prod.fst hh.1
    have h2 := congrArg Prod.fst hh.2
    dsimp at h1 h2
    omega

lemma vertical_injective : Function.Injective (fun x : Vertex => s(x,(x.1,x.2+1))) := by
  intro x y h
  rcases Sym2.eq_iff.mp h with hh|hh
  · exact hh.1
  · have h1 := congrArg Prod.snd hh.1
    have h2 := congrArg Prod.snd hh.2
    dsimp at h1 h2
    omega

lemma squareEdges_good (N : ℕ) : ∀ e∈squareEdges N,e∈grid.edgeSet := by
  intro e he
  exact ((mem_incidentEdges _ _).mp (Finset.mem_filter.mp he).1).1

lemma squareEdges_endpoints (N : ℕ) : ∀ e∈squareEdges N,∀ z∈e,z∈box (0,0) (N,N) := by
  intro e he
  exact (Finset.mem_filter.mp he).2

lemma square_horizontal (N : ℕ) {x : Vertex}
    (hx : x∈(Finset.Icc (0:ℤ) ((N:ℤ)-1)) ×ˢ (Finset.Icc (0:ℤ) N)) :
    s(x,(x.1+1,x.2))∈squareEdges N := by
  have hx := Finset.mem_product.mp hx
  have hx1 := Finset.mem_Icc.mp hx.1
  have hx2 := Finset.mem_Icc.mp hx.2
  have hxQ : x∈box (0,0) (N,N) := mem_box.mpr ⟨by omega,by omega,by omega,by omega⟩
  have hx'Q : (x.1+1,x.2)∈box (0,0) (N,N) := mem_box.mpr ⟨by omega,by omega,by omega,by omega⟩
  apply Finset.mem_filter.mpr
  refine ⟨(mem_incidentEdges _ _).mpr ⟨adj_right _ _,x,hxQ,by simp⟩,?_⟩
  intro z hz
  rcases Sym2.mem_iff.mp hz with rfl|rfl
  · exact hxQ
  · exact hx'Q

lemma square_vertical (N : ℕ) {x : Vertex}
    (hx : x∈(Finset.Icc (0:ℤ) N) ×ˢ (Finset.Icc (0:ℤ) ((N:ℤ)-1))) :
    s(x,(x.1,x.2+1))∈squareEdges N := by
  have hx := Finset.mem_product.mp hx
  have hx1 := Finset.mem_Icc.mp hx.1
  have hx2 := Finset.mem_Icc.mp hx.2
  have hxQ : x∈box (0,0) (N,N) := mem_box.mpr ⟨by omega,by omega,by omega,by omega⟩
  have hx'Q : (x.1,x.2+1)∈box (0,0) (N,N) := mem_box.mpr ⟨by omega,by omega,by omega,by omega⟩
  apply Finset.mem_filter.mpr
  refine ⟨(mem_incidentEdges _ _).mpr ⟨adj_up _ _,x,hxQ,by simp⟩,?_⟩
  intro z hz
  rcases Sym2.mem_iff.mp hz with rfl|rfl
  · exact hxQ
  · exact hx'Q

lemma energy_le_square (N : ℕ) (p : ℝ) (u : Vertex → ℝ) :
    GridTrace.energy N p u ≤ 2*∑ e∈squareEdges N,(edgeAbs u e)^p := by
  let H := (Finset.Icc (0:ℤ) ((N:ℤ)-1)) ×ˢ (Finset.Icc (0:ℤ) N)
  let V := (Finset.Icc (0:ℤ) N) ×ˢ (Finset.Icc (0:ℤ) ((N:ℤ)-1))
  have hH : ∑ x∈H,|u (x.1+1,x.2)-u x|^p ≤ ∑ e∈squareEdges N,(edgeAbs u e)^p := by
    calc
      _ = ∑ e∈H.image (fun x => s(x,(x.1+1,x.2))),(edgeAbs u e)^p := by
        rw [Finset.sum_image (fun x hx y hy hh => horizontal_injective hh)]
        rfl
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by
        intro e he;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he;exact square_horizontal N hx)
        (fun e he hne => Real.rpow_nonneg (edgeAbs_nonneg _ _) _)
  have hV : ∑ x∈V,|u (x.1,x.2+1)-u x|^p ≤ ∑ e∈squareEdges N,(edgeAbs u e)^p := by
    calc
      _ = ∑ e∈V.image (fun x => s(x,(x.1,x.2+1))),(edgeAbs u e)^p := by
        rw [Finset.sum_image (fun x hx y hy hh => vertical_injective hh)]
        rfl
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by
        intro e he;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he;exact square_vertical N hx)
        (fun e he hne => Real.rpow_nonneg (edgeAbs_nonneg _ _) _)
  have he : GridTrace.energy N p u = (∑ x∈H,|u (x.1+1,x.2)-u x|^p)+(∑ x∈V,|u (x.1,x.2+1)-u x|^p) := by
    simp only [GridTrace.energy,H,V,Finset.sum_product]
  rw [he];linarith

lemma grid_energy_nonneg (N : ℕ) (p : ℝ) (u : Vertex → ℝ) : 0 ≤ GridTrace.energy N p u := by
  unfold GridTrace.energy
  exact add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)

lemma goodEnergy_nonneg (L : Finset (Finset Vertex)) (N : ℕ) (u : Vertex → ℝ) :
    0 ≤ goodEnergy L N u := Finset.sum_nonneg fun _ _ => sq_nonneg _

end SparseHoles

end

end OAI
