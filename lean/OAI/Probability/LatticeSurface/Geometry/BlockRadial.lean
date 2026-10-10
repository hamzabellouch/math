import Mathlib
import OAI.Probability.LatticeSurface.Convexity.RadialExposure
import OAI.Probability.LatticeSurface.Geometry.BlockEdgeGeometry
import OAI.Probability.LatticeSurface.Geometry.BlockFacetGeometry
import OAI.Probability.LatticeSurface.Geometry.BlockVolume
import OAI.Probability.LatticeSurface.Geometry.EdgeCoordinates
import OAI.Probability.LatticeSurface.Geometry.FacetExposure
import OAI.Probability.LatticeSurface.Geometry.TriangularCover
import OAI.Probability.LatticeSurface.Geometry.TriangularGeometry

namespace OAI

open MeasureTheory

open scoped ENNReal

noncomputable section

namespace TriangularLipschitz

end TriangularLipschitz

namespace FacetExposure

end FacetExposure

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

end TriangularLipschitz

open MeasureTheory Set

open scoped ENNReal

noncomputable section

namespace EdgeCoordinates

end EdgeCoordinates

namespace EdgeCoordinates

end EdgeCoordinates

namespace EdgeCoordinates

end EdgeCoordinates

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

lemma radialPoint_zero (L : ℕ) (side : Fin 4) : radialPoint L side 0=faceCenter L side := by
  fin_cases side <;> simp [radialPoint,faceCenter]

lemma radialPoint_center (m : ℕ) (side : Fin 4) : radialPoint (2*m) side m=((m:ℤ),(m:ℤ)) := by
  fin_cases side <;> simp [radialPoint] <;> omega

lemma radialPoint_mem_box {m k : ℕ} (hk : k ≤ m) (side : Fin 4) :
    radialPoint (2*m) side k ∈ box (2*m) := by
  fin_cases side <;> simp [radialPoint,mem_box] <;> omega

lemma radialPoint_mem_interior {m k : ℕ} (hk0 : 0 < k) (hk : k ≤ m) (side : Fin 4) :
    radialPoint (2*m) side k ∈ interior (2*m) := by
  fin_cases side <;> simp [radialPoint,interior] <;> omega

lemma faceCenter_mem_shell {m : ℕ} (hm : 0 < m) (side : Fin 4) :
    faceCenter (2*m) side ∈ shell (2*m) := by
  fin_cases side <;> simp [faceCenter,mem_shell,mem_box] <;> omega

lemma radialPoint_fixed_iff {m k : ℕ} (hm : 0 < m) (hk : k ≤ m) (side : Fin 4) :
    radialPoint (2*m) side k ∉ interior (2*m) ↔ k=0 := by
  constructor
  · intro hi
    by_contra h
    exact hi (radialPoint_mem_interior (Nat.pos_of_ne_zero h) hk side)
  · rintro rfl
    rw [radialPoint_zero]
    exact (shell_eq_box_not_interior.mp (faceCenter_mem_shell hm side)).2

lemma radialPoint_adj (L k : ℕ) (side : Fin 4) :
    Adj (radialPoint L side k) (radialPoint L side (k+1)) := by
  fin_cases side <;> simp [radialPoint,Adj] <;> omega

lemma shifted_radial_facet {m k : ℕ} {σ : ℝ} {h χ g : Vertex → ℝ}
    (hm : 0 < m) (hk : k < m) (side : Fin 4)
    (hg : ∀ b ∈ shell (2*m), g b=h b)
    (hgrad : |g (radialPoint (2*m) side k)-g (radialPoint (2*m) side (k+1))|=1) :
    let x := radialPoint (2*m) side k
    let y := radialPoint (2*m) side (k+1)
    let τ := g y-g x
    τ*(filledHeight (2*m) (fun b => h b+σ*χ b)
      (fun z => g z+σ*χ (faceCenter (2*m) side)) y-
      filledHeight (2*m) (fun b => h b+σ*χ b)
      (fun z => g z+σ*χ (faceCenter (2*m) side)) x)=1 := by
  dsimp only
  have hy := radialPoint_mem_interior (by omega : 0 < k+1) (by omega : k+1 ≤ m) side
  have hgabs : |g (radialPoint (2*m) side (k+1))-g (radialPoint (2*m) side k)|=1 := by
    rwa [abs_sub_comm]
  have hsquare : (g (radialPoint (2*m) side (k+1))-g (radialPoint (2*m) side k))^2=1 := by
    nlinarith [sq_abs (g (radialPoint (2*m) side (k+1))-g (radialPoint (2*m) side k))]
  rw [filledHeight, dite_eq_left hy]
  by_cases hx : radialPoint (2*m) side k ∈ interior (2*m)
  · rw [filledHeight,dite_eq_left hx]
    nlinarith
  · have hk0 := (radialPoint_fixed_iff hm (Nat.le_of_lt hk) side).mp hx
    subst k
    rw [filledHeight,dite_eq_right hx,radialPoint_zero]
    have hg0 := hg (faceCenter (2*m) side) (faceCenter_mem_shell hm side)
    rw [radialPoint_zero] at hsquare
    rw [← hg0]
    nlinarith

lemma shifted_shell_error {L : ℕ} {h χ g : Vertex → ℝ} {σ β : ℝ} {v : Vertex}
    (_hβ : 0 < β) (hv : v ∈ shell L)
    (hg : ∀ b ∈ shell L, g b=h b)
    (hplus : 0 < fillingVolume L (fun x => h x+χ x))
    (hminus : 0 < fillingVolume L (fun x => h x-χ x))
    (hσ : |σ| * (2*(L:ℝ)) ≤ β/4) :
    ∀ b ∈ shell L, |(h b+σ*χ b)-(g b+σ*χ v)| ≤ β/4 := by
  intro b hb
  rw [hg b hb]
  calc
    _ = |σ| * |χ b-χ v| := by rw [← abs_mul]; congr 1; ring
    _ ≤ |σ| * latticeDist b v := mul_le_mul_of_nonneg_left
      (endpoint_shell_difference hplus hminus hb hv) (abs_nonneg σ)
    _ ≤ |σ| * (2*(L:ℝ)) := mul_le_mul_of_nonneg_left
      (latticeDist_box_le (shell_eq_box_not_interior.mp hb).1 (shell_eq_box_not_interior.mp hv).1)
      (abs_nonneg σ)
    _ ≤ β/4 := hσ

end TriangularLipschitz

end
end

end OAI
