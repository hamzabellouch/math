import Mathlib
import OAI.Combinatorics.HoneycombCorridor.BoundaryArcs

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def sourceExits (D : Finset Vertex) (g : Germ) : Finset (List Bool) := by
  classical
  exact (leaves D g).filter fun w => (terminalGerm g w).1 ∉ D

def ConvexBoundaryFlux : Prop := ∀ (D : Finset Vertex) (g : Germ),
  AdmissiblyConvex D → g.1 ∈ D → (reverseGerm g).1 ∉ D →
    (∑ w ∈ sourceExits D g, wordWeight w) = 1 ∧
    (∑ w ∈ sourceExits D g, criticalActivity ^ w.length) ≤
      (Real.cos (3 * Real.pi / 8))⁻¹



def coordinateIndex (v : Vertex) (k : Fin 3) : ℤ :=
  match v with
  | .up i j => if k = 0 then 3*j+1 else if k = 1 then 3*i+1 else 3*(i+j)+2
  | .down i j => if k = 0 then 3*j+2 else if k = 1 then 3*i+2 else 3*(i+j+1)+1

theorem coordinateIndex_box_iff (lo hi : Fin 3 → ℤ) (v : Vertex) (k : Fin 3) :
    (3*lo k < coordinateIndex v k ∧ coordinateIndex v k < 3*hi k) ↔
      lo k ≤ boxIndex v k ∧ boxIndex v k < hi k := by
  cases v <;> fin_cases k <;> simp [coordinateIndex,boxIndex] <;> omega

theorem coordinateIndex_increase (v : Vertex) (k : Fin 3) :
    ∃ l : Fin 3, coordinateIndex v k < coordinateIndex (neighbor v l) k := by
  cases v <;> fin_cases k
  all_goals first
    | (refine ⟨0,?_⟩; simp [coordinateIndex,neighbor] <;> omega)
    | (refine ⟨1,?_⟩; simp [coordinateIndex,neighbor] <;> omega)
    | (refine ⟨2,?_⟩; simp [coordinateIndex,neighbor]; omega)

theorem coordinateIndex_decrease (v : Vertex) (k : Fin 3) :
    ∃ l : Fin 3, coordinateIndex (neighbor v l) k < coordinateIndex v k := by
  cases v <;> fin_cases k
  all_goals first
    | (refine ⟨0,?_⟩; simp [coordinateIndex,neighbor] <;> omega)
    | (refine ⟨1,?_⟩; simp [coordinateIndex,neighbor] <;> omega)
    | (refine ⟨2,?_⟩; simp [coordinateIndex,neighbor]; omega)

theorem Polygon.interior_maximum_principle (P : Polygon) (f : Vertex → ℤ)
    (hf : ∀ v, ∃ k : Fin 3, f v < f (neighbor v k)) (M : ℤ)
    (hbd : ∀ v ∈ P.vertices, f v < M) : ∀ v ∈ P.interior, f v < M := by
  classical
  intro v hv
  let R := P.interior.image f
  have hvR : f v ∈ R := Finset.mem_image.mpr ⟨v,hv,rfl⟩
  have hne : R.Nonempty := ⟨f v,hvR⟩
  let m := R.max' hne
  obtain ⟨u,hu,hum⟩ := Finset.mem_image.mp (R.max'_mem hne)
  obtain ⟨k,hk⟩ := hf u
  have hn : neighbor u k ∉ P.interior := by
    intro hn
    have hle := R.le_max' _ (Finset.mem_image.mpr ⟨neighbor u k,hn,rfl⟩)
    change f (neighbor u k) ≤ m at hle
    change f u = m at hum
    omega
  have hb := P.interior_exit_on_boundary u k hu hn
  have hbound := hbd _ hb
  have hle := R.le_max' (f v) hvR
  change f v ≤ m at hle
  change f u = m at hum
  omega

theorem admissiblyConvex_filled (D : Finset Vertex) (hD : AdmissiblyConvex D) : Filled D := by
  obtain ⟨lo,hi,hbox⟩ := admissiblyConvex_box D hD
  intro P hP v hv
  apply (hbox v).mpr
  intro k
  apply (coordinateIndex_box_iff lo hi v k).mp
  have hp : P.vertices ⊆ D := (mem_polygons D P).mp hP
  have hbd (u : Vertex) (hu : u ∈ P.vertices) :
      3*lo k < coordinateIndex u k ∧ coordinateIndex u k < 3*hi k :=
    (coordinateIndex_box_iff lo hi u k).mpr ((hbox u).mp (hp hu) k)
  have hh := P.interior_maximum_principle (fun u => coordinateIndex u k)
    (fun u => coordinateIndex_increase u k) (3*hi k) (fun u hu => (hbd u hu).2) v hv
  have hl := P.interior_maximum_principle (fun u => -coordinateIndex u k)
    (fun u => by obtain ⟨l,hl⟩ := coordinateIndex_decrease u k; exact ⟨l,by omega⟩)
    (-3*lo k) (fun u hu => by have := (hbd u hu).1; omega) v hv
  omega

end PolynomialVacuumBridge.Corridor

end

end OAI
