import Mathlib
import OAI.Combinatorics.HoneycombCorridor.Polygons

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def boxIndex : Vertex → Fin 3 → ℤ
  | .up i j, k => if k = 0 then j else if k = 1 then i else i+j
  | .down i j, k => if k = 0 then j else if k = 1 then i else i+j+1

def BoxMem (lo hi : Fin 3 → ℤ) (v : Vertex) : Prop :=
  ∀ k, lo k ≤ boxIndex v k ∧ boxIndex v k < hi k

theorem tilingCoordinate_index (v : Vertex) (k : Fin 3) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      tilingCoordinate k (position v) = (boxIndex v k : ℝ) + a := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  cases v with
  | up i j =>
    fin_cases k
    · refine ⟨1/3,by norm_num,by norm_num,?_⟩
      simp [tilingCoordinate,position,boxIndex]
      field_simp
    · refine ⟨1/3,by norm_num,by norm_num,?_⟩
      simp [tilingCoordinate,position,boxIndex]
      field_simp
      ring
    · refine ⟨2/3,by norm_num,by norm_num,?_⟩
      simp [tilingCoordinate,position,boxIndex]
      field_simp
      ring
  | down i j =>
    fin_cases k
    · refine ⟨2/3,by norm_num,by norm_num,?_⟩
      simp [tilingCoordinate,position,boxIndex]
      field_simp
    · refine ⟨2/3,by norm_num,by norm_num,?_⟩
      simp [tilingCoordinate,position,boxIndex]
      field_simp
      ring
    · refine ⟨1/3,by norm_num,by norm_num,?_⟩
      simp [tilingCoordinate,position,boxIndex]
      field_simp
      ring

theorem integer_bounds_fraction (lo hi n : ℤ) (a : ℝ) (ha : 0 < a) (ha' : a < 1) :
    ((lo : ℝ) < (n : ℝ)+a ∧ (n : ℝ)+a < (hi : ℝ)) ↔ lo ≤ n ∧ n < hi := by
  constructor
  · rintro ⟨hl,hh⟩
    constructor
    · by_contra h
      have h' : n+1 ≤ lo := by omega
      have : (n : ℝ)+1 ≤ (lo : ℝ) := by exact_mod_cast h'
      linarith
    · by_contra h
      have h' : hi ≤ n := by omega
      have : (hi : ℝ) ≤ (n : ℝ) := by exact_mod_cast h'
      linarith
  · rintro ⟨hl,hh⟩
    have hl' : (lo : ℝ) ≤ (n : ℝ) := by exact_mod_cast hl
    have hh' : (n : ℝ)+1 ≤ (hi : ℝ) := by exact_mod_cast (show n+1 ≤ hi by omega)
    constructor <;> linarith

theorem admissiblyConvex_box (D : Finset Vertex) (hD : AdmissiblyConvex D) :
    ∃ lo hi : Fin 3 → ℤ, ∀ v, v ∈ D ↔ BoxMem lo hi v := by
  obtain ⟨lo,hi,h⟩ := hD
  refine ⟨lo,hi,fun v => ?_⟩
  rw [h]
  apply forall_congr'
  intro k
  obtain ⟨a,ha,ha',he⟩ := tilingCoordinate_index v k
  rw [he]
  exact integer_bounds_fraction _ _ _ _ ha ha'

def starFaces (D : Finset Vertex) : Finset FaceIndex :=
  D.biUnion fun v => Finset.univ.image fun k : Fin 3 => leftFace (v,k)

theorem mem_starFaces (D : Finset Vertex) (a : FaceIndex) :
    a ∈ starFaces D ↔ ∃ v ∈ faceVertices a, v ∈ D := by
  simp only [starFaces,Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and,
    mem_faceVertices]
  aesop

theorem incident_mem_starFaces {D : Finset Vertex} {v : Vertex} (hv : v ∈ D)
    (k : Fin 3) : leftFace (v,k) ∈ starFaces D := by
  apply (mem_starFaces D _).mpr
  exact ⟨v,(mem_faceVertices _ _).mpr ⟨k,rfl⟩,hv⟩



theorem box_opposite_face (lo hi : Fin 3 → ℤ) (v r : Vertex) (k : Fin 3)
    (hv : BoxMem lo hi (neighbor v k))
    (hr : r ∈ faceVertices (leftFace (v,k+1)))
    (hr' : BoxMem lo hi r) : BoxMem lo hi v := by
  cases v <;> fin_cases k <;>
    simp only [leftFace,Fin.reduceAdd,Fin.zero_eta,Fin.isValue,Fin.reduceEq,ite_true,
      ite_false,faceVertices,Finset.mem_insert,Finset.mem_singleton] at hr <;>
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [BoxMem,Fin.forall_fin_succ,boxIndex,neighbor] <;> omega

theorem outside_opposite_face (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (v : Vertex) (k : Fin 3) (hv : v ∉ D) (hn : neighbor v k ∈ D) :
    leftFace (v,k+1) ∉ starFaces D := by
  obtain ⟨lo,hi,hbox⟩ := admissiblyConvex_box D hD
  intro hf
  obtain ⟨r,hr,hr'⟩ := (mem_starFaces D _).mp hf
  exact hv ((hbox v).mpr (box_opposite_face lo hi v r k ((hbox _).mp hn) hr
    ((hbox _).mp hr')))

theorem box_two_faces_up0 (lo hi : Fin 3 → ℤ) (i j : ℤ) (r s : Vertex)
    (hr : r ∈ faceVertices (rightFace (.up i j,0)))
    (hs : s ∈ faceVertices (leftFace
      (neighbor (.up i j) ((0 : Fin 3)+1),(0 : Fin 3)+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi (.up i j) ∨ BoxMem lo hi (neighbor (.up i j) ((0 : Fin 3)+1)) := by
  simp only [rightFace,reverseGerm,neighbor,leftFace,Fin.reduceAdd,
    Fin.isValue,Fin.reduceEq,ite_true,ite_false,faceVertices,Finset.mem_insert,
    Finset.mem_singleton] at hr hs
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [BoxMem,Fin.forall_fin_succ,boxIndex,neighbor] <;> omega

theorem box_two_faces_up1 (lo hi : Fin 3 → ℤ) (i j : ℤ) (r s : Vertex)
    (hr : r ∈ faceVertices (rightFace (.up i j,1)))
    (hs : s ∈ faceVertices (leftFace
      (neighbor (.up i j) ((1 : Fin 3)+1),(1 : Fin 3)+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi (.up i j) ∨ BoxMem lo hi (neighbor (.up i j) ((1 : Fin 3)+1)) := by
  simp only [rightFace,reverseGerm,neighbor,leftFace,Fin.reduceAdd,
    Fin.isValue,Fin.reduceEq,ite_true,ite_false,faceVertices,Finset.mem_insert,
    Finset.mem_singleton] at hr hs
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [BoxMem,Fin.forall_fin_succ,boxIndex,neighbor] <;> omega

theorem box_two_faces_up2 (lo hi : Fin 3 → ℤ) (i j : ℤ) (r s : Vertex)
    (hr : r ∈ faceVertices (rightFace (.up i j,2)))
    (hs : s ∈ faceVertices (leftFace
      (neighbor (.up i j) ((2 : Fin 3)+1),(2 : Fin 3)+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi (.up i j) ∨ BoxMem lo hi (neighbor (.up i j) ((2 : Fin 3)+1)) := by
  simp only [rightFace,reverseGerm,neighbor,leftFace,Fin.reduceAdd,
    Fin.isValue,Fin.reduceEq,ite_true,ite_false,faceVertices,Finset.mem_insert,
    Finset.mem_singleton] at hr hs
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [BoxMem,Fin.forall_fin_succ,boxIndex,neighbor] <;> omega

theorem box_two_faces_down0 (lo hi : Fin 3 → ℤ) (i j : ℤ) (r s : Vertex)
    (hr : r ∈ faceVertices (rightFace (.down i j,0)))
    (hs : s ∈ faceVertices (leftFace
      (neighbor (.down i j) ((0 : Fin 3)+1),(0 : Fin 3)+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi (.down i j) ∨ BoxMem lo hi (neighbor (.down i j) ((0 : Fin 3)+1)) := by
  simp only [rightFace,reverseGerm,neighbor,leftFace,Fin.reduceAdd,
    Fin.isValue,Fin.reduceEq,ite_true,ite_false,faceVertices,Finset.mem_insert,
    Finset.mem_singleton] at hr hs
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [BoxMem,Fin.forall_fin_succ,boxIndex,neighbor] <;> omega

theorem box_two_faces_down1 (lo hi : Fin 3 → ℤ) (i j : ℤ) (r s : Vertex)
    (hr : r ∈ faceVertices (rightFace (.down i j,1)))
    (hs : s ∈ faceVertices (leftFace
      (neighbor (.down i j) ((1 : Fin 3)+1),(1 : Fin 3)+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi (.down i j) ∨ BoxMem lo hi (neighbor (.down i j) ((1 : Fin 3)+1)) := by
  simp only [rightFace,reverseGerm,neighbor,leftFace,Fin.reduceAdd,
    Fin.isValue,Fin.reduceEq,ite_true,ite_false,faceVertices,Finset.mem_insert,
    Finset.mem_singleton] at hr hs
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [BoxMem,Fin.forall_fin_succ,boxIndex,neighbor] <;> omega

theorem box_two_faces_down2 (lo hi : Fin 3 → ℤ) (i j : ℤ) (r s : Vertex)
    (hr : r ∈ faceVertices (rightFace (.down i j,2)))
    (hs : s ∈ faceVertices (leftFace
      (neighbor (.down i j) ((2 : Fin 3)+1),(2 : Fin 3)+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi (.down i j) ∨ BoxMem lo hi (neighbor (.down i j) ((2 : Fin 3)+1)) := by
  simp only [rightFace,reverseGerm,neighbor,leftFace,Fin.reduceAdd,
    Fin.isValue,Fin.reduceEq,ite_true,ite_false,faceVertices,Finset.mem_insert,
    Finset.mem_singleton] at hr hs
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [BoxMem,Fin.forall_fin_succ,boxIndex,neighbor] <;> omega

theorem box_two_faces (lo hi : Fin 3 → ℤ) (v r s : Vertex) (k : Fin 3)
    (hr : r ∈ faceVertices (rightFace (v,k)))
    (hs : s ∈ faceVertices (leftFace (neighbor v (k+1),k+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi v ∨ BoxMem lo hi (neighbor v (k+1)) := by
  cases v with
  | up i j =>
    fin_cases k
    · exact box_two_faces_up0 lo hi i j r s hr hs hr' hs'
    · exact box_two_faces_up1 lo hi i j r s hr hs hr' hs'
    · exact box_two_faces_up2 lo hi i j r s hr hs hr' hs'
  | down i j =>
    fin_cases k
    · exact box_two_faces_down0 lo hi i j r s hr hs hr' hs'
    · exact box_two_faces_down1 lo hi i j r s hr hs hr' hs'
    · exact box_two_faces_down2 lo hi i j r s hr hs hr' hs'

end PolynomialVacuumBridge.Corridor

end

end OAI
