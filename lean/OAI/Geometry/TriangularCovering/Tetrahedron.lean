import OAI.Geometry.TriangularCovering.CylinderFamily

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

def faceNormal : Fin 4 → Space := ![!₂[H,0,1], !₂[-H,0,1], !₂[0,H,-1], !₂[0,-H,-1] ]
def faceBound : Fin 4 → ℝ := ![H,H,0,0]
def faceVertices : Fin 4 → Fin 3 → Space
  | 0 => ![point 1 0 0, point 0 1 1, point 0 (-1) 1]
  | 1 => ![point (-1) 0 0, point 0 1 1, point 0 (-1) 1]
  | 2 => ![point 0 1 1, point 1 0 0, point (-1) 0 0]
  | 3 => ![point 0 (-1) 1, point 1 0 0, point (-1) 0 0]
def face (i : Fin 4) : Set Space := {z ∈ K | inner ℝ (faceNormal i) z = faceBound i}

lemma point_coord (z : Space) : z = point (z 0) (z 1) (z 2/H) := by
  ext i
  fin_cases i <;> dsimp [point]
  field_simp [H_ne_zero]

lemma K_halfspaces (z : Space) : z ∈ K ↔ ∀ i, inner ℝ (faceNormal i) z ≤ faceBound i := by
  constructor
  · rintro ⟨x,y,t,ht0,ht1,hx,hy,rfl⟩ i
    have hx' := abs_le.mp hx
    have hy' := abs_le.mp hy
    fin_cases i <;> simp only [inner_coord] <;> dsimp [faceNormal,faceBound,point] <;>
      nlinarith only [H_pos, hx'.1, hx'.2, hy'.1, hy'.2]
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    simp only [inner_coord] at h0 h1 h2 h3
    dsimp [faceNormal,faceBound] at h0 h1 h2 h3
    have ht : H * (z 2 / H) = z 2 := by field_simp [H_ne_zero]
    refine ⟨z 0,z 1,z 2/H,?_,?_,?_,?_,point_coord z⟩
    · nlinarith only [h2,h3,H_pos,ht]
    · nlinarith only [h0,h1,H_pos,ht]
    · rw [abs_le]; constructor <;> nlinarith only [h0,h1,H_pos,ht]
    · rw [abs_le]; constructor <;> nlinarith only [h2,h3,H_pos,ht]

lemma K_convex : Convex ℝ K := by
  have : K = ⋂ i, {z | inner ℝ (faceNormal i) z ≤ faceBound i} := by
    ext z
    simp only [mem_iInter, mem_ofPred_eq, K_halfspaces]
  rw [this]
  exact convex_iInter (fun i => convex_halfSpace_le (innerₛₗ ℝ (faceNormal i)).isLinear (faceBound i))

lemma face_vertices_mem (i : Fin 4) (j : Fin 3) : faceVertices i j ∈ face i := by
  refine ⟨?_,?_⟩
  · rw [K_halfspaces]
    intro k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp only [inner_coord] <;> dsimp [faceVertices,faceNormal,faceBound,point] <;>
      nlinarith only [H_pos]
  · fin_cases i <;> fin_cases j <;>
      simp only [inner_coord] <;> dsimp [faceVertices,faceNormal,faceBound,point] <;> ring

lemma face_convex (i : Fin 4) : Convex ℝ (face i) :=
  K_convex.inter (convex_hyperplane (innerₛₗ ℝ (faceNormal i)).isLinear (faceBound i))

lemma face_eq_triangle (i : Fin 4) :
    face i = triangle (faceVertices i 0) (faceVertices i 1) (faceVertices i 2) := by
  apply Subset.antisymm
  · rintro z ⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hz⟩
    have hx' := abs_le.mp hx
    have hy' := abs_le.mp hy
    rw [mem_triangle_iff]
    fin_cases i
    · have hh : x = 1-t := by
        simp only [inner_coord] at hz
        dsimp [faceNormal,faceBound,point] at hz
        nlinarith only [hz,H_pos]
      refine ⟨(t+y)/2,(t-y)/2,by linarith only [hy'.1],by linarith only [hy'.2],
        by linarith only [ht1],?_⟩
      ext k
      fin_cases k <;> dsimp [faceVertices,point] <;> nlinarith only [hh]
    · have hh : x = t-1 := by
        simp only [inner_coord] at hz
        dsimp [faceNormal,faceBound,point] at hz
        nlinarith only [hz,H_pos]
      refine ⟨(t+y)/2,(t-y)/2,by linarith only [hy'.1],by linarith only [hy'.2],
        by linarith only [ht1],?_⟩
      ext k
      fin_cases k <;> dsimp [faceVertices,point] <;> nlinarith only [hh]
    · have hh : y = t := by
        simp only [inner_coord] at hz
        dsimp [faceNormal,faceBound,point] at hz
        nlinarith only [hz,H_pos]
      refine ⟨(1-t+x)/2,(1-t-x)/2,by linarith only [hx'.1],by linarith only [hx'.2],
        by linarith only [ht0],?_⟩
      ext k
      fin_cases k <;> dsimp [faceVertices,point] <;> nlinarith only [hh]
    · have hh : y = -t := by
        simp only [inner_coord] at hz
        dsimp [faceNormal,faceBound,point] at hz
        nlinarith only [hz,H_pos]
      refine ⟨(1-t+x)/2,(1-t-x)/2,by linarith only [hx'.1],by linarith only [hx'.2],
        by linarith only [ht0],?_⟩
      ext k
      fin_cases k <;> dsimp [faceVertices,point] <;> nlinarith only [hh]
  · apply convexHull_min
    · rintro z ⟨j,rfl⟩
      fin_cases j <;> exact face_vertices_mem i _
    · exact face_convex i

lemma face_cross (i : Fin 4) :
    cross3 (faceVertices i 1-faceVertices i 0) (faceVertices i 2-faceVertices i 0) =
      (![2,-2,2,-2] : Fin 4 → ℝ) i • faceNormal i := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    dsimp [cross3,faceVertices,faceNormal,point,crossProduct] <;> ring

lemma face_projection_measure {u : Space} (hu : ‖u‖ = 1) (i : Fin 4) :
    Measure.euclideanHausdorffMeasure 2 (projection u '' face i) =
      ENNReal.ofReal |inner ℝ (faceNormal i) u| := by
  rw [face_eq_triangle, projection_triangle_measure hu, face_cross,
    inner_smul_right, real_inner_comm u (faceNormal i), abs_mul]
  have hh : |(![2,-2,2,-2] : Fin 4 → ℝ) i| = 2 := by fin_cases i <;> norm_num
  rw [hh]
  congr 1
  ring

end TriangularCovering

namespace TriangularCovering

/-- The four vertices of the regular tetrahedron. -/
def tetraVertices : Fin 4 → Space :=
  ![point 1 0 0,point (-1) 0 0,point 0 1 1,point 0 (-1) 1]

lemma tetraVertices_mem (i : Fin 4) : tetraVertices i ∈ K := by
  fin_cases i
  · exact ⟨1,0,0,by norm_num,by norm_num,by norm_num,by norm_num,rfl⟩
  · exact ⟨-1,0,0,by norm_num,by norm_num,by norm_num,by norm_num,rfl⟩
  · exact ⟨0,1,1,by norm_num,by norm_num,by norm_num,by norm_num,rfl⟩
  · exact ⟨0,-1,1,by norm_num,by norm_num,by norm_num,by norm_num,rfl⟩

lemma K_eq_convexHull : K = convexHull ℝ (range tetraVertices) := by
  apply Subset.antisymm
  · rintro z ⟨x,y,t,_ht0,_ht1,hx,hy,rfl⟩
    have hx' := abs_le.mp hx
    have hy' := abs_le.mp hy
    refine mem_convexHull_of_exists_fintype
      (![(1-t+x)/2,(1-t-x)/2,(t+y)/2,(t-y)/2] : Fin 4 → ℝ)
      tetraVertices ?_ ?_ (fun i => mem_range_self i) ?_
    · intro i
      fin_cases i <;> dsimp <;> linarith only [hx'.1,hx'.2,hy'.1,hy'.2]
    · rw [Fin.sum_univ_four]; dsimp; ring
    · ext i
      fin_cases i <;> simp only [Fin.sum_univ_four] <;> dsimp [tetraVertices,point] <;> ring
  · exact convexHull_min (by rintro _ ⟨i,rfl⟩; exact tetraVertices_mem i) K_convex

lemma K_compact : IsCompact K := by
  rw [K_eq_convexHull]
  exact (finite_range tetraVertices).isCompact_convexHull ℝ

lemma K_interior_nonempty : (interior K).Nonempty := by
  let U : Set Space := {z | ∀ i : Fin 4, inner ℝ (faceNormal i) z < faceBound i}
  have hopen : IsOpen U := by
    have hU : U = ⋂ i, {z | inner ℝ (faceNormal i) z < faceBound i} := by ext z; simp [U]
    rw [hU]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt (by fun_prop) continuous_const)
  have hsub : U ⊆ K := by
    intro z hz
    exact (K_halfspaces z).2 (fun i => (hz i).le)
  have hcenter : point 0 0 (1/2) ∈ U := by
    intro i
    fin_cases i <;> simp only [inner_coord] <;> dsimp [faceNormal,faceBound,point] <;>
      nlinarith only [H_pos]
  exact ⟨point 0 0 (1/2),interior_mono hsub (by simpa only [hopen.interior_eq] using hcenter)⟩

lemma tetra_edge_length {i j : Fin 4} (hij : i ≠ j) :
    dist (tetraVertices i) (tetraVertices j) = 2 := by
  have hs : ‖tetraVertices i-tetraVertices j‖^2 = 4 := by
    rw [← real_inner_self_eq_norm_sq,inner_coord]
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals dsimp [tetraVertices,point]
    all_goals nlinarith only [H_sq]
  rw [dist_eq_norm]
  nlinarith only [hs,norm_nonneg (tetraVertices i-tetraVertices j)]

lemma tetra_affineIndependent : AffineIndependent ℝ tetraVertices := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hv i
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hv
  have h0 := congrArg (fun z : Space => z 0) hv
  have h1 := congrArg (fun z : Space => z 1) hv
  have h2 := congrArg (fun z : Space => z 2) hv
  simp only [Fin.sum_univ_four] at hw h0 h1 h2
  dsimp [tetraVertices,point] at h0 h1 h2
  have hh : w 2 + w 3 = 0 := by nlinarith only [h2,H_pos]
  fin_cases i <;> dsimp <;> linarith only [hw,h0,h1,hh]

def tetraSimplex : Affine.Simplex ℝ Space 3 := ⟨tetraVertices,tetra_affineIndependent⟩

lemma tetraSimplex_equilateral : tetraSimplex.Equilateral :=
  ⟨2,fun _ _ h => tetra_edge_length h⟩

/-- The tetrahedron is compact, convex, and full dimensional, with six edges of length 2. -/
theorem tetrahedron_geometry :
    K = convexHull ℝ (range tetraVertices) ∧ IsCompact K ∧ Convex ℝ K ∧
    (interior K).Nonempty ∧ ∀ i j : Fin 4, i ≠ j → dist (tetraVertices i) (tetraVertices j) = 2 :=
  ⟨K_eq_convexHull,K_compact,K_convex,K_interior_nonempty,fun _ _ h => tetra_edge_length h⟩

end TriangularCovering

end

end OAI
