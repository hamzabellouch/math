import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Geometry.SingularHomology.SingularSubdivision
import OAI.Geometry.SingularHomology.AffineSimplexGeometry

namespace OAI

noncomputable section

namespace Problem340.SingularSubdivision

abbrev StandardSimplex (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n + 1))

def simplexCenters (k : ℕ) : Centers (StandardSimplex k) :=
  fun _ p => AffineSimplex.simplexBarycenter p

def standardVertices (n : ℕ) : Fin (n + 1) → StandardSimplex n := Convexity.StdSimplex.single

def universalSubdivision (n : ℕ) : Chains (StandardSimplex n) (n + 1) :=
  subdivision (simplexCenters n) (n + 1) (generator (standardVertices n))

def universalHomotopy (n : ℕ) : Chains (StandardSimplex n) (n + 2) :=
  subdivisionHomotopy (simplexCenters n) (n + 1) (generator (standardVertices n))

lemma map_centers {k l : ℕ} (f : Fin (k + 1) → Fin (l + 1))
    (n : ℕ) (p : Fin (n + 1) → StandardSimplex k) :
    Convexity.StdSimplex.map f (simplexCenters k n p) =
      simplexCenters l n (Convexity.StdSimplex.map f ∘ p) :=
  AffineSimplex.map_simplexBarycenter f p

lemma affine_centers {k l : ℕ} (v : Fin (k + 1) → StandardSimplex l)
    (n : ℕ) (p : Fin (n + 1) → StandardSimplex k) :
    AffineSimplex.simplexRealizeMap v (simplexCenters k n p) =
      simplexCenters l n (AffineSimplex.simplexRealizeMap v ∘ p) :=
  AffineSimplex.simplexRealizeMap_barycenter v p

lemma standardVertices_face (n : ℕ) (i : Fin (n + 2)) :
    face i (standardVertices (n + 1)) =
      Convexity.StdSimplex.map i.succAbove ∘ standardVertices n := by
  funext j
  simp [face, standardVertices]

theorem universalSubdivision_boundary (n : ℕ) :
    boundary (n + 1) (universalSubdivision (n + 1)) =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val •
        mapVertices (Convexity.StdSimplex.map i.succAbove) (n + 1) (universalSubdivision n) := by
  unfold universalSubdivision
  rw [boundary_subdivision, boundary_generator, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, standardVertices_face,
    ← mapVertices_generator (Convexity.StdSimplex.map i.succAbove)]
  rw [mapVertices_subdivision _ _ _ (map_centers i.succAbove)]

theorem universalHomotopy_boundary_zero :
    boundary 1 (universalHomotopy 0) =
      generator (standardVertices 0) - universalSubdivision 0 := by
  unfold universalHomotopy universalSubdivision
  rw [boundary_subdivisionHomotopy, subdivisionHomotopy_zero, sub_zero]

theorem universalHomotopy_boundary (n : ℕ) :
    boundary (n + 2) (universalHomotopy (n + 1)) =
      generator (standardVertices (n + 1)) - universalSubdivision (n + 1) -
        ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val •
          mapVertices (Convexity.StdSimplex.map i.succAbove) (n + 2) (universalHomotopy n) := by
  unfold universalHomotopy universalSubdivision
  rw [boundary_subdivisionHomotopy, boundary_generator, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, standardVertices_face,
    ← mapVertices_generator (Convexity.StdSimplex.map i.succAbove)]
  rw [mapVertices_subdivisionHomotopy _ _ _ (map_centers i.succAbove)]

lemma simplexCenters_zero (k : ℕ) (p : Fin 1 → StandardSimplex k) :
    simplexCenters k 0 p = p 0 := by
  change AffineSimplex.simplexRealizeMap p Convexity.StdSimplex.barycenter = p 0
  rw [show (Convexity.StdSimplex.barycenter : Convexity.StdSimplex ℝ (Fin 1)) =
    Convexity.StdSimplex.single 0 from Subsingleton.elim _ _]
  exact AffineSimplex.simplexRealizeMap_vertex p 0

theorem subdivision_one (k : ℕ) (c : Chains (StandardSimplex k) 1) :
    subdivision (simplexCenters k) 1 c = c := by
  have h : subdivision (simplexCenters k) 1 = LinearMap.id := by
    apply linearMap_ext
    intro p
    have ht : Fin.cons (p 0) (face 0 p) = p := by
      funext i
      fin_cases i
      simp
    simp [simplexCenters_zero, ht]
  exact LinearMap.congr_fun h c

theorem subdivisionHomotopy_one (k : ℕ) (c : Chains (StandardSimplex k) 1) :
    subdivisionHomotopy (simplexCenters k) 1 c = 0 := by
  have h : subdivisionHomotopy (simplexCenters k) 1 = 0 := by
    apply linearMap_ext
    intro p
    rw [subdivisionHomotopy_generator, subdivision_one]
    simp
  exact LinearMap.congr_fun h c

@[simp] theorem universalSubdivision_zero :
    universalSubdivision 0 = generator (standardVertices 0) :=
  subdivision_one 0 _

@[simp] theorem universalHomotopy_zero : universalHomotopy 0 = 0 :=
  subdivisionHomotopy_one 0 _

theorem mapVertices_universalSubdivision {k n : ℕ}
    (p : Fin (n + 1) → StandardSimplex k) :
    mapVertices (AffineSimplex.simplexRealizeMap p) (n + 1) (universalSubdivision n) =
      subdivision (simplexCenters k) (n + 1) (generator p) := by
  unfold universalSubdivision
  rw [mapVertices_subdivision _ _ _ (affine_centers p), mapVertices_generator]
  congr 2
  funext i
  exact AffineSimplex.simplexRealizeMap_vertex p i

theorem mapVertices_universalHomotopy {k n : ℕ}
    (p : Fin (n + 1) → StandardSimplex k) :
    mapVertices (AffineSimplex.simplexRealizeMap p) (n + 2) (universalHomotopy n) =
      subdivisionHomotopy (simplexCenters k) (n + 1) (generator p) := by
  unfold universalHomotopy
  rw [mapVertices_subdivisionHomotopy _ _ _ (affine_centers p), mapVertices_generator]
  congr 2
  funext i
  exact AffineSimplex.simplexRealizeMap_vertex p i

end Problem340.SingularSubdivision

end

end OAI
