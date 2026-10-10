import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Geometry.SingularHomology.AffineSimplexGeometry
import OAI.Geometry.SingularHomology.SingularChainsFinsuppBoundary
import OAI.Geometry.SingularHomology.BarycentricSubdivision

namespace OAI

noncomputable section

namespace Problem340.SimplexSingularRealization

open SingularSubdivision

abbrev Simplex (k : ℕ) := Convexity.StdSimplex ℝ (Fin (k + 1))

def realize (k n : ℕ) :
    Chains (Simplex k) (n + 1) →ₗ[ℝ] (realSingularChainComplex (Simplex k)).X n :=
  Finsupp.linearCombination ℝ (fun v =>
    SingularChainFormulas.simplexChain (AffineSimplex.simplexRealizeMap v))

@[simp] theorem realize_generator (k n : ℕ) (v : Fin (n + 1) → Simplex k) :
    realize k n (generator v) =
      SingularChainFormulas.simplexChain (AffineSimplex.simplexRealizeMap v) := by
  simp [realize, generator]

theorem face_simplexRealizeMap (k n : ℕ) (v : Fin (n + 2) → Simplex k)
    (i : Fin (n + 2)) :
    SingularChainFormulas.face (AffineSimplex.simplexRealizeMap v) i =
      AffineSimplex.simplexRealizeMap (face i v) :=
  AffineSimplex.simplexRealizeMap_comp_map i.succAbove v

theorem boundary_realize (k n : ℕ) (c : Chains (Simplex k) (n + 2)) :
    ((realSingularChainComplex (Simplex k)).d (n + 1) n).hom (realize k (n + 1) c) =
      realize k n (boundary (n + 1) c) := by
  have h : ((realSingularChainComplex (Simplex k)).d (n + 1) n).hom.comp
      (realize k (n + 1)) = (realize k n).comp (boundary (n + 1)) := by
    apply linearMap_ext
    intro v
    change ((realSingularChainComplex (Simplex k)).d (n + 1) n).hom
      (realize k (n + 1) (generator v)) = realize k n (boundary (n + 1) (generator v))
    rw [realize_generator, SingularChainFormulas.simplexChain_boundary_real,
      boundary_generator, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, realize_generator, face_simplexRealizeMap]
  exact LinearMap.congr_fun h c

theorem affineMap_realize (k l n : ℕ) (w : Fin (k + 1) → Simplex l)
    (c : Chains (Simplex k) (n + 1)) :
    ((realSingularChainMap (AffineSimplex.simplexRealizeMap w)
      (AffineSimplex.simplexRealizeMap w).continuous).f n).hom (realize k n c) =
      realize l n (mapVertices (AffineSimplex.simplexRealizeMap w) (n + 1) c) := by
  have h : ((realSingularChainMap (AffineSimplex.simplexRealizeMap w)
      (AffineSimplex.simplexRealizeMap w).continuous).f n).hom.comp (realize k n) =
      (realize l n).comp (mapVertices (AffineSimplex.simplexRealizeMap w) (n + 1)) := by
    apply linearMap_ext
    intro v
    change ((realSingularChainMap (AffineSimplex.simplexRealizeMap w)
      (AffineSimplex.simplexRealizeMap w).continuous).f n).hom
      (realize k n (generator v)) = _
    rw [realize_generator, SingularChainFormulas.simplexChain_map]
    have he : (AffineSimplex.simplexRealizeMap w).comp
        (AffineSimplex.simplexRealizeMap v) =
        AffineSimplex.simplexRealizeMap (AffineSimplex.simplexRealizeMap w ∘ v) := by
      ext p : 1
      exact AffineSimplex.simplexRealizeMap_assoc w v p
    simp only [LinearMap.comp_apply, mapVertices_generator, realize_generator]
    rw [he]
  exact LinearMap.congr_fun h c

theorem map_realize (k l n : ℕ) (f : Fin (k + 1) → Fin (l + 1))
    (c : Chains (Simplex k) (n + 1)) :
    ((realSingularChainMap (Convexity.StdSimplex.map f) (Convexity.StdSimplex.continuous_map ℝ f)).f n).hom
      (realize k n c) =
      realize l n (mapVertices (Convexity.StdSimplex.map f) (n + 1) c) := by
  let F : C(Simplex k, Simplex l) := ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩
  have h : ((realSingularChainMap F F.continuous).f n).hom.comp (realize k n) =
      (realize l n).comp (mapVertices (Convexity.StdSimplex.map f) (n + 1)) := by
    apply linearMap_ext
    intro v
    change ((realSingularChainMap F F.continuous).f n).hom
      (realize k n (generator v)) = _
    rw [realize_generator, SingularChainFormulas.simplexChain_map]
    have he : F.comp (AffineSimplex.simplexRealizeMap v) =
        AffineSimplex.simplexRealizeMap (Convexity.StdSimplex.map f ∘ v) := by
      ext p : 1
      exact AffineSimplex.map_simplexRealizeMap f v p
    simp only [LinearMap.comp_apply, mapVertices_generator, realize_generator]
    rw [he]
  exact LinearMap.congr_fun h c

@[simp] theorem simplexRealizeMap_standardVertices (n : ℕ) :
    AffineSimplex.simplexRealizeMap (standardVertices n) = ContinuousMap.id (Simplex n) := by
  ext p : 1
  apply RealSimplex.coordinates_injective
  funext j
  change AffineSimplex.simplexRealizeMap (standardVertices n) p j = p j
  rw [AffineSimplex.simplexRealizeMap_apply]
  simp [standardVertices, Finsupp.single_apply]

@[simp] theorem realize_standardVertices (n : ℕ) :
    realize n n (generator (standardVertices n)) =
      SingularChainFormulas.simplexChain (ContinuousMap.id (Simplex n)) := by
  rw [realize_generator, simplexRealizeMap_standardVertices]

end Problem340.SimplexSingularRealization

end

end OAI
