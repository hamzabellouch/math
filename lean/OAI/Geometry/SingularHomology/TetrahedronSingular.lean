import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Dynamics.EntropyCounterexample.Definitions
import OAI.Geometry.SingularHomology.SimplicialSphereHomology

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SimplicialSphere

abbrev TopologicalBoundary :=
  {p : Convexity.StdSimplex ℝ (Fin 4) // ∃ j : Fin 4, p j = 0}

def tetraVector (p : TopologicalBoundary) : SphereAmbient :=
  WithLp.toLp 2 ![p.val 0 - p.val 3, p.val 1 - p.val 3, p.val 2 - p.val 3]

lemma tetraVector_ne_zero (p : TopologicalBoundary) : tetraVector p ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : SphereAmbient => v 0) h
  have h1 := congrArg (fun v : SphereAmbient => v 1) h
  have h2 := congrArg (fun v : SphereAmbient => v 2) h
  change p.val 0 - p.val 3 = 0 at h0
  change p.val 1 - p.val 3 = 0 at h1
  change p.val 2 - p.val 3 = 0 at h2
  have hs := p.val.total_of_fintype
  rw [Fin.sum_univ_four] at hs
  rcases p.property with ⟨j, hj⟩
  fin_cases j
  · change p.val 0 = 0 at hj
    linarith
  · change p.val 1 = 0 at hj
    linarith
  · change p.val 2 = 0 at hj
    linarith
  · change p.val 3 = 0 at hj
    linarith

lemma continuous_tetraVector : Continuous tetraVector := by
  unfold tetraVector
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  have hp (j : Fin 4) : Continuous (fun p : TopologicalBoundary => p.val j) :=
    (Convexity.StdSimplex.continuous_weights_apply ℝ j).comp continuous_subtype_val
  fin_cases i
  · exact (hp 0).sub (hp 3)
  · exact (hp 1).sub (hp 3)
  · exact (hp 2).sub (hp 3)

def radial (p : TopologicalBoundary) : StandardSphere2 :=
  ⟨‖tetraVector p‖⁻¹ • tetraVector p, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (tetraVector_ne_zero p))]⟩

lemma continuous_radial : Continuous radial := by
  apply Continuous.subtype_mk
  exact (continuous_tetraVector.norm.inv₀ (fun p =>
    norm_ne_zero_iff.mpr (tetraVector_ne_zero p))).smul continuous_tetraVector

def radialMap : C(TopologicalBoundary, StandardSphere2) := ⟨radial, continuous_radial⟩

lemma map_mem_boundary {n : ℕ} (x : sphere _⦋n⦌)
    (p : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    ∃ j : Fin 4, Convexity.StdSimplex.map x.val p j = 0 := by
  classical
  have hx := x.property
  change ¬ Function.Surjective x.val at hx
  simp only [Function.Surjective, not_forall, not_exists] at hx
  rcases hx with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  change (Finsupp.mapDomain x.val p.weights) j = 0
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨index, hindex⟩
  exact hj index hindex

def simplexBoundaryMap {n : ℕ} (x : sphere _⦋n⦌) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), TopologicalBoundary) :=
  ⟨fun p => ⟨Convexity.StdSimplex.map x.val p, map_mem_boundary x p⟩,
    (Convexity.StdSimplex.continuous_map ℝ x.val).subtype_mk _⟩

lemma simplexBoundaryMap_naturality {n m : SimplexCategory} (f : n ⟶ m)
    (x : sphere.obj (op m)) (p : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    simplexBoundaryMap (sphere.map f.op x) p =
      simplexBoundaryMap x (Convexity.StdSimplex.map f p) := by
  rcases n with ⟨n⟩
  rcases m with ⟨m⟩
  apply Subtype.ext
  dsimp only [simplexBoundaryMap, ContinuousMap.coe_mk]
  exact Convexity.StdSimplex.map_comp p f x.val

lemma radialMap_naturality {n m : SimplexCategory} (f : n ⟶ m)
    (x : sphere.obj (op m)) :
    radialMap.comp (simplexBoundaryMap (sphere.map f.op x)) =
      (radialMap.comp (simplexBoundaryMap x)).comp
        ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩ := by
  apply ContinuousMap.ext
  intro p
  exact congrArg radial (simplexBoundaryMap_naturality f x p)

def singularSimplex (n : SimplexCategoryᵒᵖ) (x : sphere.obj n) :
    (TopCat.toSSet.obj (TopCat.of StandardSphere2)).obj n :=
  (TopCat.toSSetObjEquiv (TopCat.of StandardSphere2) n).symm
    (radialMap.comp (simplexBoundaryMap x))

lemma singularSimplex_naturality {n m : SimplexCategory} (f : n ⟶ m)
    (x : sphere.obj (op m)) :
    singularSimplex (op n) (sphere.map f.op x) =
      (TopCat.toSSet.obj (TopCat.of StandardSphere2)).map f.op
        (singularSimplex (op m) x) := by
  unfold singularSimplex
  rw [radialMap_naturality f x]
  exact (TopCat.toSSetObjEquiv_symm_naturality (X := TopCat.of StandardSphere2) f
    (radialMap.comp (simplexBoundaryMap x))).symm

def toSingular : sphere ⟶ TopCat.toSSet.obj (TopCat.of StandardSphere2) where
  app n := TypeCat.ofHom (singularSimplex n)
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact singularSimplex_naturality f.unop x

abbrev singularChains :=
  (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℝ)).obj coefficients).obj
    (TopCat.of StandardSphere2))

def singularChainMap : chains ⟶ singularChains :=
  sphere.fromNormalizedChainComplex coefficients ≫ SSet.chainComplexMap toSingular coefficients

def singularFundamentalCycle : coefficients ⟶ singularChains.X 2 :=
  fundamentalCycle ≫ singularChainMap.f 2

lemma singularFundamentalCycle_boundary :
    singularFundamentalCycle ≫ singularChains.d 2 1 = 0 := by
  rw [singularFundamentalCycle, Category.assoc, singularChainMap.comm,
    ← Category.assoc, fundamentalCycle_boundary, zero_comp]

def singularFundamentalClassMap : coefficients ⟶ singularChains.homology 2 :=
  singularChains.liftCycles singularFundamentalCycle 1 (by simp)
    singularFundamentalCycle_boundary ≫ singularChains.homologyπ 2

def singularFundamentalClass : RealSingularHomology 2 StandardSphere2 :=
  singularFundamentalClassMap (1 : ℝ)

theorem singularFundamentalClass_eq_zero_iff :
    singularFundamentalClass = 0 ↔
      ∃ b : singularChains.X 3,
        singularChains.d 3 2 b = singularFundamentalCycle (1 : ℝ) := by
  have hcomp : singularFundamentalClassMap ≫ singularChains.homologyι 2 =
      singularFundamentalCycle ≫ singularChains.pOpcycles 2 := by
    rw [singularFundamentalClassMap, Category.assoc,
      HomologicalComplex.homology_π_ι, ← Category.assoc,
      HomologicalComplex.liftCycles_i]
  have hx := ConcreteCategory.congr_hom hcomp (1 : ℝ)
  have hinj := (ModuleCat.mono_iff_injective (singularChains.homologyι 2)).1 inferInstance
  calc
    singularFundamentalClass = 0 ↔
        singularChains.homologyι 2 singularFundamentalClass = 0 := by
      constructor
      · intro h
        rw [h]
        exact (singularChains.homologyι 2).hom.map_zero
      · intro h
        apply hinj
        exact h.trans (singularChains.homologyι 2).hom.map_zero.symm
    _ ↔ singularChains.pOpcycles 2 (singularFundamentalCycle (1 : ℝ)) = 0 := by
      change singularChains.homologyι 2 (singularFundamentalClassMap (1 : ℝ)) = 0 ↔ _
      rw [show singularChains.homologyι 2 (singularFundamentalClassMap (1 : ℝ)) =
        singularChains.pOpcycles 2 (singularFundamentalCycle (1 : ℝ)) from hx]
    _ ↔ _ := by
      have h := (singularChains.sc 2).moduleCat_pOpcycles_eq_zero_iff
        (singularFundamentalCycle (1 : ℝ))
      change singularChains.pOpcycles 2 (singularFundamentalCycle (1 : ℝ)) = 0 ↔
        ∃ b : singularChains.X ((ComplexShape.down ℕ).prev 2),
          singularChains.d ((ComplexShape.down ℕ).prev 2) 2 b =
            singularFundamentalCycle (1 : ℝ) at h
      have hp : (ComplexShape.down ℕ).prev 2 = 3 := by simp
      rw [hp] at h
      exact h

end Problem340.SimplicialSphere

end

end OAI
