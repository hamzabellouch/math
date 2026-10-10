import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Geometry.SingularHomology.AffineSimplexCone
import OAI.Geometry.SingularHomology.SingularChainsFinsupp
import OAI.Geometry.SingularHomology.SingularSubdivision

namespace OAI

noncomputable section

open CategoryTheory Simplicial Opposite

namespace Problem340.AffineSingularRealization

variable {E : Type} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

def realize (n : ℕ) : ((Fin (n + 1) → E) →₀ ℝ) →ₗ[ℝ]
    (realSingularChainComplex E).X n :=
  (singularChainsFinsuppEquiv E n).toLinearMap.comp
    (Finsupp.lmapDomain ℝ ℝ (fun v => AffineSimplex.realization v))

@[simp]
theorem realize_single {n : ℕ} (v : Fin (n + 1) → E) (r : ℝ) :
    realize n (Finsupp.single v r) = realSingularGenerator (AffineSimplex.realization v) r := by
  simp only [realize, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, singularChainsFinsuppEquiv_single]

theorem singular_face {n : ℕ} (v : Fin (n + 2) → E) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of E)).δ i
        ((TopCat.toSSetObjEquiv (TopCat.of E) (op ⦋n + 1⦌)).symm
          (AffineSimplex.realization v)) =
      (TopCat.toSSetObjEquiv (TopCat.of E) (op ⦋n⦌)).symm
        (AffineSimplex.realization (AffineSimplex.face i v)) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of E) (op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro p
  simp only [Equiv.apply_symm_apply, AffineSimplex.realizeMap_apply]
  exact AffineSimplex.realize_map v i.succAbove p

theorem boundary_realize_single {n : ℕ} (v : Fin (n + 2) → E) (r : ℝ) :
    ((realSingularChainComplex E).d (n + 1) n).hom
        (realize (n + 1) (Finsupp.single v r)) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        realize n (Finsupp.single (AffineSimplex.face i v) r) := by
  simp only [realize_single]
  let S := TopCat.toSSet.obj (TopCat.of E)
  let σ := (TopCat.toSSetObjEquiv (TopCat.of E) (op ⦋n + 1⦌)).symm
    (AffineSimplex.realization v)
  have h := congrArg
    (fun f : ModuleCat.of ℝ ℝ ⟶ (S.chainComplex (ModuleCat.of ℝ ℝ)).X n => f.hom r)
    (S.ιChainComplex_d (ModuleCat.of ℝ ℝ) σ)
  have hface (i : Fin (n + 2)) : S.δ i σ =
      (TopCat.toSSetObjEquiv (TopCat.of E) (op ⦋n⦌)).symm
        (AffineSimplex.realization (AffineSimplex.face i v)) := singular_face v i
  simp only [hface] at h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum,
    LinearMap.sum_apply, ModuleCat.hom_zsmul, LinearMap.smul_apply] at h
  exact h

theorem boundary_realize_single_real {n : ℕ} (v : Fin (n + 2) → E) (r : ℝ) :
    ((realSingularChainComplex E).d (n + 1) n).hom
        (realize (n + 1) (Finsupp.single v r)) =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val •
        realize n (Finsupp.single (AffineSimplex.face i v) r) := by
  simpa only [← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow, Int.cast_neg, Int.cast_one]
    using boundary_realize_single v r

section SimplexTarget

abbrev Simplex (k : ℕ) := Convexity.StdSimplex ℝ (Fin (k + 1))

def realizeInSimplex (k n : ℕ) : SingularSubdivision.Chains (Simplex k) (n + 1) →ₗ[ℝ]
    (realSingularChainComplex (Simplex k)).X n :=
  (singularChainsFinsuppEquiv (Simplex k) n).toLinearMap.comp
    (Finsupp.lmapDomain ℝ ℝ (fun v => AffineSimplex.simplexRealization v))

@[simp]
theorem realizeInSimplex_single {k n : ℕ} (v : Fin (n + 1) → Simplex k) (r : ℝ) :
    realizeInSimplex k n (Finsupp.single v r) =
      realSingularGenerator (AffineSimplex.simplexRealization v) r := by
  simp only [realizeInSimplex, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, singularChainsFinsuppEquiv_single]

@[simp]
theorem realizeInSimplex_generator {k n : ℕ} (v : Fin (n + 1) → Simplex k) :
    realizeInSimplex k n (SingularSubdivision.generator v) =
      realSingularGenerator (AffineSimplex.simplexRealization v) 1 :=
  realizeInSimplex_single v 1

theorem singular_simplex_face {k n : ℕ} (v : Fin (n + 2) → Simplex k)
    (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of (Simplex k))).δ i
        ((TopCat.toSSetObjEquiv (TopCat.of (Simplex k)) (op ⦋n + 1⦌)).symm
          (AffineSimplex.simplexRealization v)) =
      (TopCat.toSSetObjEquiv (TopCat.of (Simplex k)) (op ⦋n⦌)).symm
        (AffineSimplex.simplexRealization (SingularSubdivision.face i v)) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (Simplex k)) (op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro p
  simp only [Equiv.apply_symm_apply]
  exact AffineSimplex.simplexRealize_map v i.succAbove p

theorem boundary_realizeInSimplex_single {k n : ℕ} (v : Fin (n + 2) → Simplex k)
    (r : ℝ) :
    ((realSingularChainComplex (Simplex k)).d (n + 1) n).hom
        (realizeInSimplex k (n + 1) (Finsupp.single v r)) =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val •
        realizeInSimplex k n (Finsupp.single (SingularSubdivision.face i v) r) := by
  simp only [realizeInSimplex_single]
  let S := TopCat.toSSet.obj (TopCat.of (Simplex k))
  let σ := (TopCat.toSSetObjEquiv (TopCat.of (Simplex k)) (op ⦋n + 1⦌)).symm
    (AffineSimplex.simplexRealization v)
  have h := congrArg
    (fun f : ModuleCat.of ℝ ℝ ⟶ (S.chainComplex (ModuleCat.of ℝ ℝ)).X n => f.hom r)
    (S.ιChainComplex_d (ModuleCat.of ℝ ℝ) σ)
  have hface (i : Fin (n + 2)) : S.δ i σ =
      (TopCat.toSSetObjEquiv (TopCat.of (Simplex k)) (op ⦋n⦌)).symm
        (AffineSimplex.simplexRealization (SingularSubdivision.face i v)) :=
    singular_simplex_face v i
  simp only [hface, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum,
    LinearMap.sum_apply,
    ← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow, Int.cast_neg, Int.cast_one] at h
  exact h

theorem realizeInSimplex_boundary {k n : ℕ}
    (c : SingularSubdivision.Chains (Simplex k) (n + 2)) :
    realizeInSimplex k n (SingularSubdivision.boundary (n + 1) c) =
      ((realSingularChainComplex (Simplex k)).d (n + 1) n).hom
        (realizeInSimplex k (n + 1) c) := by
  have h : (realizeInSimplex k n).comp (SingularSubdivision.boundary (n + 1)) =
      ((realSingularChainComplex (Simplex k)).d (n + 1) n).hom.comp
        (realizeInSimplex k (n + 1)) := by
    apply SingularSubdivision.linearMap_ext
    intro v
    simp only [LinearMap.comp_apply, SingularSubdivision.boundary_generator, map_sum, map_smul]
    exact (boundary_realizeInSimplex_single v 1).symm
  exact LinearMap.congr_fun h c

end SimplexTarget

end Problem340.AffineSingularRealization

end

end OAI
