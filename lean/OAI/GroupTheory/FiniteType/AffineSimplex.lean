import Mathlib
import OAI.GroupTheory.FiniteType.PresentationGeometryCellCoverExtension

namespace OAI

noncomputable section
open CategoryTheory AlgebraicTopology Limits Convexity
open scoped Simplicial
namespace AffineSimplex
open Set Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι κ : Type} [Fintype ι] [Fintype κ]

def linear (v : ι → E) : (ι → ℝ) →ₗ[ℝ] E where
  toFun c := ∑ i, c i • v i
  map_add' a b := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' r c := by simp [mul_smul,Finset.smul_sum]

def simplex (v : ι → E) : C(StdSimplex ℝ ι,E) :=
  ⟨fun s => linear v s.weights,(linear v).continuous_of_finiteDimensional.comp
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous⟩

@[simp] lemma simplex_apply (v : ι → E) (s : StdSimplex ℝ ι) :
    simplex v s = ∑ i, s.weights i • v i := rfl

lemma simplex_mem_convex (v : ι → E) {C : Set E} (hC : Convex ℝ C)
    (hv : ∀ i, v i ∈ C) (s : StdSimplex ℝ ι) : simplex v s ∈ C := by
  exact hC.sum_mem (fun i _ => s.weights_nonneg i) s.total_of_fintype (fun i _ => hv i)

lemma simplex_mem_hull (v : ι → E) (s : StdSimplex ℝ ι) :
    simplex v s ∈ convexHull ℝ (range v) :=
  simplex_mem_convex v (convex_convexHull ℝ _) (fun i => subset_convexHull ℝ _ (mem_range_self i)) s

lemma linear_map (v : κ → E) (f : ι → κ) (c : ι → ℝ) :
    linear v (FunOnFinite.linearMap ℝ ℝ f c) = linear (v ∘ f) c := by
  classical
  simp only [linear,LinearMap.coe_mk,AddHom.coe_mk,FunOnFinite.linearMap_apply_apply,
    Finset.sum_smul,Function.comp_apply]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := f)
    (by intro i _; exact Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

lemma simplex_map (v : κ → E) (f : ι → κ) (s : StdSimplex ℝ ι) :
    simplex v (StdSimplex.map f s) = simplex (v ∘ f) s := by
  change ∑ coord, (s.weights.mapDomain f) coord • v coord =
    ∑ coord, s.weights coord • v (f coord)
  rw [← Finsupp.sum_fintype (s.weights.mapDomain f)
    (fun coord coeff => coeff • v coord) (by simp),
    Finsupp.sum_mapDomain_index (by simp) (by simp [add_smul])]
  exact Finsupp.sum_fintype _ _ (by simp)

variable [DecidableEq ι]

@[simp] lemma simplex_vertex (v : ι → E) (i : ι) :
    simplex v (StdSimplex.single i) = v i := by
  simp [simplex_apply,Finsupp.single_apply]

lemma simplex_basis (s : StdSimplex ℝ ι) :
    simplex (fun i : ι => Pi.single i (1:ℝ)) s = s.weights := by
  funext j
  simp [simplex_apply,Finset.sum_apply,Pi.smul_apply,Pi.single_apply]

end AffineSimplex

namespace ConvexSimplex
open Set Topology
abbrev Std (n : ℕ) := StdSimplex ℝ (Fin (n+1))

def affine {m n : ℕ} (v : Fin (m+1) → Std n) : C(Std m,Std n) := by
  refine ⟨fun point => {
    weights := ∑ vertex, point.weights vertex • (v vertex).weights
    nonneg := Finset.sum_nonneg (fun vertex _ =>
      smul_nonneg (point.weights_nonneg vertex) (v vertex).nonneg)
    total := ?_ }, ?_⟩
  · rw [Finsupp.sum_fintype _ _ (by simp)]
    simp only [Finsupp.coe_finsetSum,Finset.sum_apply,Finsupp.smul_apply,smul_eq_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,StdSimplex.total_of_fintype,mul_one]
    exact point.total_of_fintype
  · apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff.mpr
    change Continuous (fun point : Std m =>
      ((∑ vertex, point.weights vertex • (v vertex).weights : Fin (n+1) →₀ ℝ) : Fin (n+1) → ℝ))
    simp only [Finsupp.coe_finsetSum,Finsupp.coe_smul]
    fun_prop

@[simp] lemma affine_coe {m n : ℕ} (v : Fin (m+1) → Std n) (s : Std m) :
    (affine v s).weights = ∑ i, s.weights i • (v i).weights := rfl

@[simp] lemma affine_vertex {m n : ℕ} (v : Fin (m+1) → Std n) (i : Fin (m+1)) :
    affine v (StdSimplex.single i) = v i := by
  apply StdSimplex.ext
  simp [affine_coe,Finsupp.single_apply]

@[simp] lemma affine_id (n : ℕ) :
    affine (fun i : Fin (n+1) => StdSimplex.single i) = ContinuousMap.id (Std n) := by
  ext s : 1
  apply StdSimplex.ext
  ext coord
  simp [affine_coe]

lemma affine_map {k m n : ℕ} (v : Fin (m+1) → Std n) (f : Fin (k+1) → Fin (m+1))
    (s : Std k) : affine v (StdSimplex.map f s) = affine (v ∘ f) s := by
  apply StdSimplex.ext
  apply DFunLike.coe_injective
  simpa only [affine_coe,Finsupp.coe_finsetSum,Finsupp.coe_smul,
    AffineSimplex.simplex_apply,Function.comp_apply] using
    AffineSimplex.simplex_map (fun vertex => ((v vertex).weights : Fin (n+1) → ℝ)) f s

lemma affine_comp {k m n : ℕ} (v : Fin (m+1) → Std n) (w : Fin (k+1) → Std m) :
    (affine v).comp (affine w) = affine (affine v ∘ w) := by
  ext s : 1
  apply StdSimplex.ext
  change (affine v (affine w s)).weights = (affine (affine v ∘ w) s).weights
  simp only [affine_coe]
  ext j
  simp only [affine_coe,Finsupp.coe_finsetSum,Finset.sum_apply,Finsupp.smul_apply,
    smul_eq_mul,Function.comp_apply,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  ring

def center {n : ℕ} {m : ℕ} (v : Fin (m+1) → Std n) : Std n :=
  affine v StdSimplex.barycenter

lemma affine_center {k m n : ℕ} (v : Fin (m+1) → Std n) (w : Fin (k+1) → Std m) :
    affine v (center w) = center (affine v ∘ w) :=
  congrArg (fun f : C(Std k,Std n) => f StdSimplex.barycenter) (affine_comp v w)

@[simp] lemma center_coe {m n : ℕ} (v : Fin (m+1) → Std n) :
    (center v).weights = ((m+1:ℝ)⁻¹) • ∑ i, (v i).weights := by
  simp [center,StdSimplex.weights_barycenter_apply,Finset.smul_sum]

lemma stdMap_affine {m n : ℕ} (f : Fin (m+1) → Fin (n+1)) (s : Std m) :
    StdSimplex.map f s = affine (StdSimplex.single ∘ f) s := by
  rw [← affine_map,affine_id]
  rfl

lemma stdMap_center {k m n : ℕ} (f : Fin (m+1) → Fin (n+1)) (w : Fin (k+1) → Std m) :
    StdSimplex.map f (center w) = center (StdSimplex.map f ∘ w) := by
  rw [stdMap_affine,affine_center]
  congr 1
  funext i
  exact (stdMap_affine f (w i)).symm

end ConvexSimplex
namespace SingularChains
open Set Topology CategoryTheory AlgebraicTopology Limits
open scoped Simplicial unitInterval

abbrev Std (n : ℕ) := StdSimplex ℝ (Fin (n+1))
abbrev singular (X : Type) [TopologicalSpace X] := TopCat.toSSet.obj (TopCat.of X)
abbrev chains (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat ℤ) ℕ :=
  (singular X).chainComplex (ModuleCat.of ℤ ℤ)

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def simplex {n : ℕ} (f : C(Std n,X)) : (singular X) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of X) _).symm f

def unsimplex {n : ℕ} (f : (singular X) _⦋n⦌) : C(Std n,X) :=
  TopCat.toSSetObjEquiv (TopCat.of X) _ f

@[simp] lemma simplex_unsimplex {n : ℕ} (f : (singular X) _⦋n⦌) : simplex (unsimplex f) = f :=
  Equiv.symm_apply_apply _ _
@[simp] lemma unsimplex_simplex {n : ℕ} (f : C(Std n,X)) : unsimplex (simplex f) = f :=
  Equiv.apply_symm_apply _ _

def face {n : ℕ} (i : Fin (n+2)) : C(Std n,Std (n+1)) :=
  ⟨StdSimplex.map i.succAbove,StdSimplex.continuous_map ℝ _⟩

lemma simplex_face {n : ℕ} (f : C(Std (n+1),X)) (i : Fin (n+2)) :
    (singular X).δ i (simplex f) = simplex (f.comp (face i)) := rfl

lemma simplex_map {n : ℕ} (f : C(Std n,X)) (g : C(X,Y)) :
    (TopCat.toSSet.map (TopCat.ofHom g)).app _ (simplex f) = simplex (g.comp f) := rfl

def generator {n : ℕ} (f : C(Std n,X)) : ModuleCat.of ℤ ℤ ⟶ (chains X).X n :=
  (singular X).ιChainComplex (simplex f)

@[reassoc] lemma generator_boundary {n : ℕ} (f : C(Std (n+1),X)) :
    generator f ≫ (chains X).d (n+1) n =
      ∑ i : Fin (n+2), (-1:ℤ)^i.val • generator (f.comp (face i)) := by
  simp only [generator,SSet.ιChainComplex_d,simplex_face]

def map (f : C(X,Y)) : chains X ⟶ chains Y :=
  SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ)

@[reassoc (attr := simp)] lemma generator_map {n : ℕ} (f : C(Std n,X)) (g : C(X,Y)) :
    generator f ≫ (map g).f n = generator (g.comp f) := by
  simp only [generator,map,SSet.ι_chainComplexMap_f,simplex_map]

def desc {n : ℕ} {A : ModuleCat ℤ} (b : C(Std n,X) → (ModuleCat.of ℤ ℤ ⟶ A)) :
    (chains X).X n ⟶ A := Sigma.desc (fun s => b (unsimplex s))

@[reassoc (attr := simp)] lemma generator_desc {n : ℕ} {A : ModuleCat ℤ}
    (b : C(Std n,X) → (ModuleCat.of ℤ ℤ ⟶ A)) (f : C(Std n,X)) :
    generator f ≫ desc b = b f := by
  simp only [generator,desc,SSet.ιChainComplex,Sigma.ι_comp_desc,unsimplex_simplex]

lemma hom_ext {n : ℕ} {A : ModuleCat ℤ} {f g : (chains X).X n ⟶ A}
    (h : ∀ s : C(Std n,X), generator s ≫ f = generator s ≫ g) : f = g := by
  apply SSet.chainComplex_hom_ext
  intro s
  simpa only [generator,simplex_unsimplex] using h (unsimplex s)

lemma map_comp (f : C(X,Y)) (g : C(Y,Z)) : map (g.comp f) = map f ≫ map g := by
  ext n : 1
  apply hom_ext
  intro s
  simp only [HomologicalComplex.comp_f,generator_map,generator_map_assoc,
    ContinuousMap.comp_assoc]

@[simp] lemma map_id : map (ContinuousMap.id X) = 𝟙 (chains X) := by
  ext n : 1
  apply hom_ext
  intro s
  simp only [HomologicalComplex.id_f,Category.comp_id,generator_map,ContinuousMap.id_comp]

end SingularChains

namespace AffineRealization
section
open CategoryTheory AlgebraicTopology Limits ConvexSimplex
open scoped Simplicial

def singular (n : ℕ) : AffineChains.vertices (Std n) ⟶ SingularChains.singular (Std n) where
  app _ := ↾fun v => SingularChains.simplex (affine v)
  naturality k m f := by
    ext v
    apply (TopCat.toSSetObjEquiv (TopCat.of (Std n)) m).injective
    change affine (v ∘ f.unop.toOrderHom) = (affine v).comp
      ⟨StdSimplex.map f.unop.toOrderHom,StdSimplex.continuous_map ℝ _⟩
    ext s : 1
    exact (affine_map _ _ _).symm

def realize (n : ℕ) : AffineChains.chains (Std n) ⟶ SingularChains.chains (Std n) :=
  SSet.chainComplexMap (singular n) (ModuleCat.of ℤ ℤ)

@[reassoc (attr := simp)] lemma generator_realize {m n : ℕ} (v : Fin (m+1) → Std n) :
    AffineChains.generator v ≫ (realize n).f m = SingularChains.generator (affine v) := by
  exact SSet.ι_chainComplexMap_f (AffineChains.vertices (Std n))
    (SingularChains.singular (Std n)) (singular n) (ModuleCat.of ℤ ℤ) v

@[reassoc] lemma realize_affine {m n k : ℕ} (v : Fin (m+1) → Std n) :
    (AffineChains.map (affine v)).f k ≫ (realize n).f k =
      (realize m).f k ≫ (SingularChains.map (affine v)).f k := by
  apply AffineChains.hom_ext
  intro w
  simp only [AffineChains.generator_map_assoc,generator_realize,
    generator_realize_assoc,SingularChains.generator_map,affine_comp]

def basis (n : ℕ) : Fin (n+1) → Std n := StdSimplex.single

lemma basis_map_face {n : ℕ} (i : Fin (n+2)) :
    SingularChains.face i ∘ basis n = basis (n+1) ∘ i.succAbove := by
  funext j
  exact StdSimplex.map_single _ _

@[simp] lemma basis_affine (n : ℕ) : affine (basis n) = ContinuousMap.id (Std n) :=
  affine_id n

lemma basis_map_affine {m n : ℕ} (v : Fin (m+1) → Std n) :
    affine v ∘ basis m = v := by
  funext j
  exact affine_vertex v j

end

open CategoryTheory AlgebraicTopology Limits ConvexSimplex
lemma face_affine {n : ℕ} (i : Fin (n+2)) :
    SingularChains.face i = affine (basis (n+1) ∘ i.succAbove) := by
  ext s : 1
  exact stdMap_affine _ s

@[reassoc] lemma realize_face {n k : ℕ} (i : Fin (n+2)) :
    (AffineChains.map (SingularChains.face i)).f k ≫ (realize (n+1)).f k =
      (realize n).f k ≫ (SingularChains.map (SingularChains.face i)).f k := by
  rw [face_affine]
  exact realize_affine _

end AffineRealization

end

end OAI
