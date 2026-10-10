import Mathlib
import OAI.GroupTheory.FiniteType.SingularSupport

namespace OAI

noncomputable section
open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace SingularSubdivision
open CategoryTheory AlgebraicTopology Limits ConvexSimplex AffineRealization
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def iterate (X : Type) [TopologicalSpace X] (n k : ℕ) :
    (SingularChains.chains X).X n ⟶ (SingularChains.chains X).X n :=
  match k with
  | 0 => 𝟙 _
  | k+1 => iterate X n k ≫ subdiv n

lemma realize_subdiv (N n : ℕ) :
    AffineChains.subdiv (@center N) n ≫ (realize N).f n =
      (realize N).f n ≫ subdiv n := by
  apply AffineChains.hom_ext
  intro v
  rw [generator_realize_assoc,generator_affine_subdiv]

@[reassoc] lemma realize_iterate (N n k : ℕ) :
    SubdivisionMesh.iterate N n k ≫ (realize N).f n =
      (realize N).f n ≫ iterate (Std N) n k := by
  induction k with
  | zero => simp [SubdivisionMesh.iterate,iterate]
  | succ k ih =>
    rw [SubdivisionMesh.iterate,Category.assoc,realize_subdiv,← Category.assoc,ih]
    simp only [iterate,Category.assoc]

@[reassoc] lemma iterate_map (f : C(X,Y)) (n k : ℕ) :
    iterate X n k ≫ (SingularChains.map f).f n =
      (SingularChains.map f).f n ≫ iterate Y n k := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    rw [iterate,Category.assoc,subdiv_map,← Category.assoc,ih]
    simp only [iterate,Category.assoc]

lemma iterate_generator {n : ℕ} (f : C(Std n,X)) (k : ℕ) :
    SingularChains.generator f ≫ iterate X n k =
      AffineChains.generator (basis n) ≫ SubdivisionMesh.iterate n n k ≫
        (realize n).f n ≫ (SingularChains.map f).f n := by
  rw [realize_iterate_assoc,iterate_map]
  simp only [← Category.assoc,generator_realize,basis_affine,SingularChains.generator_map,
    ContinuousMap.comp_id]

end SingularSubdivision

namespace SmallChains
section
open Set Topology Filter CategoryTheory ConvexSimplex AffineRealization
variable {X : Type} [TopologicalSpace X] {ι : Type} (U : ι → Set X)

lemma affine_small {n m : ℕ} (f : C(Std n,X)) {δ : ℝ} {i : ι}
    (v : Fin (m+1) → Std n) (hv : SubdivisionMesh.MeshLe δ v)
    (hi : Metric.closedBall (v 0) δ ⊆ f ⁻¹' U i) : Small U (f.comp (affine v)) := by
  refine ⟨i,?_⟩
  rintro _ ⟨s,rfl⟩
  apply hi
  change dist (affine v s) (v 0) ≤ δ
  change dist ((affine v s).weights : Fin (n+1) → ℝ) (v 0).weights ≤ δ
  simp only [affine_coe,Finsupp.coe_finsetSum,Finsupp.coe_smul]
  apply AffineMesh.hull_dist _ (by simpa using hv 0 0) (fun i j => hv i j)
  · exact AffineSimplex.simplex_mem_hull _ _
  · exact subset_convexHull ℝ _ (mem_range_self 0)

lemma eventually_generator_small (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ)
    {n : ℕ} (f : C(Std n,X)) :
    ∀ᶠ k in atTop, SingularSubdivision.iterate X n k (SingularSupport.gen f) ∈ group U n := by
  obtain ⟨δ,hδ,hball⟩ := lebesgue_number_lemma_of_metric (s := (univ : Set (Std n)))
    isCompact_univ (fun i => (hU i).preimage f.continuous) (by
      simp only [← preimage_iUnion,hcover,preimage_univ,subset_refl])
  have ht : Tendsto (fun k : ℕ => AffineMesh.ratio n ^ k * 2) atTop (𝓝 (0:ℝ)) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (AffineMesh.ratio_nonneg n) (AffineMesh.ratio_lt_one n)).mul_const (2:ℝ)
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with k hk
  change (SingularChains.generator f ≫ SingularSubdivision.iterate X n k) 1 ∈ group U n
  rw [SingularSubdivision.iterate_generator]
  let g := (realize n).f n ≫ (SingularChains.map f).f n
  change g (SubdivisionMesh.iterate n n k (AffineSupport.gen (basis n))) ∈ group U n
  apply AffineSupport.map_mem (P := SubdivisionMesh.MeshLe (AffineMesh.ratio n ^ k * 2)) g
  · intro v hv
    change (AffineChains.generator v ≫ (realize n).f n ≫ (SingularChains.map f).f n) 1 ∈ group U n
    rw [generator_realize_assoc,SingularChains.generator_map]
    obtain ⟨i,hi⟩ := hball (v 0) (mem_univ _)
    apply gen_mem U _
    apply affine_small U f v hv
    intro s hs
    exact hi (lt_of_le_of_lt hs hk)
  · apply SubdivisionMesh.iterate_mesh (by norm_num)
    exact AffineSupport.gen_mem _ (SubdivisionMesh.basis_mesh n)

def eventuallySmall (n : ℕ) : Submodule ℤ ((SingularChains.chains X).X n) where
  carrier := {c | ∀ᶠ k in atTop, SingularSubdivision.iterate X n k c ∈ group U n}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    filter_upwards [hx,hy] with k hx hy
    simpa using (group U n).add_mem hx hy
  smul_mem' := by
    intro a c hc
    filter_upwards [hc] with k hc
    simpa using (group U n).smul_mem a hc

theorem eventually_small (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ)
    {n : ℕ} (c : (SingularChains.chains X).X n) :
    ∀ᶠ k in atTop, SingularSubdivision.iterate X n k c ∈ group U n := by
  apply SingularSupport.induction_on (eventuallySmall U n) _ c
  intro f
  exact eventually_generator_small U hU hcover f

lemma iterate_mem {n : ℕ} {c : (SingularChains.chains X).X n} (hc : c ∈ group U n) (k : ℕ) :
    SingularSubdivision.iterate X n k c ∈ group U n := by
  induction k with
  | zero => simpa [SingularSubdivision.iterate] using hc
  | succ k ih => exact subdiv_mem U ih

end

open CategoryTheory SingularChains
variable {X : Type} [TopologicalSpace X] {ι : Type} (U : ι → Set X)

def obj (n : ℕ) : ModuleCat ℤ := by
  letI := Submodule.module (group U n)
  exact ModuleCat.of ℤ (group U n)

def boundary (n : ℕ) : obj U (n+1) ⟶ obj U n := by
  letI := Submodule.module (group U n)
  letI := Submodule.module (group U (n+1))
  exact ModuleCat.ofHom (((chains X).d (n+1) n).hom.domRestrict (group U (n+1)) |>.codRestrict
    (group U n) (fun c => boundary_mem U c.2))

lemma boundary_val (n : ℕ) (c : obj U (n+1)) :
    (boundary U n c).1 = (chains X).d (n+1) n c.1 := rfl

lemma boundary_sq (n : ℕ) : boundary U (n+1) ≫ boundary U n = 0 := by
  apply ModuleCat.hom_ext
  ext c : 1
  apply Subtype.ext
  change (chains X).d (n+1) n ((chains X).d (n+2) (n+1) c.1) = 0
  exact congrArg (fun h : (chains X).X (n+2) ⟶ (chains X).X n => h c.1)
    ((chains X).d_comp_d (n+2) (n+1) n)

def complex : ChainComplex (ModuleCat ℤ) ℕ := ChainComplex.of (obj U) (boundary U) (boundary_sq U)

def inclusion : complex U ⟶ chains X := ChainComplex.ofHom
  (fun n => by
    letI := Submodule.module (group U n)
    exact ModuleCat.ofHom (group U n).subtype) (fun n => by
    apply ModuleCat.hom_ext
    ext c : 1
    simp only [complex,ChainComplex.of_d]
    rfl)

@[simp] lemma inclusion_apply (n : ℕ) (c : (complex U).X n) : (inclusion U).f n c = c.1 := rfl

end SmallChains

namespace SingularSubdivision
open CategoryTheory SingularChains
variable {X : Type} [TopologicalSpace X]

lemma iterate_comm (n m k : ℕ) :
    iterate X n k ≫ (chains X).d n m = (chains X).d n m ≫ iterate X m k := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    change (iterate X n k ≫ subdivision.f n) ≫ _ = _ ≫ (iterate X m k ≫ subdivision.f m)
    rw [Category.assoc,subdivision.comm,← Category.assoc,ih,Category.assoc]

def sumPrism (X : Type) [TopologicalSpace X] (n k : ℕ) :
    (chains X).X n ⟶ (chains X).X (n+1) :=
  match k with
  | 0 => 0
  | k+1 => sumPrism X n k + iterate X n k ≫ prism n

lemma sumPrism_zero (k : ℕ) : sumPrism X 0 k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [sumPrism,ih]

lemma iterate_zero (k : ℕ) : iterate X 0 k = 𝟙 _ := by
  induction k with
  | zero => rfl
  | succ k ih => simp [iterate,ih]

lemma sumPrism_boundary (n k : ℕ) :
    sumPrism X (n+1) k ≫ (chains X).d (n+2) (n+1) = 𝟙 _ - iterate X (n+1) k -
      (chains X).d (n+1) n ≫ sumPrism X n k := by
  induction k with
  | zero => simp [sumPrism,iterate]
  | succ k ih =>
    rw [sumPrism,Preadditive.add_comp,Category.assoc,prism_boundary,ih]
    simp only [Preadditive.comp_sub,Preadditive.comp_add,Category.comp_id,iterate,
      sumPrism,← Category.assoc]
    rw [iterate_comm]
    abel

end SingularSubdivision

namespace SmallChains
open CategoryTheory SingularChains
variable {X : Type} [TopologicalSpace X] {ι : Type} (U : ι → Set X)

lemma sumPrism_mem {n : ℕ} {c : (chains X).X n} (hc : c ∈ group U n) (k : ℕ) :
    SingularSubdivision.sumPrism X n k c ∈ group U (n+1) := by
  induction k with
  | zero => exact (group U (n+1)).zero_mem
  | succ k ih =>
    apply (group U (n+1)).add_mem ih
    exact prism_mem U (iterate_mem U hc k)

end SmallChains
namespace ModuleHomology
open CategoryTheory Limits
variable {R : Type} [Ring R] (S : ShortComplex (ModuleCat R))

abbrev Cycles := LinearMap.ker S.g.hom

def classMap : S.moduleCatLeftHomologyData.K ⟶ S.homology :=
  S.moduleCatCyclesIso.inv ≫ S.homologyπ

lemma classMap_surjective : Function.Surjective (classMap S) := by
  apply (ModuleCat.epi_iff_surjective _).mp
  dsimp [classMap]
  infer_instance

lemma classMap_zero_iff (c : Cycles S) : classMap S c = 0 ↔ ∃ b : S.X₁, S.f b = c.1 := by
  have hi := (ModuleCat.mono_iff_injective S.moduleCatHomologyIso.hom).mp inferInstance
  rw [← hi.eq_iff]
  change (classMap S ≫ S.moduleCatHomologyIso.hom) c = S.moduleCatHomologyIso.hom 0 ↔ _
  rw [classMap,Category.assoc,ShortComplex.π_moduleCatCyclesIso_hom,
    ← Category.assoc,Iso.inv_hom_id,Category.id_comp,map_zero]
  change (LinearMap.range S.moduleCatToCycles).mkQ c = 0 ↔ _
  change c ∈ LinearMap.ker (LinearMap.range S.moduleCatToCycles).mkQ ↔ _
  rw [Submodule.ker_mkQ]
  constructor
  · rintro ⟨b,hb⟩; exact ⟨b,congrArg Subtype.val hb⟩
  · rintro ⟨b,hb⟩; exact ⟨b,Subtype.ext hb⟩

lemma classMap_eq_iff (c d : Cycles S) : classMap S c = classMap S d ↔
    ∃ b : S.X₁, S.f b = c.1 - d.1 := by
  erw [← sub_eq_zero,← map_sub,classMap_zero_iff]
  rfl

variable {S} {T : ShortComplex (ModuleCat R)}

def cyclesMap (φ : S ⟶ T) : S.moduleCatLeftHomologyData.K ⟶ T.moduleCatLeftHomologyData.K :=
  ModuleCat.ofHom ((φ.τ₂.hom.domRestrict (LinearMap.ker S.g.hom)).codRestrict (LinearMap.ker T.g.hom) (by
    intro x
    change T.g (φ.τ₂ x.1) = 0
    have h := congrArg (fun h : S.X₂ ⟶ T.X₃ => h x.1) φ.comm₂₃
    change T.g (φ.τ₂ x.1) = φ.τ₃ (S.g x.1) at h
    have hx : S.g x.1 = 0 := x.2
    simpa only [hx,map_zero] using h))

lemma cyclesMap_i (φ : S ⟶ T) :
    cyclesMap φ ≫ T.moduleCatLeftHomologyData.i = S.moduleCatLeftHomologyData.i ≫ φ.τ₂ := rfl

lemma cyclesMap_eq (φ : S ⟶ T) :
    cyclesMap φ = S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ ≫ T.moduleCatCyclesIso.hom := by
  rw [← cancel_mono T.moduleCatLeftHomologyData.i]
  simp only [Category.assoc,ShortComplex.moduleCatCyclesIso_hom_i,
    ShortComplex.cyclesMap_i,ShortComplex.moduleCatCyclesIso_inv_iCycles_assoc,cyclesMap_i]

lemma classMap_natural (φ : S ⟶ T) :
    classMap S ≫ ShortComplex.homologyMap φ = cyclesMap φ ≫ classMap T := by
  simp only [classMap,cyclesMap_eq,Category.assoc,
    ShortComplex.homologyπ_naturality,← Category.assoc T.moduleCatCyclesIso.hom,
    Iso.hom_inv_id,Category.id_comp]

lemma homologyMap_class (φ : S ⟶ T) (c : Cycles S) :
    ShortComplex.homologyMap φ (classMap S c) = classMap T (cyclesMap φ c) :=
  congrArg (fun h : S.moduleCatLeftHomologyData.K ⟶ T.homology => h c) (classMap_natural φ)

lemma homologyMap_surjective (φ : S ⟶ T)
    (hs : ∀ c : Cycles T, ∃ d : Cycles S, ∃ b : T.X₁, T.f b = c.1 - φ.τ₂ d.1) :
    Function.Surjective (ShortComplex.homologyMap φ) := by
  intro a
  obtain ⟨c,rfl⟩ := classMap_surjective T a
  obtain ⟨d,b,hb⟩ := hs c
  refine ⟨classMap S d,?_⟩
  rw [homologyMap_class]
  symm
  exact (classMap_eq_iff T _ _).mpr ⟨b,hb⟩

lemma homologyMap_injective (φ : S ⟶ T)
    (hi : ∀ c : Cycles S, (∃ b : T.X₁, T.f b = φ.τ₂ c.1) → ∃ b : S.X₁, S.f b = c.1) :
    Function.Injective (ShortComplex.homologyMap φ) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨c,rfl⟩ := classMap_surjective S x
  erw [homologyMap_class,classMap_zero_iff] at hx
  exact (classMap_zero_iff S c).mpr (hi c hx)

end ModuleHomology

end

end OAI
