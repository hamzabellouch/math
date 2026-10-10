import Mathlib
import OAI.GroupTheory.FiniteType.HomotopyFunctor
import OAI.GroupTheory.FiniteType.SingularPrism

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
namespace SingularSphereCycle
open Set Topology CategoryTheory AlgebraicTopology
open scoped Simplicial
open SphereQuotient

def collapse (n : ℕ) : C(Convexity.StdSimplex ℝ (Fin (n+1)), Boundary (n+1)) :=
  (quotient n).comp ⟨SimplexDisk.diskEquiv n,(SimplexDisk.diskEquiv n).continuous⟩

lemma face_zero {n : ℕ} (i : Fin (n+2)) (s : Convexity.StdSimplex ℝ (Fin (n+1))) :
    (Convexity.StdSimplex.map i.succAbove s).weights i = 0 := by
  exact Finsupp.mapDomain_of_notMem_range s.weights i (by simp)

lemma collapse_face (n : ℕ) (i : Fin (n+2)) (s : Convexity.StdSimplex ℝ (Fin (n+1))) :
    collapse (n+1) (Convexity.StdSimplex.map i.succAbove s) = pole (n+1) :=
  quotient_boundary _ (SimplexDisk.diskEquiv_boundary _ i (face_zero i s))

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def simplex {n : ℕ} (f : C(Convexity.StdSimplex ℝ (Fin (n+1)),X)) :
    (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌ :=
  ⟨TopCat.ofHom (f.comp ⟨Homeomorph.ulift,Homeomorph.ulift.continuous⟩)⟩

lemma simplex_face {n : ℕ} (f : C(Convexity.StdSimplex ℝ (Fin (n+2)),X)) (i : Fin (n+2)) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (simplex f) =
      simplex (f.comp ⟨Convexity.StdSimplex.map i.succAbove,
        Convexity.StdSimplex.continuous_map ℝ _⟩) := by
  rfl

abbrev chains (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat ℤ) ℕ :=
  (TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℤ ℤ)

def cycle (n : ℕ) : ModuleCat.of ℤ ℤ ⟶ (chains (Boundary (n+1))).X n :=
  (TopCat.toSSet.obj (TopCat.of (Boundary (n+1)))).ιChainComplex (simplex (collapse n)) -
    (TopCat.toSSet.obj (TopCat.of (Boundary (n+1)))).ιChainComplex
      (simplex (ContinuousMap.const _ (pole n)))

lemma cycle_d_succ (n : ℕ) :
    cycle (n+1) ≫ (chains (Boundary (n+2))).d (n+1) n = 0 := by
  rw [cycle,Preadditive.sub_comp,SSet.ιChainComplex_d,SSet.ιChainComplex_d]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  rw [simplex_face,simplex_face]
  congr 1
  apply ContinuousMap.ext
  intro s
  exact collapse_face n i s

lemma cycle_d (n : ℕ) : cycle n ≫ (chains (Boundary (n+1))).d n (n-1) = 0 := by
  cases n with
  | zero => simp
  | succ n => simpa using cycle_d_succ n

def fundamentalClass (n : ℕ) : (chains (Boundary (n+1))).homology n :=
  ((chains (Boundary (n+1))).liftCycles (cycle n) (n-1) (by cases n <;> simp [ChainComplex.next_nat_zero,ChainComplex.next_nat_succ]) (cycle_d n) ≫
    (chains (Boundary (n+1))).homologyπ n) 1

end SingularSphereCycle

namespace HurewiczConstruction
open Set Topology CategoryTheory AlgebraicTopology
open SphereQuotient
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

def canonical (n : ℕ) : HomotopyGroup (Fin n) X x → integralHomology n X :=
  map n (SingularSphereCycle.fundamentalClass n)

@[simp] theorem canonical_mk (n : ℕ) (a : GenLoop (Fin n) X x) :
    canonical n ⟦a⟧ = pushforward n (sphereMap a) (SingularSphereCycle.fundamentalClass n) := rfl

theorem canonical_natural (n : ℕ) (f : C(X,Y)) (hf : f x = y)
    (a : HomotopyGroup (Fin n) X x) :
    canonical n (HomotopyFunctor.map f hf a) = pushforward n f (canonical n a) :=
  map_natural n _ f hf a

@[simp] theorem canonical_one (n : ℕ) [NeZero n] :
    canonical n (1 : HomotopyGroup (Fin n) X x) = 0 := by
  exact map_one n (NeZero.ne n) _

end HurewiczConstruction

namespace BasedSimplex
open Set Topology Metric
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ} {x : X}
abbrev Std (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n+1))
def Boundary (n : ℕ) : Set (Std n) := {s | ∃ i, s.weights i = 0}

def Space (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X) :=
  {f : C(Std n,X) // ∀ s ∈ Boundary n, f s = x}

instance : FunLike (Space n X x) (Std n) X where
  coe f := f.1
  coe_injective := fun _ _ h => Subtype.ext (ContinuousMap.ext (congrFun h))

@[ext] theorem ext {f g : Space n X x} (h : ∀ s, f s = g s) : f = g :=
  DFunLike.ext _ _ h

def cubeEquiv (n : ℕ) : (Fin n → I) ≃ₜ Std n :=
  (CubeDisk.homeomorph n).trans (SimplexDisk.diskEquiv n).symm

lemma cubeEquiv_boundary {n : ℕ} (v : Fin n → I) :
    cubeEquiv n v ∈ Boundary n ↔ v ∈ Cube.boundary (Fin n) := by
  change (∃ j, (cubeEquiv n v).weights j = 0) ↔ _
  rw [← SimplexDisk.diskEquiv_boundary_iff]
  change ‖(SimplexDisk.diskEquiv n ((SimplexDisk.diskEquiv n).symm (CubeDisk.toDisk n v))).1‖ = 1 ↔ _
  rw [Homeomorph.apply_symm_apply]
  exact ⟨fun h => by simpa only [CubeDisk.toCube_toDisk] using
    CubeDisk.boundary_of_norm_eq_one (CubeDisk.toDisk n v) h,
    CubeDisk.norm_eq_one_of_boundary v⟩

def loop (f : Space n X x) : GenLoop (Fin n) X x :=
  ⟨f.1.comp ⟨cubeEquiv n,(cubeEquiv n).continuous⟩,
    fun v hv => f.2 _ ((cubeEquiv_boundary v).mpr hv)⟩

def ofLoop (f : GenLoop (Fin n) X x) : Space n X x :=
  ⟨f.1.comp ⟨(cubeEquiv n).symm,(cubeEquiv n).symm.continuous⟩,
    fun s hs => f.2 _ ((cubeEquiv_boundary _).mp (by change cubeEquiv n ((cubeEquiv n).symm s) ∈ Boundary n; simpa only [Homeomorph.apply_symm_apply] using hs))⟩

@[simp] lemma loop_ofLoop (f : GenLoop (Fin n) X x) : loop (ofLoop f) = f := by
  ext v
  change f ((cubeEquiv n).symm (cubeEquiv n v)) = f v
  rw [Homeomorph.symm_apply_apply]

@[simp] lemma ofLoop_loop (f : Space n X x) : ofLoop (loop f) = f := by
  ext v
  change f (cubeEquiv n ((cubeEquiv n).symm v)) = f v
  rw [Homeomorph.apply_symm_apply]

def homotopyClass (f : Space n X x) : HomotopyGroup (Fin n) X x := ⟦loop f⟧

def const (n : ℕ) (x : X) : Space n X x := ⟨ContinuousMap.const _ x,fun _ _ => rfl⟩

@[simp] lemma loop_const (n : ℕ) (x : X) : loop (const n x) = GenLoop.const := rfl

lemma class_const (n : ℕ) [NeZero n] (x : X) : homotopyClass (const n x) = 1 := by
  rw [homotopyClass,loop_const,HomotopyGroup.one_def]

def map {Y : Type u} [TopologicalSpace Y] {y : Y} (g : C(X,Y)) (hg : g x = y)
    (f : Space n X x) : Space n Y y :=
  ⟨g.comp f.1,fun s hs => by change g (f.1 s) = y; rw [f.2 s hs,hg]⟩

lemma class_homotopic {f g : Space n X x} (H : f.1.HomotopyRel g.1 (Boundary n)) :
    homotopyClass f = homotopyClass g := by
  apply Quotient.sound
  refine ⟨?_⟩
  refine
  { toHomotopy :=
    { toFun := fun z => H (z.1,cubeEquiv n z.2)
      continuous_toFun := H.continuous.comp
        (continuous_fst.prodMk ((cubeEquiv n).continuous.comp continuous_snd))
      map_zero_left := fun z => H.apply_zero _
      map_one_left := fun z => H.apply_one _ },
    prop' := ?_ }
  intro t s hs
  exact H.eq_fst t ((cubeEquiv_boundary s).mpr hs)

def homotopy_of_loop {f g : Space n X x}
    (H : (loop f).1.HomotopyRel (loop g).1 (Cube.boundary (Fin n))) :
    f.1.HomotopyRel g.1 (Boundary n) := by
  refine
  { toHomotopy :=
    { toFun := fun z => H (z.1,(cubeEquiv n).symm z.2)
      continuous_toFun := H.continuous.comp
        (continuous_fst.prodMk ((cubeEquiv n).symm.continuous.comp continuous_snd))
      map_zero_left := ?_,
      map_one_left := ?_ },
    prop' := ?_ }
  · intro s
    rw [H.apply_zero]
    change f (cubeEquiv n ((cubeEquiv n).symm s)) = f s
    rw [Homeomorph.apply_symm_apply]
  · intro s
    rw [H.apply_one]
    change g (cubeEquiv n ((cubeEquiv n).symm s)) = g s
    rw [Homeomorph.apply_symm_apply]
  · intro t s hs
    change H (t,(cubeEquiv n).symm s) = f.1 s
    rw [H.eq_fst t ((cubeEquiv_boundary ((cubeEquiv n).symm s)).mp (by
      simpa only [Homeomorph.apply_symm_apply] using hs))]
    change f (cubeEquiv n ((cubeEquiv n).symm s)) = f s
    rw [Homeomorph.apply_symm_apply]

lemma class_eq_iff (f g : Space n X x) :
    homotopyClass f = homotopyClass g ↔ Nonempty (f.1.HomotopyRel g.1 (Boundary n)) := by
  constructor
  · intro h
    obtain ⟨H⟩ := Quotient.exact h
    exact ⟨homotopy_of_loop H⟩
  · rintro ⟨H⟩
    exact class_homotopic H

end BasedSimplex

namespace HurewiczNormalized
section
open Set Topology CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {n : ℕ} {x : X}

def cycle (f : BasedSimplex.Space n X x) : ModuleCat.of ℤ ℤ ⟶ (chains X).X n :=
  generator f.1 - generator (ContinuousMap.const _ x)

lemma based_face (f : BasedSimplex.Space (n+1) X x) (i : Fin (n+2)) :
    f.1.comp (face i) = ContinuousMap.const _ x := by
  ext s
  exact f.2 _ ⟨i,SimplexBoundary.face_zero i s⟩

lemma cycle_d (f : BasedSimplex.Space n X x) :
    cycle f ≫ (chains X).d n (n-1) = 0 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [cycle,Preadditive.sub_comp,Nat.add_sub_cancel,generator_boundary,generator_boundary]
    apply sub_eq_zero.mpr
    apply Finset.sum_congr rfl
    intro i _
    rw [based_face]
    rfl

def cycleClassHom {X : Type} [TopologicalSpace X] {n : ℕ}
    (c : ModuleCat.of ℤ ℤ ⟶ (chains X).X n) (hc : c ≫ (chains X).d n (n-1) = 0) :
    ModuleCat.of ℤ ℤ ⟶ (chains X).homology n :=
  (chains X).liftCycles c (n-1)
    (by cases n <;> simp [ChainComplex.next_nat_zero,ChainComplex.next_nat_succ]) hc ≫
      (chains X).homologyπ n

lemma cycleClassHom_map (c : ModuleCat.of ℤ ℤ ⟶ (chains X).X n)
    (hc : c ≫ (chains X).d n (n-1) = 0) (g : C(X,Y)) :
    cycleClassHom c hc ≫ homologyMap (map g) n =
      cycleClassHom (c ≫ (map g).f n)
        (by rw [Category.assoc,(map g).comm,← Category.assoc,hc,zero_comp]) := by
  unfold cycleClassHom
  rw [Category.assoc,homologyπ_naturality,← Category.assoc,liftCycles_comp_cyclesMap]

def homologyClass (f : BasedSimplex.Space n X x) : (chains X).homology n :=
  cycleClassHom (cycle f) (cycle_d f) 1

lemma sphereMap_comp_collapse (f : BasedSimplex.Space n X x) :
    (HurewiczConstruction.sphereMap (BasedSimplex.loop f)).comp
      (SingularSphereCycle.collapse n) = f.1 := by
  ext s
  change HurewiczConstruction.sphereMap (BasedSimplex.loop f)
    (SphereQuotient.sphereQuot n (.inl (SimplexDisk.diskEquiv n s))) = f.1 s
  rw [HurewiczConstruction.sphereMap_apply_quot]
  change f.1 ((SimplexDisk.diskEquiv n).symm
    (CubeDisk.toDisk n (CubeDisk.toCube n (SimplexDisk.diskEquiv n s)))) = f.1 s
  rw [CubeDisk.toDisk_toCube,Homeomorph.symm_apply_apply]

lemma sphereCycle_map (f : BasedSimplex.Space n X x) :
    SingularSphereCycle.cycle n ≫
      (map (HurewiczConstruction.sphereMap (BasedSimplex.loop f))).f n = cycle f := by
  change (generator (SingularSphereCycle.collapse n) -
    generator (ContinuousMap.const _ (SphereQuotient.pole n))) ≫ _ = _
  rw [Preadditive.sub_comp,generator_map,generator_map,sphereMap_comp_collapse]
  unfold cycle
  congr 2
  ext s
  exact HurewiczConstruction.sphereMap_pole _

theorem canonical_simplex (f : BasedSimplex.Space n X x) :
    HurewiczConstruction.canonical n (BasedSimplex.homotopyClass f) = homologyClass f := by
  change (cycleClassHom (SingularSphereCycle.cycle n) (SingularSphereCycle.cycle_d n) ≫
    homologyMap (map (HurewiczConstruction.sphereMap (BasedSimplex.loop f))) n) 1 = _
  rw [cycleClassHom_map]
  simp only [sphereCycle_map,homologyClass]

variable {k : ℕ}

def normalizedSimplex
    (hπ : ∀ p < k+1, ∀ z : X, Subsingleton (HomotopyGroup (Fin p) X z))
    (x₀ : X) (f : C(Std (k+1),X)) : BasedSimplex.Space (k+1) X x₀ :=
  ⟨(SingularNormalization.tightening hπ x₀).top (k+1) f,by
    rintro s ⟨i,hi⟩
    rw [← SimplexBoundary.face_drop i s hi]
    change ((SingularNormalization.tightening hπ x₀).top (k+1) f).comp (face i) _ = _
    rw [SingularNormalization.Coherent.top_face,
      SingularNormalization.tightening_top hπ x₀ k (by omega)]
    rfl⟩

end

open Set Topology CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains
variable {X : Type} [TopologicalSpace X] {k : ℕ}
variable (hπ : ∀ p < k+1, ∀ z : X, Subsingleton (HomotopyGroup (Fin p) X z)) (x₀ : X)

def differenceMap : chains X ⟶ chains X :=
  (SingularNormalization.tightening hπ x₀).topMap - map (ContinuousMap.const X x₀)

lemma difference_generator (f : C(Std (k+1),X)) :
    generator f ≫ (differenceMap hπ x₀).f (k+1) = cycle (normalizedSimplex hπ x₀ f) := by
  simp only [differenceMap,sub_f_apply,Preadditive.comp_sub]
  change generator f ≫ desc _ - _ = _
  rw [generator_desc,generator_map]
  rfl

lemma difference_cycle :
    (differenceMap hπ x₀).f (k+1) ≫ (chains X).d (k+1) k = 0 := by
  apply SingularChains.hom_ext
  intro f
  rw [← Category.assoc,difference_generator,comp_zero]
  have h := cycle_d (normalizedSimplex hπ x₀ f)
  rw [Nat.add_sub_cancel] at h
  exact h

def toCycles : (chains X).X (k+1) ⟶ (chains X).cycles (k+1) :=
  (chains X).liftCycles ((differenceMap hπ x₀).f (k+1)) k
    (by simp [ChainComplex.next_nat_succ]) (difference_cycle hπ x₀)

def toHomology : (chains X).X (k+1) ⟶ (chains X).homology (k+1) :=
  toCycles hπ x₀ ≫ (chains X).homologyπ (k+1)

lemma difference_homology : homologyMap (differenceMap hπ x₀) (k+1) = 𝟙 _ := by
  rw [differenceMap,homologyMap_sub]
  have he := (SingularNormalization.tightening hπ x₀).chainHomotopy.homologyMap_eq (k+1)
  rw [homologyMap_id] at he
  rw [← he,SingularNormalization.homologyMap_const (k+1) (by omega) x₀,sub_zero]

lemma cycles_toHomology :
    (chains X).iCycles (k+1) ≫ toHomology hπ x₀ = (chains X).homologyπ (k+1) := by
  have he : (chains X).iCycles (k+1) ≫ toCycles hπ x₀ =
      cyclesMap (differenceMap hπ x₀) (k+1) := by
    apply (cancel_mono ((chains X).iCycles (k+1))).1
    simp only [Category.assoc,toCycles,liftCycles_i,cyclesMap_i]
  rw [toHomology,← Category.assoc,he,← homologyπ_naturality,difference_homology,Category.comp_id]

instance toHomology_epi : Epi (toHomology hπ x₀) :=
  epi_of_epi_fac (cycles_toHomology hπ x₀)

lemma generator_toHomology (f : C(Std (k+1),X)) :
    generator f ≫ toHomology hπ x₀ =
      cycleClassHom (cycle (normalizedSimplex hπ x₀ f)) (cycle_d _) := by
  simp only [toHomology,← Category.assoc,toCycles,comp_liftCycles,difference_generator]
  rfl

include hπ in

theorem canonical_span :
    Submodule.span ℤ (Set.range (HurewiczConstruction.canonical (k+1) (X := X) (x := x₀))) = ⊤ := by
  let P := Submodule.span ℤ
    (Set.range (HurewiczConstruction.canonical (k+1) (X := X) (x := x₀)))
  let : Module ℤ ((chains X).homology (k+1) ⧸ P) := Submodule.Quotient.module P
  let q : (chains X).homology (k+1) ⟶ ModuleCat.of ℤ ((chains X).homology (k+1) ⧸ P) :=
    ModuleCat.ofHom P.mkQ
  have hq : toHomology hπ x₀ ≫ q = 0 := by
    apply SingularChains.hom_ext
    intro f
    rw [← Category.assoc,generator_toHomology,comp_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change P.mkQ (homologyClass (normalizedSimplex hπ x₀ f)) = 0
    change homologyClass (normalizedSimplex hπ x₀ f) ∈ LinearMap.ker P.mkQ
    rw [Submodule.ker_mkQ]
    rw [← canonical_simplex]
    exact Submodule.subset_span ⟨_,rfl⟩
  have hqzero : q = 0 := (cancel_epi (toHomology hπ x₀)).mp (by simpa using hq)
  apply top_unique
  intro z _
  have hz := congrArg (fun t => t z) hqzero
  change P.mkQ z = 0 at hz
  have hz' : z ∈ LinearMap.ker P.mkQ := hz
  simpa only [Submodule.ker_mkQ] using hz'

end HurewiczNormalized

end

end OAI
