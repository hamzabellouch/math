import Mathlib
import OAI.GroupTheory.FiniteType.ChainShortExact

namespace OAI

noncomputable section
open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace RelativeChains
open Set CategoryTheory HomologicalComplex SingularChains
variable {X : Type} [TopologicalSpace X]

lemma empty_projection_quasiIso : QuasiIso (projection (∅ : Set X)) :=
  ChainShortExact.quasiIso_g (shortExact ∅) (fun n => SingularChains.isEmpty_homology_isZero n)

def twoPointHomologyIso [DiscreteTopology X] (x y : X) (hxy : x ≠ y)
    (h : ∀ z, z = x ∨ z = y) (n : ℕ) :
    (complex ({x} : Set X)).homology n ≅ (chains ({y} : Set X)).homology n := by
  have hcover : interior ({x} : Set X) ∪ interior ({y} : Set X) = univ := by
    rw [(isOpen_discrete _).interior_eq,(isOpen_discrete _).interior_eq]
    exact eq_univ_of_forall h
  letI := SingularExcision.inclusion_quasiIso {x} {y} hcover
  have he : (SingularSubspace.inclusionMap ({y} : Set X)) ⁻¹' ({x} : Set X) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hxy ((mem_singleton_iff.mp hz).symm.trans (mem_singleton_iff.mp z.2))
  refine (asIso (homologyMap (inclusion {x} {y}) n)).symm ≪≫ ?_
  rw [he]
  letI := empty_projection_quasiIso (X := ({y} : Set X))
  exact (asIso (homologyMap (projection (∅ : Set ({y} : Set X))) n)).symm

end RelativeChains

namespace SphereCover
section
open Set Metric CategoryTheory
variable {E : Type} [NormedAddCommGroup E]

lemma val_ne_zero (v : Sphere E) : (v : E) ≠ 0 := by
  intro h
  have hv := norm_eq_of_mem_sphere v
  simp [h] at hv

variable [InnerProductSpace ℝ E]

lemma eq_or_neg_of_finrank_one [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = 1)
    (v w : Sphere E) : w = v ∨ w = -v := by
  have ht : (ℝ ∙ (v : E)) = ⊤ := Submodule.eq_top_of_finrank_eq ((finrank_span_singleton (val_ne_zero v)).trans hd.symm)
  have hw : (w : E) ∈ ℝ ∙ (v : E) := by rw [ht]; trivial
  obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hw
  have hn : |t| = 1 := by
    have h := congrArg norm ht
    simpa only [norm_smul,Real.norm_eq_abs,norm_eq_of_mem_sphere v,norm_eq_of_mem_sphere w,mul_one] using h
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hn with rfl | rfl
  · left; apply Subtype.ext; simpa using ht.symm
  · right; apply Subtype.ext; simpa using ht.symm

lemma finite_of_finrank_one [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = 1) (v : Sphere E) :
    Finite (Sphere E) := by
  apply Finite.of_surjective (fun b : Bool => if b then v else -v)
  intro w
  rcases eq_or_neg_of_finrank_one hd v w with rfl | rfl
  · exact ⟨true,rfl⟩
  · exact ⟨false,rfl⟩

def baseHomologyIso [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = 1) (v : Sphere E) :
    (RelativeChains.complex ({v} : Set (Sphere E))).homology 0 ≅ ModuleCat.of ℤ ℤ := by
  letI := finite_of_finrank_one hd v
  exact RelativeChains.twoPointHomologyIso v (-v) (ne_neg v) (eq_or_neg_of_finrank_one hd v) 0 ≪≫
    SingularChains.unique_homologyZeroIso

lemma baseHomology_isZero [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = 1) (v : Sphere E)
    (n : ℕ) (hn : n ≠ 0) : CategoryTheory.Limits.IsZero ((RelativeChains.complex ({v} : Set (Sphere E))).homology n) := by
  let := finite_of_finrank_one hd v
  exact (SingularChains.contractible_homology_isZero (X := ({-v} : Set (Sphere E))) n hn).of_iso
    (RelativeChains.twoPointHomologyIso v (-v) (ne_neg v) (eq_or_neg_of_finrank_one hd v) n)

end

section
open Set Metric CategoryTheory HomologicalComplex

theorem homology (n : ℕ) : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E], Module.finrank ℝ E = n+1 → ∀ (v : Sphere E),
    Nonempty ((RelativeChains.complex ({v} : Set (Sphere E))).homology n ≅ ModuleCat.of ℤ ℤ) ∧
      ∀ k, k ≠ n → Limits.IsZero ((RelativeChains.complex ({v} : Set (Sphere E))).homology k) := by
  induction n with
  | zero =>
    intro E _ _ _ hd v
    exact ⟨⟨baseHomologyIso hd v⟩,baseHomology_isZero hd v⟩
  | succ n ih =>
    intro E _ _ _ hd v
    let : Fact (Module.finrank ℝ E = (n+1)+1) := ⟨hd⟩
    have horth : Module.finrank ℝ (Orth (-v)) = n+1 :=
      Submodule.finrank_orthogonal_span_singleton (val_ne_zero (-v))
    let : Nontrivial (Orth (-v)) := Module.nontrivial_of_finrank_eq_succ horth
    obtain ⟨w,hw⟩ := exists_norm_eq (Orth (-v)) (by norm_num : (0 : ℝ) ≤ 1)
    let p : Sphere (Orth (-v)) := ⟨w,by simpa only [mem_sphere,dist_zero_right] using hw⟩
    let e := overlapHomotopyEquiv v
    let x : Overlap v := e.symm p
    let := cap_contractible v
    let := cap_contractible (-v)
    let d (k : ℕ) :
        (RelativeChains.complex ({v} : Set (Sphere E))).homology (k+1) ≅
        (RelativeChains.complex ({e x} : Set (Sphere (Orth (-v))))).homology k :=
      RelativeChains.pointHomologyIso v x.1.1 (k+1) ≪≫
        RelativeChains.suspensionIso (Cap v) (Cap (-v)) (cap_cover v) x k ≪≫
        RelativeChains.pointHomotopyEquivIso e x k
    obtain ⟨hn,hother⟩ := ih (Orth (-v)) horth (e x)
    refine ⟨⟨d n ≪≫ hn.some⟩,?_⟩
    intro k hk
    cases k with
    | zero =>
      exact (RelativeChains.suspension_zero (Cap v) (Cap (-v)) (cap_cover v) x).of_iso
        (RelativeChains.pointHomologyIso v x.1.1 0)
    | succ k =>
      exact (hother k (by omega)).of_iso (d k)

end

open Set Metric CategoryTheory
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma normed_homology [FiniteDimensional ℝ E] (n : ℕ) (hd : Module.finrank ℝ E = n+1)
    (v : Sphere E) :
    Nonempty ((RelativeChains.complex ({v} : Set (Sphere E))).homology n ≅ ModuleCat.of ℤ ℤ) ∧
      ∀ k, k ≠ n → Limits.IsZero ((RelativeChains.complex ({v} : Set (Sphere E))).homology k) := by
  let F := EuclideanSpace ℝ (Fin (n+1))
  let : ContinuousSMul ℝ F := IsBoundedSMul.continuousSMul
  have hdF : Module.finrank ℝ F = n+1 := finrank_euclideanSpace_fin
  let e : E ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq (hd.trans hdF.symm)
  let s := sphereHomotopyEquiv e
  obtain ⟨hn,hother⟩ := homology n F hdF (s v)
  exact ⟨⟨RelativeChains.pointHomotopyEquivIso s v n ≪≫ hn.some⟩,
    fun k hk => (hother k hk).of_iso (RelativeChains.pointHomotopyEquivIso s v k)⟩

end SphereCover

namespace RelativeChains
open Set CategoryTheory HomologicalComplex SingularChains
variable {X : Type} [TopologicalSpace X] [ContractibleSpace X]

def contractiblePairIso (A : Set X) (x : A) (n : ℕ) :
    (complex A).homology (n+1) ≅ (complex ({x} : Set A)).homology n := by
  let h : ({x.1} : Set X) ⊆ A := singleton_subset_iff.mpr x.2
  have e := (triple_shortExact h).δIso (n+1) n rfl
    (contractible_singleton_homology_isZero x.1 (n+1)) (contractible_singleton_homology_isZero x.1 n)
  simpa only [triple,preimage_singleton_inclusion x] using e

lemma contractiblePair_zero (A : Set X) (x : A) : Limits.IsZero ((complex A).homology 0) :=
  ChainShortExact.zero_homology₃_zero (triple_shortExact (singleton_subset_iff.mpr x.2))
    (contractible_singleton_homology_isZero x.1 0)

end RelativeChains

namespace DiskHomology
open Set Metric CategoryTheory HomologicalComplex
variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Disk := closedBall (0 : E) 1
abbrev Boundary : Set (Disk E) := (SingularSubspace.inclusionMap (closedBall (0 : E) 1)) ⁻¹' sphere (0 : E) 1

def boundaryEquiv : Boundary E ≃ₜ SphereCover.Sphere E where
  toEquiv :=
    { toFun := fun x => ⟨x.1.1,x.2⟩
      invFun := fun x => ⟨⟨x.1,sphere_subset_closedBall x.2⟩,x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

lemma contractible : ContractibleSpace (Disk E) :=
  (convex_closedBall (0 : E) 1).contractibleSpace ⟨0,by norm_num⟩

lemma homology [FiniteDimensional ℝ E] (n : ℕ) (hd : Module.finrank ℝ E = n+1) :
    Nonempty ((RelativeChains.complex (Boundary E)).homology (n+1) ≅ ModuleCat.of ℤ ℤ) ∧
      ∀ k, k ≠ n+1 → Limits.IsZero ((RelativeChains.complex (Boundary E)).homology k) := by
  let := contractible E
  let : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hd
  obtain ⟨v,hv⟩ := exists_norm_eq E (by norm_num : (0 : ℝ) ≤ 1)
  let s : SphereCover.Sphere E := ⟨v,by simpa only [mem_sphere,dist_zero_right] using hv⟩
  let x : Boundary E := (boundaryEquiv E).symm s
  let d (k : ℕ) : (RelativeChains.complex (Boundary E)).homology (k+1) ≅
      (RelativeChains.complex ({(boundaryEquiv E) x} : Set (SphereCover.Sphere E))).homology k :=
    RelativeChains.contractiblePairIso (Boundary E) x k ≪≫
      RelativeChains.pointHomotopyEquivIso (boundaryEquiv E).toHomotopyEquiv x k
  obtain ⟨hn,hother⟩ := SphereCover.normed_homology n hd ((boundaryEquiv E) x)
  refine ⟨⟨d n ≪≫ hn.some⟩,?_⟩
  intro k hk
  cases k with
  | zero => exact RelativeChains.contractiblePair_zero (Boundary E) x
  | succ k => exact (hother k (by omega)).of_iso (d k)

end DiskHomology

namespace FinsuppHomology
open CategoryTheory HomologicalComplex
variable {R : Type} [CommRing R] (ι : Type)

abbrev obj (M : ModuleCat.{0} R) := ModuleCat.of R (ι →₀ M)
def map {M N : ModuleCat.{0} R} (f : M ⟶ N) : obj ι M ⟶ obj ι N :=
  ModuleCat.ofHom (Finsupp.mapRange.linearMap f.hom)
@[simp] lemma map_apply {M N : ModuleCat.{0} R} (f : M ⟶ N) (x : obj ι M) (i : ι) :
    map ι f x i = f (x i) := rfl

def singleObj (M : ModuleCat.{0} R) (i : ι) : M ⟶ obj ι M :=
  ModuleCat.ofHom (Finsupp.lsingle i)
def sumMap {M N : ModuleCat.{0} R} (f : ι → (M ⟶ N)) : obj ι M ⟶ N :=
  ModuleCat.ofHom (Finsupp.lsum R (fun i => (f i).hom))
lemma sumMap_single {M N : ModuleCat.{0} R} (f : ι → (M ⟶ N)) (i : ι) (x : M) :
    sumMap ι f (Finsupp.single i x) = f i x := Finsupp.lsum_single _ _ _ _

def complex (C : ChainComplex (ModuleCat.{0} R) ℕ) : ChainComplex (ModuleCat.{0} R) ℕ where
  X n := obj ι (C.X n)
  d n m := map ι (C.d n m)
  shape n m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro i
    change C.d n m (x i) = 0
    rw [C.shape n m h]
    rfl
  d_comp_d' n m k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro i
    change C.d m k (C.d n m (x i)) = 0
    exact congrArg (fun f : C.X n ⟶ C.X k => f (x i)) (C.d_comp_d n m k)

def single (C : ChainComplex (ModuleCat.{0} R) ℕ) (i : ι) : C ⟶ complex ι C where
  f n := ModuleCat.ofHom (Finsupp.lsingle i)
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Finsupp.mapRange (C.d n m) (map_zero _) (Finsupp.single i x) = Finsupp.single i (C.d n m x)
    simp

def eval (C : ChainComplex (ModuleCat.{0} R) ℕ) (i : ι) : complex ι C ⟶ C where
  f _ := ModuleCat.ofHom (Finsupp.lapply i)
  comm' _ _ _ := rfl

lemma single_eval (C : ChainComplex (ModuleCat.{0} R) ℕ) (i : ι) : single ι C i ≫ eval ι C i = 𝟙 C := by
  ext n x
  change (Finsupp.single i x) i = x
  exact Finsupp.single_eq_same
lemma single_eval_ne (C : ChainComplex (ModuleCat.{0} R) ℕ) {i j : ι} (h : i ≠ j) :
    single ι C i ≫ eval ι C j = 0 := by
  ext n x
  change (Finsupp.single i x) j = 0
  exact Finsupp.single_eq_of_ne (Ne.symm h)

def homologySum (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    obj ι (C.homology n) ⟶ (complex ι C).homology n :=
  ModuleCat.ofHom (Finsupp.lsum R (fun i => (homologyMap (single ι C i) n).hom))

@[simp] lemma homologySum_single (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) (i : ι)
    (x : C.homology n) : homologySum ι C n (Finsupp.single i x) = homologyMap (single ι C i) n x := by
  change Finsupp.lsum R (fun j => (homologyMap (single ι C j) n).hom) (Finsupp.single i x) = _
  exact Finsupp.lsum_single _ _ _ _

lemma eval_homologySum (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) (i : ι)
    (x : obj ι (C.homology n)) : homologyMap (eval ι C i) n (homologySum ι C n x) = x i := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx,hy]
  | single j x =>
    rw [homologySum_single]
    change (homologyMap (single ι C j) n ≫ homologyMap (eval ι C i) n) x = _
    rw [← homologyMap_comp]
    by_cases h : j = i
    · subst j; simp [single_eval]
    · simp [single_eval_ne ι C h,Finsupp.single_eq_of_ne (Ne.symm h)]

lemma homologySum_injective (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Function.Injective (homologySum ι C n) := by
  intro x y h
  ext i
  calc
    x i = homologyMap (eval ι C i) n (homologySum ι C n x) := (eval_homologySum ι C n i x).symm
    _ = homologyMap (eval ι C i) n (homologySum ι C n y) := congrArg _ h
    _ = y i := eval_homologySum ι C n i y

lemma homologySum_surjective (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Function.Surjective (homologySum ι C n) := by
  classical
  let S := C.sc n
  let T := (complex ι C).sc n
  intro x
  obtain ⟨c,rfl⟩ := ModuleHomology.classMap_surjective T x
  let cc : ι →₀ C.X n := c.1
  have hc (i : ι) : S.g (cc i) = 0 := by
    have h := congrArg (fun v : ι →₀ C.X ((ComplexShape.down ℕ).next n) => v i) c.2
    exact h
  let z (i : ι) : S.moduleCatLeftHomologyData.K := ⟨cc i,hc i⟩
  refine ⟨∑ i ∈ cc.support, Finsupp.single i (ModuleHomology.classMap S (z i)),?_⟩
  simp only [map_sum]
  dsimp only [HomologicalComplex.homology] at *
  have hsingle (i : ι) : homologyMap (single ι C i) n (ModuleHomology.classMap S (z i)) =
      ModuleHomology.classMap T (ModuleHomology.cyclesMap ((shortComplexFunctor _ _ n).map (single ι C i)) (z i)) :=
    ModuleHomology.homologyMap_class _ _
  refine Eq.trans (b := ∑ i ∈ cc.support,
    homologyMap (single ι C i) n (ModuleHomology.classMap S (z i))) ?_ ?_
  · apply Finset.sum_congr rfl
    intro i hi
    exact homologySum_single ι C n i _
  refine Eq.trans (b := ∑ i ∈ cc.support, ModuleHomology.classMap T
    (ModuleHomology.cyclesMap ((shortComplexFunctor _ _ n).map (single ι C i)) (z i))) ?_ ?_
  · apply Finset.sum_congr rfl
    intro i hi
    exact hsingle i

  rw [← map_sum]
  congr 1
  apply Subtype.ext
  exact Eq.trans (map_sum (LinearMap.ker T.g.hom).subtype _ _) (Finsupp.sum_single cc)

def homologyIso (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    obj ι (C.homology n) ≅ (complex ι C).homology n :=
  LinearEquiv.toModuleIso (LinearEquiv.ofBijective (homologySum ι C n).hom
    ⟨homologySum_injective ι C n,homologySum_surjective ι C n⟩)

end FinsuppHomology

end

end OAI
