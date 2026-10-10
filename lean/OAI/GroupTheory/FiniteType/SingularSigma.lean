import Mathlib
import OAI.GroupTheory.FiniteType.RelativeChainsEmptyProjectionQuasiIso

namespace OAI

noncomputable section
open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace SingularSigma
open Set CategoryTheory HomologicalComplex SingularChains
attribute [-instance] AddCommGroup.toIntModule
variable {ι X : Type} [TopologicalSpace X]
abbrev Space (ι X : Type) := Σ _ : ι, X

def incl (i : ι) : C(X,Space ι X) := ⟨fun x => (⟨i,x⟩ : Space ι X),(continuous_sigmaMk (σ := fun _ : ι => X))⟩
def snd : C(Space ι X,X) := ⟨Sigma.snd,continuous_sigma fun _ => continuous_id⟩
def index {n : ℕ} (f : C(Std n,Space ι X)) : ι := (f (Convexity.StdSimplex.single 0)).1
lemma index_eq {n : ℕ} (f : C(Std n,Space ι X)) (s : Std n) : (f s).1 = index f := by
  let : TopologicalSpace ι := ⊥
  let : DiscreteTopology ι := ⟨rfl⟩
  exact PreconnectedSpace.constant (inferInstance : PreconnectedSpace (Std n))
    (f := fun s => (f s).1) ((continuous_sigma fun _ => continuous_const).comp f.continuous)
lemma incl_snd {n : ℕ} (f : C(Std n,Space ι X)) : (incl (index f)).comp (snd.comp f) = f := by
  apply ContinuousMap.ext
  intro s
  change Sigma.mk (index f) (f s).2 = f s
  have h := index_eq f s
  cases hf : f s with | mk i x => simp only [hf] at h ⊢; exact congrArg (fun i => Sigma.mk i x) h.symm
lemma index_incl {n : ℕ} (i : ι) (f : C(Std n,X)) : index ((incl i).comp f) = i := rfl
lemma snd_incl {n : ℕ} (i : ι) (f : C(Std n,X)) : snd.comp ((incl i).comp f) = f := rfl

variable (ι) (A : Set X)
def subset : Set (Space ι X) := snd ⁻¹' A

def inclPair (i : ι) : RelativeChains.complex A ⟶ RelativeChains.complex (subset ι A) :=
  RelativeChains.map A (subset ι A) (incl i) (fun _ h => h)

def merge : FinsuppHomology.complex ι (RelativeChains.complex A) ⟶ RelativeChains.complex (subset ι A) where
  f n := FinsuppHomology.sumMap ι (fun i => (inclPair ι A i).f n)
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro i x
    change (RelativeChains.complex (subset ι A)).d n m
      (FinsuppHomology.sumMap ι (fun i => (inclPair ι A i).f n) (Finsupp.single i x)) =
      FinsuppHomology.sumMap ι (fun i => (inclPair ι A i).f m)
        (Finsupp.mapRange ((RelativeChains.complex A).d n m).hom (map_zero _) (Finsupp.single i x))
    rw [FinsuppHomology.sumMap_single,Finsupp.mapRange_single,FinsuppHomology.sumMap_single]
    exact congrArg (fun f => f x) ((inclPair ι A i).comm n m)

@[simp] lemma merge_single (n : ℕ) (i : ι) (x : (RelativeChains.complex A).X n) :
    (merge ι A).f n (Finsupp.single i x) = (inclPair ι A i).f n x := by
  exact FinsuppHomology.sumMap_single _ _ _ _

def splitAbsolute (n : ℕ) : (chains (Space ι X)).X n ⟶
    FinsuppHomology.obj ι ((RelativeChains.complex A).X n) :=
  desc (fun f => generator (snd.comp f) ≫ (RelativeChains.projection A).f n ≫
    FinsuppHomology.singleObj ι _ (index f))

lemma splitAbsolute_gen {n : ℕ} (f : C(Std n,Space ι X)) :
    splitAbsolute ι A n (SingularSupport.gen f) =
      Finsupp.single (index f) ((RelativeChains.projection A).f n (SingularSupport.gen (snd.comp f))) := by
  change (generator f ≫ splitAbsolute ι A n) 1 = _
  rw [splitAbsolute,generator_desc]
  rfl

lemma splitAbsolute_kill (n : ℕ) : SingularSubspace.group (subset ι A) n ≤
    LinearMap.ker (splitAbsolute ι A n).hom := by
  apply Submodule.span_le.mpr
  rintro _ ⟨f,hf,rfl⟩
  change splitAbsolute ι A n (SingularSupport.gen f) = 0
  rw [splitAbsolute_gen]
  have hz : (RelativeChains.projection A).f n (SingularSupport.gen (snd.comp f)) = 0 := by
    apply (RelativeChains.projection_zero_iff A n _).mpr
    apply SingularSupport.gen_mem
    rintro _ ⟨s,rfl⟩
    exact hf (mem_range_self s)
  rw [hz,Finsupp.single_zero]

def split (n : ℕ) : (RelativeChains.complex (subset ι A)).X n ⟶
    FinsuppHomology.obj ι ((RelativeChains.complex A).X n) :=
  ModuleCat.ofHom ((SingularSubspace.group (subset ι A) n).liftQ (splitAbsolute ι A n).hom
    (splitAbsolute_kill ι A n))

lemma split_projection (n : ℕ) (x : (chains (Space ι X)).X n) :
    split ι A n ((RelativeChains.projection (subset ι A)).f n x) = splitAbsolute ι A n x := rfl

lemma merge_splitAbsolute (n : ℕ) : splitAbsolute ι A n ≫ (merge ι A).f n =
    (RelativeChains.projection (subset ι A)).f n := by
  apply SingularChains.hom_ext
  intro f
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (merge ι A).f n (splitAbsolute ι A n (SingularSupport.gen f)) = _
  erw [splitAbsolute_gen,merge_single,inclPair,RelativeChains.map_projection,SingularSupport.map_gen,incl_snd]
  rfl

lemma splitAbsolute_incl (n : ℕ) (i : ι) :
    (SingularChains.map (incl (X := X) i)).f n ≫ splitAbsolute ι A n =
      (RelativeChains.projection A).f n ≫ FinsuppHomology.singleObj ι _ i := by
  apply SingularChains.hom_ext
  intro f
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change splitAbsolute ι A n ((SingularChains.map (incl i)).f n (SingularSupport.gen f)) = _
  rw [SingularSupport.map_gen,splitAbsolute_gen,index_incl,snd_incl]
  rfl

lemma merge_split (n : ℕ) : split ι A n ≫ (merge ι A).f n = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x,rfl⟩ := RelativeChains.projection_surjective (subset ι A) n x
  change (merge ι A).f n (split ι A n ((RelativeChains.projection (subset ι A)).f n x)) = _
  rw [split_projection]
  exact congrArg (fun f => f x) (merge_splitAbsolute ι A n)

lemma split_merge (n : ℕ) : (merge ι A).f n ≫ split ι A n = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro i x
  obtain ⟨x,rfl⟩ := RelativeChains.projection_surjective A n x
  change split ι A n ((merge ι A).f n (Finsupp.single i ((RelativeChains.projection A).f n x))) = Finsupp.single i ((RelativeChains.projection A).f n x)
  erw [merge_single,inclPair,RelativeChains.map_projection,split_projection]
  exact congrArg (fun f => f x) (splitAbsolute_incl ι A n i)

instance merge_isIso : IsIso (merge ι A) := by
  have (n : ℕ) : IsIso ((merge ι A).f n) := ⟨⟨split ι A n,split_merge ι A n,merge_split ι A n⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components _

def homologyIso (n : ℕ) : ModuleCat.of ℤ (ι →₀ (RelativeChains.complex A).homology n) ≅
    (RelativeChains.complex (subset ι A)).homology n :=
  FinsuppHomology.homologyIso ι (RelativeChains.complex A) n ≪≫
    (homologyFunctor _ _ n).mapIso (asIso (merge ι A))

attribute [instance] AddCommGroup.toIntModule
end SingularSigma

namespace RelativeChains
open Set CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X]
def setIso (A B : Set X) (h : A = B) : complex A ≅ complex B where
  hom := map A B (ContinuousMap.id _) (fun _ hx => h.subset hx)
  inv := map B A (ContinuousMap.id _) (fun _ hx => h.symm.subset hx)
  hom_inv_id := by erw [map_comp]; exact map_id A
  inv_hom_id := by erw [map_comp]; exact map_id B
lemma map_setIso (A B D : Set X) (h : B = D) (f : C(X,X)) (hf : MapsTo f A B) :
    map A B f hf ≫ (setIso B D h).hom = map A D f (fun _ hx => h.subset (hf hx)) := by
  exact map_comp A B D f (ContinuousMap.id _) hf (fun _ hx => h.subset hx)
end RelativeChains

namespace FinsuppHomology
open CategoryTheory
variable {R : Type} [CommRing R] (ι : Type)
def objIso {M N : ModuleCat.{0} R} (e : M ≅ N) : obj ι M ≅ obj ι N :=
  LinearEquiv.toModuleIso (Finsupp.mapRange.linearEquiv e.toLinearEquiv)
lemma obj_isZero {M : ModuleCat.{0} R} (h : Limits.IsZero M) : Limits.IsZero (obj ι M) := by
  let := ModuleCat.subsingleton_of_isZero h
  exact ModuleCat.isZero_of_subsingleton _
end FinsuppHomology

namespace DiskHomology
open Set Metric CategoryTheory HomologicalComplex
lemma boundary_zero : Boundary (Fin 0 → ℝ) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h : x.1 = 0 := Subsingleton.elim _ _
  have hh : ‖x.1‖ = 1 := by
    change x.1 ∈ sphere (0 : Fin 0 → ℝ) 1 at hx
    simpa only [mem_sphere,dist_zero_right] using hx
  rw [h,norm_zero] at hh
  norm_num at hh

def zeroHomologyIso : (RelativeChains.complex (Boundary (Fin 0 → ℝ))).homology 0 ≅ ModuleCat.of ℤ ℤ := by
  rw [boundary_zero]
  letI : Unique (Disk (Fin 0 → ℝ)) := ⟨⟨0,by norm_num⟩,fun _ => Subsingleton.elim _ _⟩
  letI := RelativeChains.empty_projection_quasiIso (X := Disk (Fin 0 → ℝ))
  exact (asIso (homologyMap (RelativeChains.projection (∅ : Set (Disk (Fin 0 → ℝ)))) 0)).symm ≪≫
    SingularChains.unique_homologyZeroIso

lemma zeroHomology_isZero (k : ℕ) (hk : k ≠ 0) :
    Limits.IsZero ((RelativeChains.complex (Boundary (Fin 0 → ℝ))).homology k) := by
  rw [boundary_zero]
  let := RelativeChains.empty_projection_quasiIso (X := Disk (Fin 0 → ℝ))
  let := contractible (Fin 0 → ℝ)
  exact (SingularChains.contractible_homology_isZero k (by omega)).of_iso
    (asIso (homologyMap (RelativeChains.projection (∅ : Set (Disk (Fin 0 → ℝ)))) k)).symm

def cellIso (n : ℕ) : (RelativeChains.complex (Boundary (Fin n → ℝ))).homology n ≅ ModuleCat.of ℤ ℤ := by
  cases n with
  | zero => exact zeroHomologyIso
  | succ n => exact (homology (Fin (n+1) → ℝ) n (by simp)).1.some
lemma cell_isZero (n k : ℕ) (hk : k ≠ n) :
    Limits.IsZero ((RelativeChains.complex (Boundary (Fin n → ℝ))).homology k) := by
  cases n with
  | zero => exact zeroHomology_isZero k hk
  | succ n => exact (homology (Fin (n+1) → ℝ) n (by simp)).2 k hk
end DiskHomology

namespace CWSkeletalHomology
attribute [-instance] AddCommGroup.toIntModule
open Set Topology Metric CWExtension CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

abbrev complex (n : ℕ) := RelativeChains.complex (CWCollar.lower (C := C) n)

omit [T2Space X] in
lemma boundary_eq (n : ℕ) : CWSingularPair.Boundary (C := C) n =
    SingularSigma.subset (RelCWComplex.cell C n) (DiskHomology.Boundary (Fin n → ℝ)) := by
  ext z
  change ‖z.2.1‖ = 1 ↔ z.2.1 ∈ sphere (0 : Fin n → ℝ) 1
  simp only [mem_sphere,dist_zero_right]

def diskSumIso (n k : ℕ) :
    ModuleCat.of ℤ (RelCWComplex.cell C n →₀ (RelativeChains.complex (DiskHomology.Boundary (Fin n → ℝ))).homology k) ≅
      (RelativeChains.complex (CWSingularPair.Boundary (C := C) n)).homology k :=
  SingularSigma.homologyIso (RelCWComplex.cell C n) (DiskHomology.Boundary (Fin n → ℝ)) k ≪≫
    (homologyFunctor _ _ k).mapIso
      (RelativeChains.setIso _ _ (boundary_eq (C := C) n).symm)

def characteristicMap (n : ℕ) :
    RelativeChains.complex (CWSingularPair.Boundary (C := C) n) ⟶ complex (C := C) n :=
  RelativeChains.map (CWSingularPair.Boundary n) (CWCollar.lower n)
    (CWSingularPair.attach (C := C) n) (CWSingularPair.maps_boundary n)

def characteristicIso (n k : ℕ) :
    (RelativeChains.complex (CWSingularPair.Boundary (C := C) n)).homology k ≅ (complex (C := C) n).homology k := by
  letI : QuasiIso (characteristicMap (C := C) n) := CWSingularPair.quasiIso (C := C) n
  exact asIso (homologyMap (characteristicMap n) k)

lemma characteristicIso_hom (n k : ℕ) : (characteristicIso (C := C) n k).hom =
    homologyMap (characteristicMap n) k := rfl

def basisIso (n : ℕ) : ModuleCat.of ℤ (RelCWComplex.cell C n →₀ ℤ) ≅ (complex (C := C) n).homology n :=
  (FinsuppHomology.objIso (RelCWComplex.cell C n) (DiskHomology.cellIso n)).symm ≪≫
    diskSumIso (C := C) n n ≪≫ characteristicIso (C := C) n n

lemma homology_isZero (n k : ℕ) (hk : k ≠ n) : Limits.IsZero ((complex (C := C) n).homology k) :=
  (FinsuppHomology.obj_isZero (RelCWComplex.cell C n) (DiskHomology.cell_isZero n k hk)).of_iso
    ((diskSumIso (C := C) n k ≪≫ characteristicIso (C := C) n k).symm)

attribute [instance] AddCommGroup.toIntModule
end CWSkeletalHomology

end

end OAI
