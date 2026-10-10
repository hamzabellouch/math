import Mathlib
import OAI.GroupTheory.FiniteType.RepresentationKilling

namespace OAI

noncomputable section

section
attribute [-instance] AddCommGroup.toIntModule
namespace SingularSigma
open Set CategoryTheory HomologicalComplex
variable {ι X : Type} [TopologicalSpace X] (A : Set X)

lemma single_merge (i : ι) : FinsuppHomology.single ι (RelativeChains.complex A) i ≫
    merge ι A = inclPair ι A i := by
  ext n x
  exact merge_single ι A n i x

lemma homologyIso_single (n : ℕ) (i : ι) (x : (RelativeChains.complex A).homology n) :
    (homologyIso ι A n).hom (Finsupp.single i x) = homologyMap (inclPair ι A i) n x := by
  change homologyMap (merge ι A) n
    (FinsuppHomology.homologySum ι (RelativeChains.complex A) n (Finsupp.single i x)) = _
  rw [FinsuppHomology.homologySum_single]
  change (homologyMap (FinsuppHomology.single ι (RelativeChains.complex A) i) n ≫
    homologyMap (merge ι A) n) x = _
  rw [← homologyMap_comp,single_merge]

end SingularSigma

namespace CWSkeletalHomology
open Set Topology Metric CWExtension CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

lemma oneDisk_maps (n : ℕ) (i : RelCWComplex.cell C n) :
    MapsTo (charSkel n i) (DiskHomology.Boundary (Fin n → ℝ)) (CWCollar.lower (C := C) n) := by
  intro v hv
  apply (CWCollar.radius_eq_one_iff n _).mp
  rw [CWCollar.radius_disk]
  change v.1 ∈ sphere (0 : Fin n → ℝ) 1 at hv
  simpa only [mem_sphere,dist_zero_right] using hv

def oneDisk (n : ℕ) (i : RelCWComplex.cell C n) :
    RelativeChains.complex (DiskHomology.Boundary (Fin n → ℝ)) ⟶ complex (C := C) n :=
  RelativeChains.map _ _ (charSkel n i) (oneDisk_maps n i)

def inclDisk (n : ℕ) (i : RelCWComplex.cell C n) :
    RelativeChains.complex (DiskHomology.Boundary (Fin n → ℝ)) ⟶
      RelativeChains.complex (CWSingularPair.Boundary (C := C) n) :=
  RelativeChains.map _ _ (SingularSigma.incl i)
    (by rw [boundary_eq]; exact fun _ h => h)

lemma inclDisk_comp (n : ℕ) (i : RelCWComplex.cell C n) :
    inclDisk n i ≫ characteristicMap n = oneDisk n i := by
  unfold inclDisk characteristicMap oneDisk
  rw [RelativeChains.map_comp]
  rfl

omit [T2Space X] in
lemma diskSumIso_single (n k : ℕ) (i : RelCWComplex.cell C n)
    (x : (RelativeChains.complex (DiskHomology.Boundary (Fin n → ℝ))).homology k) :
    (diskSumIso (C := C) n k).hom (Finsupp.single i x) =
      homologyMap (inclDisk n i) k x := by
  change homologyMap (RelativeChains.setIso _ _ _).hom k
    ((SingularSigma.homologyIso _ _ k).hom (Finsupp.single i x)) = _
  rw [SingularSigma.homologyIso_single]
  change (homologyMap (SingularSigma.inclPair _ _ i) k ≫
    homologyMap (RelativeChains.setIso _ _ _).hom k) x = _
  rw [← homologyMap_comp]
  unfold SingularSigma.inclPair RelativeChains.setIso
  erw [RelativeChains.map_comp]
  · rfl
  · intro z hz
    simpa only [ContinuousMap.id_apply, boundary_eq] using hz

lemma basisIso_single (n : ℕ) (i : RelCWComplex.cell C n) (a : ℤ) :
    (basisIso (C := C) n).hom (Finsupp.single i a) =
      homologyMap (oneDisk n i) n ((DiskHomology.cellIso n).inv a) := by
  change (characteristicIso (C := C) n n).hom
    ((diskSumIso (C := C) n n).hom
      (Finsupp.mapRange (DiskHomology.cellIso n).toLinearEquiv.symm (map_zero _)
        (Finsupp.single i a))) = _
  rw [Finsupp.mapRange_single,diskSumIso_single]
  rw [characteristicIso_hom]
  change (homologyMap (inclDisk n i) n ≫ homologyMap (characteristicMap n) n)
    ((DiskHomology.cellIso n).inv a) = _
  rw [← homologyMap_comp,inclDisk_comp]
end CWSkeletalHomology

namespace CWCellular.SkeletalMap
open Set Topology CWExtension CategoryTheory HomologicalComplex
variable {X Y : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  {C : Set X} {D : Set Y} [CWComplex C] [CWComplex D]
variable (f : SkeletalMap C D) (g : ∀ n, RelCWComplex.cell C n → RelCWComplex.cell D n)
  (h : ∀ n i (v : Disk n), f.toMap (RelCWComplex.map n i v) = RelCWComplex.map n (g n i) v)

include h
lemma oneDisk_natural (n : ℕ) (i : RelCWComplex.cell C n) :
    CWSkeletalHomology.oneDisk n i ≫ f.relativeMap n = CWSkeletalHomology.oneDisk n (g n i) := by
  unfold CWSkeletalHomology.oneDisk relativeMap
  rw [RelativeChains.map_comp]
  congr 1
  apply ContinuousMap.ext
  intro v
  exact Subtype.ext (h n i v)

lemma basis_natural (n : ℕ) (i : RelCWComplex.cell C n) (a : ℤ) :
    f.cellMap n ((CWSkeletalHomology.basisIso n).hom (Finsupp.single i a)) =
      (CWSkeletalHomology.basisIso n).hom (Finsupp.single (g n i) a) := by
  rw [CWSkeletalHomology.basisIso_single,CWSkeletalHomology.basisIso_single]
  change (homologyMap (CWSkeletalHomology.oneDisk n i) n ≫ homologyMap (f.relativeMap n) n) _ = _
  rw [← homologyMap_comp,f.oneDisk_natural g h]
end CWCellular.SkeletalMap

attribute [instance] AddCommGroup.toIntModule

end

namespace CWEquivariant
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension CWCellular CategoryTheory HomologicalComplex
variable {G X : Type} [Group G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
  [∀ n, MulAction G (RelCWComplex.cell (univ : Set X) n)]
variable (hc : ∀ (g : G) n (i : RelCWComplex.cell (univ : Set X) n) (v : Disk n),
  g • RelCWComplex.map n i v = RelCWComplex.map n (g • i) v)

include hc in
omit [ContinuousConstSMul G X] in
lemma smul_skel (g : G) (n : ℕ) : MapsTo (g • ·) (Skel (univ : Set X) n) (Skel (univ : Set X) n) := by
  intro x hx
  obtain ⟨m,hm,i,v,hv,rfl⟩ := CWComplex.mem_skeletonLT_iff.mp hx
  refine CWComplex.mem_skeletonLT_iff.mpr ⟨m,hm,g • i,v,hv,?_⟩
  exact (hc g m i ⟨v,Metric.ball_subset_closedBall hv⟩).symm

def skeletal (g : G) : SkeletalMap (univ : Set X) (univ : Set X) where
  toMap := ⟨(g • ·),continuous_const_smul g⟩
  maps := smul_skel hc g

abbrev rep (n : ℕ) := Representation.ofMulAction ℤ G (RelCWComplex.cell (univ : Set X) n)

def orientedIso (n : ℕ) : ModuleCat.of ℤ (MonoidAlgebra ℤ (RelCWComplex.cell (univ : Set X) n)) ≅
    cell (C := (univ : Set X)) n :=
  LinearEquiv.toModuleIso (MonoidAlgebra.coeffLinearEquiv ℤ) ≪≫ CWSkeletalHomology.basisIso n

lemma orientedIso_single (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n) (a : ℤ) :
    (orientedIso (X := X) n).hom (MonoidAlgebra.single i a) =
      (CWSkeletalHomology.basisIso n).hom (Finsupp.single i a) := rfl

lemma orientedIso_smul (g : G) (n : ℕ) (x : MonoidAlgebra ℤ (RelCWComplex.cell (univ : Set X) n)) :
    (skeletal hc g).cellMap n ((orientedIso n).hom x) = (orientedIso n).hom (rep (G := G) n g x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | single i a =>
    rw [Representation.ofMulAction_single,orientedIso_single,orientedIso_single]
    exact (skeletal hc g).basis_natural (fun _ i => g • i) (hc g) n i a

def boundary (n : ℕ) :
    MonoidAlgebra ℤ (RelCWComplex.cell (univ : Set X) (n+1)) →ₗ[ℤ]
      MonoidAlgebra ℤ (RelCWComplex.cell (univ : Set X) n) :=
  ((orientedIso n).inv).hom.comp ((d n).hom.comp ((orientedIso (n+1)).hom).hom)

lemma oriented_boundary (n : ℕ) (x : MonoidAlgebra ℤ (RelCWComplex.cell (univ : Set X) (n+1))) :
    (orientedIso n).hom (boundary n x) = d n ((orientedIso (n+1)).hom x) := by
  change ((orientedIso n).inv ≫ (orientedIso n).hom) (d n ((orientedIso (n+1)).hom x)) = _
  rw [Iso.inv_hom_id]
  rfl

include hc in
lemma boundary_smul (g : G) (n : ℕ) (x : MonoidAlgebra ℤ (RelCWComplex.cell (univ : Set X) (n+1))) :
    boundary n (rep (G := G) (n+1) g x) = rep (G := G) n g (boundary n x) := by
  apply (orientedIso n).toLinearEquiv.injective
  change (orientedIso n).hom _ = (orientedIso n).hom _
  rw [oriented_boundary,← orientedIso_smul hc,← orientedIso_smul hc,oriented_boundary]
  exact (congrArg (fun k => k ((orientedIso (n+1)).hom x)) ((skeletal hc g).d_natural n)).symm

def boundaryIntertwiner (n : ℕ) : (rep (G := G) (X := X) (n+1)).IntertwiningMap (rep (G := G) (X := X) n) :=
  (boundary n).intertwiningMap_of_isIntertwiningMap _ _ (fun g x => boundary_smul hc g n x)

abbrev module (n : ℕ) := (rep (G := G) (X := X) n).asModule

def moduleBoundary (n : ℕ) : module (G := G) (X := X) (n+1) →ₗ[MonoidAlgebra ℤ G] module (G := G) (X := X) n :=
  Representation.IntertwiningMap.equivLinearMapAsModule _ _ (boundaryIntertwiner hc n)

lemma boundary_comp (n : ℕ) : (moduleBoundary hc n).comp (moduleBoundary hc (n+1)) = 0 := by
  apply LinearMap.ext
  intro x
  apply (orientedIso n).toLinearEquiv.injective
  change (orientedIso n).hom (boundary n (boundary (n+1) x)) = (orientedIso n).hom 0
  erw [map_zero,oriented_boundary,oriented_boundary]
  exact congrArg (fun f => f ((orientedIso (n+2)).hom x)) (d_comp_d (C := (univ : Set X)) n)

lemma boundary_exact (n : ℕ) (h : Limits.IsZero ((SingularChains.chains (univ : Set X)).homology (n+1))) :
    Function.Exact (moduleBoundary hc (n+1)) (moduleBoundary hc n) := by
  intro x
  constructor
  · intro hx
    have hx' : d n ((orientedIso (n+1)).hom x) = 0 := by
      erw [← oriented_boundary]
      change (orientedIso n).hom (moduleBoundary hc n x) = 0
      erw [hx,map_zero]
    obtain ⟨y,hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp (exact_of_homology_zero n h)
      ((orientedIso (n+1)).hom x) hx'
    refine ⟨(orientedIso (n+2)).inv y,?_⟩
    apply (orientedIso (n+1)).toLinearEquiv.injective
    change (orientedIso (n+1)).hom (boundary (n+1) ((orientedIso (n+2)).inv y)) = _
    rw [oriented_boundary]
    change CWCellular.d (n+1) (((orientedIso (n+2)).inv ≫ (orientedIso (n+2)).hom) y) = _
    rw [Iso.inv_hom_id]
    exact hy
  · rintro ⟨y,rfl⟩
    exact congrArg (fun f => f y) (boundary_comp hc n)

attribute [instance] AddCommGroup.toIntModule
end CWEquivariant

end

end OAI
