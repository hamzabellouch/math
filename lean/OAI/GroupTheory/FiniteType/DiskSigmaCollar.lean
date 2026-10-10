import Mathlib
import OAI.GroupTheory.FiniteType.DiskRadial

namespace OAI

noncomputable section
open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace DiskSigmaCollar
open Set Topology Metric
open scoped unitInterval
variable (ι E : Type) [NormedAddCommGroup E]

abbrev Disks := Σ _i : ι, DiskRadial.Disk (E := E)
abbrev Opens := Σ _i : ι, ball (0 : E) 1

def radius : C(Disks ι E,ℝ) :=
  ⟨fun z => ‖(z.2 : E)‖,continuous_sigma (fun _ => continuous_norm.comp continuous_subtype_val)⟩
def boundary : Set (Disks ι E) := radius ι E ⁻¹' {1}
def collar : Set (Disks ι E) := radius ι E ⁻¹' Ioi (1/2)
lemma boundary_closed : IsClosed (boundary ι E) := isClosed_singleton.preimage (radius ι E).continuous
lemma collar_open : IsOpen (collar ι E) := isOpen_Ioi.preimage (radius ι E).continuous
lemma boundary_subset_collar : boundary ι E ⊆ collar ι E := by intro x hx; change (1/2:ℝ) < radius ι E x; rw [show radius ι E x = 1 from hx]; norm_num

variable [NormedSpace ℝ E]

def paths : C(Disks ι E,C(I,Disks ι E)) :=
  ⟨fun z => ⟨fun t => ⟨z.1,DiskRadial.radial t z.2⟩,
    continuous_sigmaMk.comp (DiskRadial.continuous_radial.comp (continuous_id.prodMk continuous_const))⟩,
    continuous_sigma (fun i => (⟨fun z : DiskRadial.Disk (E := E) × I => (⟨i,DiskRadial.radial z.2 z.1⟩ : Disks ι E),
      continuous_sigmaMk.comp (DiskRadial.continuous_radial.comp continuous_swap)⟩ : C(_, _)).curry.continuous)⟩

@[simp] lemma paths_zero (x : Disks ι E) : paths ι E x 0 = x := by rcases x with ⟨i,v⟩; change (⟨i,DiskRadial.radial 0 v⟩ : Disks ι E) = _; rw [DiskRadial.radial_zero]
lemma paths_mem (x : Disks ι E) (hx : x ∈ collar ι E) (t : I) : paths ι E x t ∈ collar ι E :=
  lt_of_lt_of_le hx (DiskRadial.norm_le_radial t x.2)
lemma paths_one (x : Disks ι E) (hx : x ∈ collar ι E) : paths ι E x 1 ∈ boundary ι E := by
  change ‖(DiskRadial.radial 1 x.2 : E)‖ = 1
  rw [DiskRadial.radial_one]
  exact DiskRadial.norm_inflate_of_half_lt x.2 hx
lemma paths_fixed (x : Disks ι E) (hx : x ∈ boundary ι E) (t : I) : paths ι E x t = x := by
  rcases x with ⟨i,v⟩
  change (⟨i,DiskRadial.radial t v⟩ : Disks ι E) = _
  rw [DiskRadial.radial_boundary t v hx]

def inclusion : C(boundary ι E,collar ι E) :=
  ⟨Set.inclusion (boundary_subset_collar ι E),continuous_subtype_val.subtype_mk _⟩
def retract : C(collar ι E,boundary ι E) :=
  ⟨fun x => ⟨paths ι E x 1,paths_one ι E x x.2⟩,
    (((paths ι E).continuous.comp continuous_subtype_val).eval continuous_const).subtype_mk _⟩
def homotopy : ContinuousMap.Homotopy (ContinuousMap.id (collar ι E)) ((inclusion ι E).comp (retract ι E)) where
  toFun z := ⟨paths ι E z.2 z.1,paths_mem ι E z.2 z.2.2 z.1⟩
  continuous_toFun := (((paths ι E).continuous.comp (continuous_subtype_val.comp continuous_snd)).eval continuous_fst).subtype_mk _
  map_zero_left x := Subtype.ext (paths_zero ι E x)
  map_one_left _ := rfl

def collarEquiv : ContinuousMap.HomotopyEquiv (boundary ι E) (collar ι E) where
  toFun := inclusion ι E
  invFun := retract ι E
  left_inv := by
    have he : (retract ι E).comp (inclusion ι E) = ContinuousMap.id (boundary ι E) := by
      apply ContinuousMap.ext
      intro x
      exact Subtype.ext (paths_fixed ι E x x.2 1)
    rw [he]
  right_inv := ⟨(homotopy ι E).symm⟩

omit [NormedSpace ℝ E]

def openMap (x : Opens ι E) : Disks ι E := ⟨x.1,⟨x.2,ball_subset_closedBall x.2.2⟩⟩
lemma openMap_embedding : IsEmbedding (openMap ι E) := by
  change IsEmbedding (Sigma.map (β₁ := fun _ : ι => ball (0 : E) 1) (β₂ := fun _ : ι => DiskRadial.Disk (E := E)) id (fun _ => Set.inclusion ball_subset_closedBall))
  exact (isEmbedding_sigmaMap Function.injective_id).mpr (fun _ => IsEmbedding.inclusion _)
lemma openMap_mem (x : Opens ι E) : openMap ι E x ∈ (boundary ι E)ᶜ := by
  change ‖(x.2 : E)‖ ≠ 1
  exact ne_of_lt (by simpa only [mem_ball,dist_zero_right] using x.2.2)
lemma openMap_surj : Function.Surjective (fun x : Opens ι E => (⟨openMap ι E x,openMap_mem ι E x⟩ : ↑((boundary ι E)ᶜ))) := by
  rintro ⟨⟨i,v⟩,hv⟩
  have hv' : (v : E) ∈ ball 0 1 := by
    rw [mem_ball,dist_zero_right]
    exact lt_of_le_of_ne (by simpa only [mem_closedBall,dist_zero_right] using v.2) hv
  exact ⟨⟨i,⟨v,hv'⟩⟩,rfl⟩

def openEquiv : Opens ι E ≃ₜ ↑((boundary ι E)ᶜ) :=
  ((openMap_embedding ι E).codRestrict _ (openMap_mem ι E)).toHomeomorphOfSurjective (openMap_surj ι E)

@[simp] lemma openEquiv_apply (x : Opens ι E) : (openEquiv ι E x).1 = openMap ι E x := rfl

end DiskSigmaCollar

namespace CWSingularPair
open Set Topology Metric CWExtension CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

abbrev Disks (n : ℕ) := DiskSigmaCollar.Disks (RelCWComplex.cell C n) (Fin n → ℝ)
abbrev Boundary (n : ℕ) := DiskSigmaCollar.boundary (RelCWComplex.cell C n) (Fin n → ℝ)
abbrev Collar (n : ℕ) := DiskSigmaCollar.collar (RelCWComplex.cell C n) (Fin n → ℝ)

def attach (n : ℕ) : C(Disks (C := C) n,Skel C (n+1)) :=
  ⟨fun z => charSkel n z.1 z.2,continuous_sigma (fun i => (charSkel n i).continuous)⟩

lemma radius_attach (n : ℕ) (z : Disks (C := C) n) :
    CWCollar.radius n (attach n z) = DiskSigmaCollar.radius (RelCWComplex.cell C n) (Fin n → ℝ) z :=
  CWCollar.radius_disk n z.1 z.2

lemma maps_boundary (n : ℕ) : MapsTo (attach (C := C) n) (Boundary n) (CWCollar.lower n) := by
  intro z hz
  apply (CWCollar.radius_eq_one_iff n _).mp
  rw [radius_attach]
  exact hz
lemma maps_collar (n : ℕ) : MapsTo (attach (C := C) n) (Collar n) (CWCollar.collar n) := by
  intro z hz
  change (1/2:ℝ) < CWCollar.radius n (attach n z)
  rw [radius_attach]
  exact hz

def complementEquiv (n : ℕ) : ↑((Boundary (C := C) n)ᶜ) ≃ₜ ↑((CWCollar.lower (C := C) n)ᶜ) :=
  (DiskSigmaCollar.openEquiv (RelCWComplex.cell C n) (Fin n → ℝ)).symm.trans (CWCollar.openCellsEquiv n)

lemma complementEquiv_apply (n : ℕ) (x : ↑((Boundary (C := C) n)ᶜ)) :
    (complementEquiv n x).1 = attach n x.1 := by
  obtain ⟨z,rfl⟩ := (DiskSigmaCollar.openEquiv (RelCWComplex.cell C n) (Fin n → ℝ)).surjective x
  change (CWCollar.openCellsEquiv n ((DiskSigmaCollar.openEquiv (RelCWComplex.cell C n) (Fin n → ℝ)).symm
    ((DiskSigmaCollar.openEquiv (RelCWComplex.cell C n) (Fin n → ℝ)) z))).1 = _
  rw [Homeomorph.symm_apply_apply]
  rfl

lemma collar_map_quasiIso (n : ℕ) : QuasiIso
    (RelativeChains.map (Collar n) (CWCollar.collar n) (attach (C := C) n) (maps_collar n)) := by
  apply RelativeChains.excision_map_quasiIso (Collar n) (Boundary n) (CWCollar.collar n) (CWCollar.lower n)
    (attach n) (maps_collar n) (DiskSigmaCollar.boundary_closed _ _)
    (by rw [(DiskSigmaCollar.collar_open _ _).interior_eq]; exact DiskSigmaCollar.boundary_subset_collar _ _)
    (CWCollar.lower_closed n)
    (by rw [(CWCollar.collar_open n).interior_eq]; exact CWCollar.lower_subset_collar n)
    (complementEquiv n) (complementEquiv_apply n)
  intro x
  rw [complementEquiv_apply]
  change (1/2:ℝ) < DiskSigmaCollar.radius _ _ x.1 ↔ (1/2:ℝ) < CWCollar.radius n (attach n x.1)
  rw [radius_attach]

theorem quasiIso (n : ℕ) : QuasiIso
    (RelativeChains.map (Boundary n) (CWCollar.lower n) (attach (C := C) n) (maps_boundary n)) := by
  let hD := DiskSigmaCollar.boundary_subset_collar (RelCWComplex.cell C n) (Fin n → ℝ)
  let hX := CWCollar.lower_subset_collar (C := C) n
  let d := RelativeChains.map (Boundary n) (Collar n) (ContinuousMap.id (Disks (C := C) n)) hD
  let s := RelativeChains.map (CWCollar.lower n) (CWCollar.collar n) (ContinuousMap.id (Skel C (n+1))) hX
  let f := RelativeChains.map (Boundary n) (CWCollar.lower n) (attach (C := C) n) (maps_boundary n)
  let g := RelativeChains.map (Collar n) (CWCollar.collar n) (attach (C := C) n) (maps_collar n)
  have hd : QuasiIso d := RelativeChains.enlarge_quasiIso hD
    (SingularChains.homotopyEquiv_quasiIso (DiskSigmaCollar.collarEquiv _ _))
  have hs : QuasiIso s := RelativeChains.enlarge_quasiIso hX
    (SingularChains.homotopyEquiv_quasiIso (CWCollar.collarEquiv n))
  have hg : QuasiIso g := collar_map_quasiIso n
  let := hd
  let := hs
  let := hg
  have comm : f ≫ s = d ≫ g := by
    dsimp [f,s,d,g]
    erw [RelativeChains.map_comp,RelativeChains.map_comp]
    rfl
  have : QuasiIso (f ≫ s) := by rw [comm]; infer_instance
  exact quasiIso_of_comp_right f s

end CWSingularPair

namespace RelativeChains
open Set CategoryTheory HomologicalComplex SingularChains
variable {X : Type} [TopologicalSpace X]

def quotientMap {D A : Set X} (h : D ⊆ A) : complex D ⟶ complex A :=
  map D A (ContinuousMap.id X) h

@[simp] lemma quotientMap_projection {D A : Set X} (h : D ⊆ A) (n : ℕ) (c : (chains X).X n) :
    (quotientMap h).f n ((projection D).f n c) = (projection A).f n c := by
  erw [quotientMap,map_projection,SingularChains.map_id]
  rfl

def triple {D A : Set X} (h : D ⊆ A) : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (inclusion D A) (quotientMap h) (by
    ext n z
    obtain ⟨c,rfl⟩ := projection_surjective ((SingularSubspace.inclusionMap A) ⁻¹' D) n z
    change (quotientMap h).f n ((projection D).f n
      ((SingularChains.map (SingularSubspace.inclusionMap A)).f n c)) = 0
    rw [quotientMap_projection]
    exact (projection_zero_iff A n _).mpr (SingularSubspace.inclusion_mem A n c))

lemma triple_shortExact {D A : Set X} (h : D ⊆ A) : (triple h).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro z hz
    obtain ⟨c,rfl⟩ := projection_surjective D n z
    change (quotientMap h).f n ((projection D).f n c) = 0 at hz
    rw [quotientMap_projection] at hz
    have hc := (projection_zero_iff A n c).mp hz
    refine ⟨(projection ((SingularSubspace.inclusionMap A) ⁻¹' D)).f n
      (SingularSubspace.lift A n c),?_⟩
    change (projection D).f n ((SingularChains.map (SingularSubspace.inclusionMap A)).f n
      (SingularSubspace.lift A n c)) = _
    rw [SingularSubspace.lift_inclusion_apply A hc]
  · exact (ModuleCat.mono_iff_injective _).mpr (inclusion_injective D A n)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro z
    obtain ⟨c,rfl⟩ := projection_surjective A n z
    exact ⟨(projection D).f n c,quotientMap_projection h n c⟩

lemma univ_isZero (n : ℕ) : Limits.IsZero ((complex (univ : Set X)).X n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun z w => ?_⟩
  suffices ∀ z : (complex (univ : Set X)).X n,z = 0 by rw [this z,this w]
  intro z
  obtain ⟨c,rfl⟩ := projection_surjective (univ : Set X) n z
  apply (projection_zero_iff _ _ _).mpr
  exact SingularSupport.induction_on _ (fun f => SingularSupport.gen_mem f (subset_univ _)) c

end RelativeChains

namespace SingularChains
open CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X]

lemma constant_quasiIso [ContractibleSpace X] :
    QuasiIso (map (ContinuousMap.const X (() : Unit))) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  convert homotopyEquiv_quasiIso e using 1
  congr 1

end SingularChains

end

end OAI
