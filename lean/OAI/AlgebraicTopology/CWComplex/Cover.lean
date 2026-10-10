import Mathlib.Tactic
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Normed.Module.Connected

namespace OAI

noncomputable section

open Classical Set Metric Topology

/-! Actual characteristic-cell lifts for an ordinary Whitehead CW complex.
This is a dependency toward (not an assumption replacing) the arbitrary-CW
presentation and cellular-cycle bridge. -/
open Set Metric Topology
namespace EilenbergGanea.CWCover

abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1

def diskCenter (n : ℕ) : Disk n := ⟨0,by simp⟩

instance diskContractible (n : ℕ) : ContractibleSpace (Disk n) :=
  contractibleSpace_closedBall (by norm_num)

instance diskLocallyPathConnected (n : ℕ) : LocallyPathConnectedSpace (Disk n) :=
  (convex_closedBall (0 : Fin n → ℝ) 1).locallyPathConnectedSpace

variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)

abbrev Cell (n : ℕ) := Topology.RelCWComplex.cell (univ : Set X) n

def characteristic {n : ℕ} (i : Cell (X := X) n) : C(Disk n,X) :=
  ⟨fun z => Topology.RelCWComplex.map n i z.val,
    continuousOn_iff_continuous_domRestrict.mp (Topology.RelCWComplex.continuousOn n i)⟩

abbrev LiftedCell (n : ℕ) := Σ i : Cell (X := X) n, {e : E // p e = characteristic i (diskCenter n)}

noncomputable def cellLift {n : ℕ} (c : LiftedCell (p := p) n) : C(Disk n,E) :=
  (cov.existsUnique_continuousMap_lifts (characteristic c.1) (diskCenter n) c.2.val c.2.property).exists.choose

@[simp] theorem cellLift_center {n : ℕ} (c : LiftedCell (p := p) n) :
    cellLift cov c (diskCenter n) = c.2.val :=
  (cov.existsUnique_continuousMap_lifts (characteristic c.1) (diskCenter n) c.2.val c.2.property).exists.choose_spec.1

theorem cellLift_project {n : ℕ} (c : LiftedCell (p := p) n) (z : Disk n) :
    p (cellLift cov c z) = characteristic c.1 z :=
  congrFun (cov.existsUnique_continuousMap_lifts (characteristic c.1) (diskCenter n) c.2.val c.2.property).exists.choose_spec.2 z

def liftedOpenCell {n : ℕ} (c : LiftedCell (p := p) n) : Set E :=
  cellLift cov c '' {z : Disk n | z.val ∈ ball 0 1}

theorem cellLift_injOn {n : ℕ} (c : LiftedCell (p := p) n) :
    InjOn (cellLift cov c) {z : Disk n | z.val ∈ ball 0 1} := by
  intro z hz w hw he
  apply Subtype.ext
  apply (Topology.RelCWComplex.map n c.1).injOn
  · rwa [Topology.RelCWComplex.source_eq]
  · rwa [Topology.RelCWComplex.source_eq]
  · have h := congrArg p he
    rw [cellLift_project cov c z,cellLift_project cov c w] at h
    exact h

theorem projection_liftedOpenCell {n : ℕ} (c : LiftedCell (p := p) n) :
    p '' liftedOpenCell cov c = Topology.RelCWComplex.openCell n c.1 := by
  ext x
  constructor
  · rintro ⟨e,⟨z,hz,rfl⟩,rfl⟩
    rw [cellLift_project cov c z]
    exact ⟨z.val,hz,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    let z' : Disk n := ⟨z,ball_subset_closedBall hz⟩
    exact ⟨cellLift cov c z',⟨z',hz,rfl⟩,cellLift_project cov c z'⟩

theorem cellLift_unique {n : ℕ} {c d : LiftedCell (p := p) n}
    (hi : c.1 = d.1) (z : Disk n) (hz : cellLift cov c z = cellLift cov d z) : c = d := by
  have he : (cellLift cov c : Disk n → E) = cellLift cov d :=
    cov.eq_of_comp_eq (cellLift cov c).continuous (cellLift cov d).continuous
      (by ext t; simp only [Function.comp_apply,cellLift_project,hi]) z hz
  have hc : c.2.val = d.2.val := by
    simpa only [cellLift_center] using congrFun he (diskCenter n)
  rcases c with ⟨i,e,he⟩
  rcases d with ⟨j,f,hf⟩
  dsimp at hi hc
  cases hi
  cases hc
  rfl

end EilenbergGanea.CWCover

namespace EilenbergGanea.CWCover
open Classical
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ : Set X)] [T2Space X]

abbrev CellDisks (X : Type*) [TopologicalSpace X] [CWComplex (univ : Set X)] :=
  Σ c : (Σ n, RelCWComplex.cell (univ : Set X) n), Disk c.1

def characteristicSum : CellDisks X → X := fun c => characteristic c.1.2 c.2

omit [T2Space X] in
theorem characteristicSum_continuous : Continuous (characteristicSum (X := X)) :=
  continuous_sigma fun c => (characteristic (X := X) c.2).continuous

omit [T2Space X] in
theorem characteristicSum_surjective : Function.Surjective (characteristicSum (X := X)) := by
  intro x
  have hx : x ∈ ⋃ (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n),
      RelCWComplex.closedCell n i := by rw [CWComplex.union]; trivial
  obtain ⟨n,i,z,hz,rfl⟩ := by simpa only [Set.mem_iUnion,RelCWComplex.closedCell,Set.mem_image] using hx
  exact ⟨⟨⟨n,i⟩,⟨z,hz⟩⟩,rfl⟩

/-- The ordinary CW topology is exactly the quotient topology of the disjoint
union of its closed characteristic disks. -/
theorem characteristicSum_quotient : IsQuotientMap (characteristicSum (X := X)) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨characteristicSum_surjective,fun A => ⟨fun h => h.preimage characteristicSum_continuous,?_⟩⟩
  intro hA
  apply (CWComplex.closed (univ : Set X) A (Set.subset_univ A)).mpr
  intro n i
  have hD : IsClosed ((characteristic (X := X) i) ⁻¹' A) :=
    hA.preimage (continuous_sigmaMk (i := (⟨n,i⟩ : Σ n, RelCWComplex.cell (univ : Set X) n)))
  have hcompact : IsCompact ((characteristic (X := X) i) ⁻¹' A) := hD.isCompact
  have he : characteristic i '' (characteristic i ⁻¹' A) = A ∩ RelCWComplex.closedCell n i := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨hz,z.val,z.property,rfl⟩
    · rintro ⟨hx,z,hz,rfl⟩
      exact ⟨⟨z,hz⟩,hx,rfl⟩
  rw [← he]
  exact (hcompact.image (characteristic i).continuous).isClosed

variable {p : E → X} (cov : IsCoveringMap p)

omit [T2Space X] in
/-- Every point over a characteristic disk is hit by exactly one lift of that
disk with the specified base cell. -/
theorem exists_cellLift_through {n : ℕ} (i : Cell (X := X) n) (z : Disk n)
    (e : E) (he : p e = characteristic i z) :
    ∃ c : LiftedCell (p := p) n, c.1 = i ∧ cellLift cov c z = e := by
  obtain ⟨f,hfz,hfp⟩ := (cov.existsUnique_continuousMap_lifts (characteristic i) z e he).exists
  let c : LiftedCell (p := p) n := ⟨i,f (diskCenter n),congrFun hfp (diskCenter n)⟩
  refine ⟨c,rfl,?_⟩
  have hf : (cellLift cov c : Disk n → E) = f :=
    cov.eq_of_comp_eq (cellLift cov c).continuous f.continuous
      (by ext w; rw [Function.comp_apply,cellLift_project cov c w]; exact (congrFun hfp w).symm)
      (diskCenter n) (cellLift_center cov c)
  rw [hf]
  exact hfz


/-- The pulled-back weak topology can be proved before constructing the
lifted CW structure: openness is detected by the actual lifted disks. -/
theorem isOpen_of_cellLift_preimages {A : Set E}
    (hA : ∀ n (c : LiftedCell (p := p) n), IsOpen (cellLift cov c ⁻¹' A)) : IsOpen A := by
  apply isOpen_iff_mem_nhds.mpr
  intro e he
  let s := cov.isLocalHomeomorph.localInverseAt e
  let B : Set X := s.source ∩ s ⁻¹' A
  have hp (x : E) : s.symm x = p x := congrFun (cov.isLocalHomeomorph.localInverseAt_symm e) x
  have hB : IsOpen B := by
    apply characteristicSum_quotient.isOpen_preimage.mp
    rw [isOpen_sigma_iff]
    rintro ⟨n,i⟩
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    change characteristic i z ∈ B at hz
    obtain ⟨c,hci,hcz⟩ := exists_cellLift_through cov i z (s (characteristic i z))
      (cov.isLocalHomeomorph.apply_localInverseAt_of_mem hz.1)
    let W := cellLift cov c ⁻¹' A ∩ cellLift cov c ⁻¹' s.target
    have hW : IsOpen W := (hA n c).inter (s.open_target.preimage (cellLift cov c).continuous)
    have hzW : z ∈ W := by
      change cellLift cov c z ∈ A ∧ cellLift cov c z ∈ s.target
      rw [hcz]
      exact ⟨hz.2,s.map_source hz.1⟩
    apply Filter.mem_of_superset (hW.mem_nhds hzW)
    intro w hw
    have hw₁ : s.symm (cellLift cov c w) = characteristic i w := by
      rw [hp,cellLift_project cov c w,hci]
    have hw₂ : s (characteristic i w) = cellLift cov c w := by
      rw [← hw₁]
      exact s.right_inv hw.2
    change characteristic i w ∈ s.source ∧ s (characteristic i w) ∈ A
    constructor
    · rw [← hw₁]; exact s.map_target hw.2
    · rw [hw₂]; exact hw.1
  have hU : IsOpen (s.target ∩ p ⁻¹' B) := s.open_target.inter (hB.preimage cov.continuous)
  have heU : e ∈ s.target ∩ p ⁻¹' B := by
    refine ⟨cov.isLocalHomeomorph.self_mem_localInverseAt_target,?_,?_⟩
    · exact cov.isLocalHomeomorph.apply_self_mem_localInverseAt_source
    · change s (p e) ∈ A
      simpa only [s,cov.isLocalHomeomorph.localInverseAt_apply_self] using he
  apply Filter.mem_of_superset (hU.mem_nhds heU)
  rintro x ⟨hx,hxB⟩
  have hx' : s (p x) = x := by rw [← hp]; exact s.right_inv hx
  exact hx' ▸ hxB.2

theorem isOpen_iff_cellLift_preimages {A : Set E} :
    IsOpen A ↔ ∀ n (c : LiftedCell (p := p) n), IsOpen (cellLift cov c ⁻¹' A) :=
  ⟨fun h _ c => h.preimage (cellLift cov c).continuous,isOpen_of_cellLift_preimages cov⟩

end EilenbergGanea.CWCover

namespace EilenbergGanea.CWCover
open Classical
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)

/-- Extend the genuine lifted characteristic disk outside its domain only so
that it can be used in Mathlib's ordinary `PartialEquiv` CW convention. -/
def liftedMapFun {n : ℕ} (c : LiftedCell (p := p) n) (z : Fin n → ℝ) : E :=
  if h : z ∈ closedBall 0 1 then cellLift cov c ⟨z,h⟩ else c.2.val

theorem liftedMapFun_disk {n : ℕ} (c : LiftedCell (p := p) n) (z : Disk n) :
    liftedMapFun cov c z.val = cellLift cov c z := by
  simp only [liftedMapFun,dite_eq_left z.property]

theorem liftedMapFun_continuousOn {n : ℕ} (c : LiftedCell (p := p) n) :
    ContinuousOn (liftedMapFun cov c) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert (cellLift cov c).continuous using 1
  ext z
  exact liftedMapFun_disk cov c z

/-- The real inverse chart is obtained by projecting to the ordinary base
chart. It is not chosen by an abstract set-theoretic inverse. -/
def liftedMap {n : ℕ} (c : LiftedCell (p := p) n) : PartialEquiv (Fin n → ℝ) E where
  toFun := liftedMapFun cov c
  invFun := fun e => (RelCWComplex.map n c.1).symm (p e)
  source := ball 0 1
  target := liftedOpenCell cov c
  map_source' := by
    intro z hz
    let z' : Disk n := ⟨z,ball_subset_closedBall hz⟩
    exact ⟨z',hz,(liftedMapFun_disk cov c z').symm⟩
  map_target' := by
    rintro e ⟨z,hz,rfl⟩
    rw [cellLift_project cov c z]
    change (RelCWComplex.map n c.1).symm (RelCWComplex.map n c.1 z.val) ∈ ball 0 1
    rw [(RelCWComplex.map n c.1).left_inv (by rwa [RelCWComplex.source_eq])]
    exact hz
  left_inv' := by
    intro z hz
    let z' : Disk n := ⟨z,ball_subset_closedBall hz⟩
    rw [show liftedMapFun cov c z = cellLift cov c z' from liftedMapFun_disk cov c z']
    rw [cellLift_project cov c z']
    exact (RelCWComplex.map n c.1).left_inv (by rwa [RelCWComplex.source_eq])
  right_inv' := by
    rintro e ⟨z,hz,rfl⟩
    rw [cellLift_project cov c z]
    change liftedMapFun cov c ((RelCWComplex.map n c.1).symm
      (RelCWComplex.map n c.1 z.val)) = _
    rw [(RelCWComplex.map n c.1).left_inv (by rwa [RelCWComplex.source_eq])]
    exact liftedMapFun_disk cov c z

@[simp] theorem liftedMap_source {n : ℕ} (c : LiftedCell (p := p) n) :
    (liftedMap cov c).source = ball 0 1 := rfl

@[simp] theorem liftedMap_target {n : ℕ} (c : LiftedCell (p := p) n) :
    (liftedMap cov c).target = liftedOpenCell cov c := rfl

theorem liftedMap_continuousOn_symm {n : ℕ} (c : LiftedCell (p := p) n) :
    ContinuousOn (liftedMap cov c).symm (liftedMap cov c).target := by
  apply (RelCWComplex.continuousOn_symm n c.1).comp cov.continuous.continuousOn
  intro e he
  rcases he with ⟨z,hz,rfl⟩
  rw [cellLift_project cov c z]
  apply (RelCWComplex.map n c.1).map_source
  rwa [RelCWComplex.source_eq]

theorem liftedOpenCells_disjoint {n m : ℕ} (c : LiftedCell (p := p) n)
    (d : LiftedCell (p := p) m) (hne : (⟨n,c⟩ : Σ k, LiftedCell (p := p) k) ≠ ⟨m,d⟩) :
    Disjoint (liftedOpenCell cov c) (liftedOpenCell cov d) := by
  apply Set.disjoint_left.mpr
  rintro e ⟨z,hz,he⟩ ⟨w,hw,he'⟩
  have hbase : (⟨n,c.1⟩ : Σ k, Cell (X := X) k) = ⟨m,d.1⟩ := by
    by_contra h
    apply Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne h)
      (show p e ∈ RelCWComplex.openCell n c.1 from ?_)
      (show p e ∈ RelCWComplex.openCell m d.1 from ?_)
    · rw [← he,cellLift_project cov c z]; exact ⟨z.val,hz,rfl⟩
    · rw [← he',cellLift_project cov d w]; exact ⟨w.val,hw,rfl⟩
  have hnm : n = m := congrArg Sigma.fst hbase
  subst m
  have hci : c.1 = d.1 := by simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hbase
  have hzw : z = w := by
    apply Subtype.ext
    apply (RelCWComplex.map n c.1).injOn
    · rwa [RelCWComplex.source_eq]
    · rwa [RelCWComplex.source_eq]
    · have h := congrArg p (he.trans he'.symm)
      rw [cellLift_project cov c z,cellLift_project cov d w] at h
      change RelCWComplex.map n c.1 z.val = RelCWComplex.map n d.1 w.val at h
      simpa only [hci] using h
  subst w
  have hcd : c = d := cellLift_unique cov hci z (he.trans he'.symm)
  exact hne (congrArg (fun c => Sigma.mk n c) hcd)

include cov in
omit [CWComplex (univ : Set X)] in
/-- The total space of an ordinary covering of a Hausdorff space is Hausdorff;
no Hausdorff hypothesis is added to the source's definition of K(G,1). -/
theorem t2Space [T2Space X] : T2Space E := by
  refine ⟨fun e f hne => ?_⟩
  by_cases h : p e = p f
  · exact cov.isSeparatedMap e f h hne
  · obtain ⟨U,V,hU,hV,he,hf,hd⟩ := t2_separation h
    exact ⟨p ⁻¹' U,p ⁻¹' V,hU.preimage cov.continuous,hV.preimage cov.continuous,
      he,hf,hd.preimage p⟩

end EilenbergGanea.CWCover


end

end OAI
