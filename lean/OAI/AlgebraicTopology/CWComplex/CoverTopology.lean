import OAI.AlgebraicTopology.CWComplex.CellularPaths
import Mathlib.Topology.Covering.Deck

namespace OAI

noncomputable section

open Classical Set Metric Topology

namespace EilenbergGanea.CWCover
open Classical
open scoped unitInterval
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)

def diskContraction (n : ℕ) : C(unitInterval × Disk n,Disk n) where
  toFun tz := ⟨(1 - (tz.1 : ℝ)) • tz.2.val,
    (convex_closedBall (0 : Fin n → ℝ) 1).smul_mem_of_zero_mem (by simp) tz.2.property
      ⟨sub_nonneg.mpr tz.1.property.2,by linarith [tz.1.property.1]⟩⟩
  continuous_toFun := (by fun_prop : Continuous (fun tz : unitInterval × Disk n =>
    (1 - (tz.1 : ℝ)) • tz.2.val)).subtype_mk _

@[simp] theorem diskContraction_zero (n : ℕ) (z : Disk n) : diskContraction n (0,z) = z := by
  apply Subtype.ext
  simp [diskContraction]

@[simp] theorem diskContraction_one (n : ℕ) (z : Disk n) :
    diskContraction n (1,z) = diskCenter n := by
  apply Subtype.ext
  simp [diskContraction,diskCenter]

abbrev CellPullback {n : ℕ} (i : Cell (X := X) n) :=
  {ez : E × Disk n // p ez.1 = characteristic i ez.2}

def cellPullbackHomotopy {n : ℕ} (i : Cell (X := X) n) :
    C(unitInterval × CellPullback (p := p) i,X) :=
  (characteristic i).comp ((diskContraction n).comp
    ⟨fun tz => (tz.1,tz.2.val.2),by fun_prop⟩)

def cellPullbackStart {n : ℕ} (i : Cell (X := X) n) : C(CellPullback (p := p) i,E) :=
  ⟨fun ez => ez.val.1,by fun_prop⟩

theorem cellPullbackHomotopy_zero {n : ℕ} (i : Cell (X := X) n) (ez : CellPullback (p := p) i) :
    cellPullbackHomotopy i (0,ez) = p (cellPullbackStart i ez) := by
  change characteristic i (diskContraction n (0,ez.val.2)) = p ez.val.1
  rw [diskContraction_zero]
  exact ez.property.symm

def cellEndpoint {n : ℕ} (i : Cell (X := X) n) : C(CellPullback (p := p) i,E) :=
  (cov.liftHomotopy (cellPullbackHomotopy i) (cellPullbackStart i)
    (cellPullbackHomotopy_zero i)).comp ⟨fun ez => (1,ez),by fun_prop⟩

theorem cellEndpoint_project {n : ℕ} (i : Cell (X := X) n)
    (ez : CellPullback (p := p) i) :
    p (cellEndpoint cov i ez) = characteristic i (diskCenter n) := by
  have h := congrFun (cov.liftHomotopy_lifts (cellPullbackHomotopy i)
    (cellPullbackStart i) (cellPullbackHomotopy_zero i)) (1,ez)
  change p (cellEndpoint cov i ez) = characteristic i (diskContraction n (1,ez.val.2)) at h
  simpa only [diskContraction_one] using h

/-- The sheet-coordinate of a point on a lifted characteristic disk is
continuous, including along the disk's nonembedded attaching boundary. -/
def cellSheet {n : ℕ} (i : Cell (X := X) n) :
    C(CellPullback (p := p) i,{e : E // p e = characteristic i (diskCenter n)}) where
  toFun ez := ⟨cellEndpoint cov i ez,cellEndpoint_project cov i ez⟩
  continuous_toFun := (cellEndpoint cov i).continuous.subtype_mk _

/-- Sheet coordinates identify the actual origin of the unique lifted disk. -/
theorem cellSheet_lift {n : ℕ} (c : LiftedCell (p := p) n) (z : Disk n) :
    cellSheet cov c.1 ⟨(cellLift cov c z,z),cellLift_project cov c z⟩ = c.2 := by
  let ez : CellPullback (p := p) c.1 := ⟨(cellLift cov c z,z),cellLift_project cov c z⟩
  let f : C(unitInterval,E) := (cellLift cov c).comp
    ((diskContraction n).comp ⟨fun t => (t,z),by fun_prop⟩)
  let g : C(unitInterval,E) := (cov.liftHomotopy (cellPullbackHomotopy c.1)
    (cellPullbackStart c.1) (cellPullbackHomotopy_zero c.1)).comp
      ⟨fun t => (t,ez),by fun_prop⟩
  have he : (f : unitInterval → E) = g := cov.eq_of_comp_eq f.continuous g.continuous (by
    ext t
    change p (cellLift cov c (diskContraction n (t,z))) =
      p (cov.liftHomotopy (cellPullbackHomotopy c.1) (cellPullbackStart c.1)
        (cellPullbackHomotopy_zero c.1) (t,ez))
    rw [cellLift_project cov c]
    exact (congrFun (cov.liftHomotopy_lifts (cellPullbackHomotopy c.1)
      (cellPullbackStart c.1) (cellPullbackHomotopy_zero c.1)) (t,ez)).symm) 0 (by
    change cellLift cov c (diskContraction n (0,z)) =
      cov.liftHomotopy (cellPullbackHomotopy c.1) (cellPullbackStart c.1)
        (cellPullbackHomotopy_zero c.1) (0,ez)
    rw [diskContraction_zero,cov.liftHomotopy_zero]
    rfl)
  apply Subtype.ext
  change g 1 = c.2.val
  rw [← he]
  change cellLift cov c (diskContraction n (1,z)) = c.2.val
  rw [diskContraction_one,cellLift_center]

end EilenbergGanea.CWCover

namespace EilenbergGanea.CWCover
open Classical
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)
variable [T2Space X]

/-- A compact subset meets only finitely many sheets over each fixed closed
characteristic disk. Boundary points are included; the cell need not be regular. -/
theorem finite_touchingSheets {n : ℕ} (i : Cell (X := X) n) {K : Set E} (hK : IsCompact K) :
    {y : {e : E // p e = characteristic i (diskCenter n)} |
      ∃ z : Disk n, cellLift cov ⟨i,y⟩ z ∈ K}.Finite := by
  let S : Set (CellPullback (p := p) i) := {ez | ez.val.1 ∈ K}
  have hS : IsCompact S := by
    apply Subtype.isCompact_iff.mpr
    have he : Subtype.val '' S = (K ×ˢ Set.univ) ∩
        {ez : E × Disk n | p ez.1 = characteristic i ez.2} := by
      ext ez
      constructor
      · rintro ⟨w,hw,rfl⟩
        exact ⟨⟨hw,trivial⟩,w.property⟩
      · rintro ⟨⟨hK,_⟩,he⟩
        exact ⟨⟨ez,he⟩,hK,rfl⟩
    rw [he]
    exact (hK.prod isCompact_univ).inter_right
      (isClosed_eq (cov.continuous.comp continuous_fst)
        ((characteristic i).continuous.comp continuous_snd))
  let : DiscreteTopology {e : E // p e = characteristic i (diskCenter n)} :=
    (cov (characteristic i (diskCenter n))).1
  have hfin : (cellSheet cov i '' S).Finite :=
    isCompact_iff_finite.mp (hS.image (cellSheet cov i).continuous)
  apply hfin.subset
  rintro y ⟨z,hz⟩
  refine ⟨⟨(cellLift cov ⟨i,y⟩ z,z),cellLift_project cov ⟨i,y⟩ z⟩,hz,?_⟩
  exact cellSheet_lift cov ⟨i,y⟩ z

end EilenbergGanea.CWCover


namespace EilenbergGanea.CWCover
open Classical
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ : Set X)] [T2Space X]
variable {p : E → X} (cov : IsCoveringMap p)

omit [T2Space X] in
@[simp] theorem liftedMap_image_disk {n : ℕ} (c : LiftedCell (p := p) n) :
    liftedMap cov c '' closedBall 0 1 = Set.range (cellLift cov c) := by
  ext e
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨⟨z,hz⟩,(liftedMapFun_disk cov c ⟨z,hz⟩).symm⟩
  · rintro ⟨z,rfl⟩
    exact ⟨z.val,z.property,liftedMapFun_disk cov c z⟩

omit [T2Space X] in
@[simp] theorem liftedMap_image_ball {n : ℕ} (c : LiftedCell (p := p) n) :
    liftedMap cov c '' ball 0 1 = liftedOpenCell cov c :=
  (liftedMap cov c).image_source_eq_target

/-- Compactness of the lifted boundary supplies the actual closure-finiteness
axiom, without assuming a locally finite or finite-cell classifying complex. -/
theorem lifted_mapsTo (n : ℕ) (c : LiftedCell (p := p) n) :
    ∃ J : Π m, Finset (LiftedCell (p := p) m),
      MapsTo (liftedMap cov c) (sphere 0 1)
        (⋃ (m < n) (j ∈ J m), liftedMap cov j '' closedBall 0 1) := by
  let K : Set E := liftedMap cov c '' sphere 0 1
  have hK : IsCompact K := (isCompact_sphere (0 : Fin n → ℝ) 1).image_of_continuousOn
    ((liftedMapFun_continuousOn cov c).mono sphere_subset_closedBall)
  obtain ⟨I,hI⟩ := CWComplex.mapsTo' n c.1
  let J (m : ℕ) : Finset (LiftedCell (p := p) m) := (I m).biUnion (fun i =>
    (finite_touchingSheets cov i hK).toFinset.image (fun y => ⟨i,y⟩))
  refine ⟨J,?_⟩
  intro z hz
  have hb := hI hz
  obtain ⟨m,hm,i,hi,w,hw,he⟩ := by
    simpa only [Set.mem_iUnion,Set.mem_image] using hb
  have he' : p (liftedMap cov c z) = characteristic i ⟨w,hw⟩ := by
    change p (liftedMapFun cov c z) = _
    have hzD : z ∈ closedBall (0 : Fin n → ℝ) 1 :=
      mem_closedBall.mpr (mem_sphere.mp hz).le
    rw [liftedMapFun_disk cov c ⟨z,hzD⟩]
    exact (cellLift_project cov c ⟨z,hzD⟩).trans he.symm
  obtain ⟨d,hdi,hdw⟩ := exists_cellLift_through cov i ⟨w,hw⟩ (liftedMap cov c z) he'
  have hdJ : d ∈ J m := by
    rcases d with ⟨j,y⟩
    dsimp at hdi
    subst j
    apply Finset.mem_biUnion.mpr
    refine ⟨i,hi,Finset.mem_image.mpr ⟨y,?_,rfl⟩⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨⟨w,hw⟩,hdw ▸ ⟨z,hz,rfl⟩⟩
  exact Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨hm,Set.mem_iUnion.mpr
    ⟨d,Set.mem_iUnion.mpr ⟨hdJ,w,hw,(liftedMapFun_disk cov d ⟨w,hw⟩).trans hdw⟩⟩⟩⟩

/-- Every ordinary CW structure lifts through any covering, with exactly the
actual sheets times the base cells as cell indices. -/
@[instance_reducible] def cwComplex : CWComplex (univ : Set E) where
  cell := LiftedCell (p := p)
  map := fun _ c => liftedMap cov c
  source_eq := fun _ _ => rfl
  continuousOn := fun _ c => liftedMapFun_continuousOn cov c
  continuousOn_symm := fun _ c => liftedMap_continuousOn_symm cov c
  pairwiseDisjoint' := by
    intro a _ b _ hab
    simpa only [liftedMap_image_ball] using liftedOpenCells_disjoint cov a.2 b.2 hab
  mapsTo' := lifted_mapsTo cov
  closed' := by
    intro A _ hA
    apply isOpen_compl_iff.mp
    apply isOpen_of_cellLift_preimages cov
    intro n c
    have h := (hA n c).preimage (cellLift cov c).continuous
    have he : cellLift cov c ⁻¹' (A ∩ liftedMap cov c '' closedBall 0 1) =
        cellLift cov c ⁻¹' A := by
      rw [liftedMap_image_disk,Set.preimage_inter]
      simp only [Set.preimage_range,Set.inter_univ]
    rw [he] at h
    exact h.isOpen_compl
  union' := by
    apply Set.eq_univ_of_forall
    intro e
    obtain ⟨⟨⟨n,i⟩,z⟩,hz⟩ := characteristicSum_surjective (p e)
    obtain ⟨c,_,hc⟩ := exists_cellLift_through cov i z e hz.symm
    exact Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨c,z.val,z.property,
      (liftedMapFun_disk cov c z).trans hc⟩⟩

end EilenbergGanea.CWCover


namespace EilenbergGanea.CWCover
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ : Set X)] [T2Space X]
variable {p : E → X} (cov : IsCoveringMap p)

/-- Covering lifts preserve the literal absence of cells in each dimension. -/
theorem cwComplex_cell_isEmpty (n : ℕ) [IsEmpty (Topology.CWComplex.cell (univ : Set X) n)] :
    @IsEmpty (@Topology.CWComplex.cell E _ (univ : Set E) (cwComplex cov) n) := by
  change IsEmpty (LiftedCell (p := p) n)
  infer_instance

/-- No cardinality restriction is made in this dimension comparison. -/
theorem cwComplex_dimension_le (d : ℕ)
    (h : ∀ n, d < n → IsEmpty (Topology.CWComplex.cell (univ : Set X) n)) :
    ∀ n, d < n → @IsEmpty (@Topology.CWComplex.cell E _ (univ : Set E) (cwComplex cov) n) := by
  intro n hn
  let := h n hn
  exact cwComplex_cell_isEmpty cov n

end EilenbergGanea.CWCover


open Set Topology
open scoped unitInterval
namespace EilenbergGanea.CoverTopology
variable {A E X : Type*} [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace X]
variable {p : E → X} (cov : IsCoveringMap p)

include cov

/-- A contractible domain admits based covering lifts without a separate
local path-connectivity hypothesis: lift a contraction and reverse its base path. -/
theorem existsUnique_lift_contractible [ContractibleSpace A]
    (f : C(A,X)) (a₀ : A) (e₀ : E) (he : p e₀ = f a₀) :
    ∃! g : C(A,E), g a₀ = e₀ ∧ p ∘ g = f := by
  obtain ⟨a,⟨H⟩⟩ := id_nullhomotopic A
  let β : C(unitInterval,X) := f.comp (H.evalAt a₀).toContinuousMap
  have hβ : β 0 = p e₀ := by
    change f ((H.evalAt a₀) 0) = p e₀
    rw [Path.source]
    exact he.symm
  let β' := cov.liftPath β e₀ hβ
  let e := β' 1
  have he' : p e = f a := by
    have h := congrFun (cov.liftPath_lifts β e₀ hβ) 1
    change p e = β 1 at h
    change p e = f ((H.evalAt a₀) 1) at h
    rw [(H.evalAt a₀).target] at h
    exact h
  let B : C(unitInterval × A,X) := f.comp H.symm.toContinuousMap
  have hB : ∀ z, B (0,z) = p ((ContinuousMap.const A e) z) := by
    intro z
    change f (H.symm (0,z)) = p e
    simpa only [ContinuousMap.Homotopy.apply_zero,ContinuousMap.const_apply] using he'.symm
  let L := cov.liftHomotopy B (ContinuousMap.const A e) hB
  let g : C(A,E) := L.comp ⟨fun z => (1,z),by fun_prop⟩
  have hg : p ∘ g = f := by
    ext z
    change p (g z) = f z
    have h := congrFun (cov.liftHomotopy_lifts B (ContinuousMap.const A e) hB) (1,z)
    change p (g z) = f (H.symm (1,z)) at h
    simpa only [ContinuousMap.Homotopy.apply_one,ContinuousMap.id_apply] using h
  have hbase : g a₀ = e₀ := by
    let k : C(unitInterval,E) := L.comp ⟨fun t => (t,a₀),by fun_prop⟩
    let k' : C(unitInterval,E) := β'.comp ⟨unitInterval.symm,unitInterval.symmHomeomorph.continuous⟩
    have hk : (k : unitInterval → E) = k' := cov.eq_of_comp_eq k.continuous k'.continuous (by
      ext t
      change p (L (t,a₀)) = p (β' (unitInterval.symm t))
      rw [show p (L (t,a₀)) = B (t,a₀) from
        congrFun (cov.liftHomotopy_lifts B (ContinuousMap.const A e) hB) (t,a₀)]
      rw [show p (β' (unitInterval.symm t)) = β (unitInterval.symm t) from
        congrFun (cov.liftPath_lifts β e₀ hβ) (unitInterval.symm t)]
      rfl) 0 (by
        change L (0,a₀) = β' (unitInterval.symm 0)
        rw [unitInterval.symm_zero]
        exact cov.liftHomotopy_zero B (ContinuousMap.const A e) hB a₀)
    have h := congrFun hk 1
    change g a₀ = β' (unitInterval.symm 1) at h
    rw [unitInterval.symm_one] at h
    exact h.trans (cov.liftPath_zero β e₀ hβ)
  refine ⟨g,⟨hbase,hg⟩,?_⟩
  intro k hk
  apply DFunLike.ext'
  exact cov.eq_of_comp_eq k.continuous g.continuous (hk.2.trans hg.symm) a₀
    (hk.1.trans hbase.symm)

end EilenbergGanea.CoverTopology

namespace EilenbergGanea.CoverTopology
variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
variable (p : E → X)

/-- The actual group of self-homeomorphisms over a covering projection. -/
def deckGroup : Subgroup (E ≃ₜ E) where
  carrier := {d | ∀ e, p (d e) = p e}
  one_mem' := fun _ => rfl
  mul_mem' := fun {d e} hd he x => (hd (e x)).trans (he x)
  inv_mem' := by
    intro d hd e
    simpa only [Homeomorph.inv_apply,Homeomorph.apply_symm_apply] using (hd (d.symm e)).symm

instance deckMulAction : MulAction (deckGroup p) E where
  smul d e := d.val e
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

omit [TopologicalSpace X] in
@[simp] theorem deck_smul (d : deckGroup p) (e : E) : d • e = d.val e := rfl
omit [TopologicalSpace X] in
theorem deck_project (d : deckGroup p) (e : E) : p (d • e) = p e := d.property e

instance deckContinuous : ContinuousConstSMul (deckGroup p) E where
  continuous_const_smul d := d.val.continuous

variable {p} (cov : IsCoveringMap p)
include cov

theorem deck_ext [PreconnectedSpace E] {d e : deckGroup p} (x : E)
    (hx : d • x = e • x) : d = e := by
  apply Subtype.ext
  apply Homeomorph.ext
  exact congrFun (cov.eq_of_comp_eq d.val.continuous e.val.continuous
    (by ext z; exact (d.property z).trans (e.property z).symm) x hx)

/-- Every two points in a fiber of a contractible covering are related by a
unique genuine deck homeomorphism. No local-connectivity hypothesis is added. -/
theorem existsUnique_deck [ContractibleSpace E] (x y : E) (hxy : p x = p y) :
    ∃! d : deckGroup p, d • x = y := by
  let P : C(E,X) := ⟨p,cov.continuous⟩
  obtain ⟨f,hf,_⟩ := existsUnique_lift_contractible cov P x y hxy.symm
  obtain ⟨g,hg,_⟩ := existsUnique_lift_contractible cov P y x hxy
  have hgf : g ∘ f = id := cov.eq_of_comp_eq
    (g.continuous.comp f.continuous) continuous_id (by
      ext z
      change p (g (f z)) = p z
      exact (congrFun hg.2 (f z)).trans (congrFun hf.2 z)) x (by
        change g (f x) = x
        rw [hf.1,hg.1])
  have hfg : f ∘ g = id := cov.eq_of_comp_eq
    (f.continuous.comp g.continuous) continuous_id (by
      ext z
      change p (f (g z)) = p z
      exact (congrFun hf.2 (g z)).trans (congrFun hg.2 z)) y (by
        change f (g y) = y
        rw [hg.1,hf.1])
  let d : deckGroup p := ⟨{
      toFun := f
      invFun := g
      left_inv := fun z => congrFun hgf z
      right_inv := fun z => congrFun hfg z
      continuous_toFun := f.continuous
      continuous_invFun := g.continuous }, fun z => congrFun hf.2 z⟩
  refine ⟨d,hf.1,?_⟩
  intro d' hd'
  exact deck_ext cov x (hd'.trans hf.1.symm)

/-- A surjective contractible covering is literally a quotient covering by its
deck group, with a free properly discontinuous action. -/
theorem isQuotientCoveringMap_deck [ContractibleSpace E] (hs : Function.Surjective p) :
    IsQuotientCoveringMap p (deckGroup p) where
  __ := cov.isQuotientMap hs
  __ := deckContinuous p
  apply_eq_iff_mem_orbit := by
    intro x y
    constructor
    · intro h
      obtain ⟨d,hd,_⟩ := existsUnique_deck cov y x h.symm
      exact ⟨d,hd⟩
    · rintro ⟨d,rfl⟩
      exact deck_project p d y
  disjoint := by
    intro x
    obtain ⟨U,hU,hxU,hinj⟩ := cov.isLocalHomeomorph.isLocallyInjective x
    refine ⟨U,hU.mem_nhds hxU,?_⟩
    rintro d ⟨z,⟨y,hyU,rfl⟩,hzU⟩
    apply deck_ext cov y
    exact hinj hzU hyU (deck_project p d y)

end EilenbergGanea.CoverTopology

namespace EilenbergGanea.CWCover
open CoverTopology
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)

/-- Deck transformations act on the actual lifted cells through their centers. -/
instance liftedCellAction (n : ℕ) : MulAction (deckGroup p) (LiftedCell (p := p) n) where
  smul d c := ⟨c.1,⟨d • c.2.val,(deck_project p d c.2.val).trans c.2.property⟩⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem liftedCell_smul_base {n : ℕ} (d : deckGroup p) (c : LiftedCell (p := p) n) :
    (d • c).1 = c.1 := rfl

@[simp] theorem liftedCell_smul_center {n : ℕ} (d : deckGroup p) (c : LiftedCell (p := p) n) :
    (d • c).2.val = d • c.2.val := rfl

/-- Compatibility includes the full closed disk, not only cell interiors. -/
theorem cellLift_smul {n : ℕ} (d : deckGroup p) (c : LiftedCell (p := p) n) (z : Disk n) :
    cellLift cov (d • c) z = d • cellLift cov c z := by
  apply congrFun (cov.eq_of_comp_eq (cellLift cov (d • c)).continuous
    (d.val.continuous.comp (cellLift cov c).continuous) ?_ (diskCenter n) ?_) z
  · ext w
    change p (cellLift cov (d • c) w) = p (d • cellLift cov c w)
    rw [cellLift_project cov (d • c) w,deck_project p d (cellLift cov c w),
      cellLift_project cov c w]
    rfl
  · change cellLift cov (d • c) (diskCenter n) = d • cellLift cov c (diskCenter n)
    rw [cellLift_center,cellLift_center,liftedCell_smul_center]

variable [ContractibleSpace E] (hs : Function.Surjective p)

/-- An arbitrary choice of one disk lift per base cell; no finiteness is needed. -/
def chosenCell {n : ℕ} (i : Cell (X := X) n) : LiftedCell (p := p) n :=
  ⟨i,⟨(hs (characteristic i (diskCenter n))).choose,
    (hs (characteristic i (diskCenter n))).choose_spec⟩⟩

/-- Every lifted ordinary cell is uniquely a deck translate of the chosen lift
of its base cell. This is the actual free-module coefficient indexing. -/
def cellOrbitEquiv (n : ℕ) : LiftedCell (p := p) n ≃ Cell (X := X) n × deckGroup p where
  toFun c := (c.1,(isQuotientCoveringMap_deck cov hs).fiberEquivGroup
    (chosenCell hs c.1).2 c.2)
  invFun j := j.2 • chosenCell hs j.1
  left_inv := by
    intro c
    change (⟨c.1, _⟩ : LiftedCell (p := p) n) = c
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact (isQuotientCoveringMap_deck cov hs).fiberEquivGroup_smul_self
        (chosenCell hs c.1).2
  right_inv := by
    rintro ⟨i,d⟩
    change (i, _) = (i,d)
    apply Prod.ext
    · rfl
    · exact ((isQuotientCoveringMap_deck cov hs).fiberEquivGroup_eq_iff _ _ _).mpr rfl

@[simp] theorem cellOrbitEquiv_symm {n : ℕ} (i : Cell (X := X) n) (d : deckGroup p) :
    (cellOrbitEquiv cov hs n).symm (i,d) = d • chosenCell hs i := rfl

end EilenbergGanea.CWCover


namespace EilenbergGanea.PathTransport
open CubicalSingular Set
variable {X : Type*} [TopologicalSpace X]
local instance : ContractibleSpace I := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩

/-- A finite-mesh local-to-global principle for actual paths, preserving their
homotopy classes rather than only abelianized chains. -/
theorem path_cover_induction (U : Set (Set X)) (hU : ∀ V ∈ U, IsOpen V)
    (hc : ⋃₀ U = univ) (P : ∀ {x y : X}, Path x y → Prop)
    (hhom : ∀ {x y} {p s : Path x y}, Path.Homotopic p s → P s → P p)
    (htrans : ∀ {x y z} (p : Path x y) (s : Path y z), P p → P s → P (p.trans s))
    (hsmall : ∀ {x y} (p : Path x y), p.toContinuousMap ∈ CubicalMesh.small U → P p)
    {x y} (p : Path x y) : P p := by
  have step : ∀ n {x y} (p : Path x y), Local.Good₁ (U:=U) n p.toContinuousMap → P p := by
    intro n
    induction n with
    | zero => intro x y p hp; exact hsmall p (Local.good₁_zero hp)
    | succ n ih =>
      intro x y p hp
      let p₀ : Path x (p (half true 0)) := (halfPath₀.map p.continuous).cast p.source.symm rfl
      let p₁ : Path (p (half true 0)) y := (halfPath₁.map p.continuous).cast rfl p.target.symm
      have h₀ : P p₀ := ih p₀ (Local.good₁_cut hp false)
      have h₁ : P p₁ := ih p₁ (Local.good₁_cut hp true)
      have hh := ((SimplyConnectedSpace.paths_homotopic Path.id (halfPath₀.trans halfPath₁)).map p.toContinuousMap).pathCast p.source.symm p.target.symm
      have hid : (Path.id.map p.continuous).cast p.source.symm p.target.symm = p := Path.ext (by rfl)
      rw [hid] at hh
      exact hhom (by simpa only [Path.map_trans,Path.cast_trans] using hh) (htrans p₀ p₁ h₀ h₁)
  obtain ⟨n,hn⟩ := (Local.good₁_eventually hU hc p.toContinuousMap).exists
  exact step n p hn

end EilenbergGanea.PathTransport


namespace EilenbergGanea.PathTransport
open Set CubicalSingular
variable {X : Type*} [TopologicalSpace X]

def subpath (W : Set X) {x y : X} (p : Path x y) (hp : Set.range p ⊆ W) :
    Path (⟨x,hp ⟨0,p.source⟩⟩ : W) ⟨y,hp ⟨1,p.target⟩⟩ where
  toFun t := ⟨p t,hp ⟨t,rfl⟩⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

structure Compression (U V : Set X) where
  select : X → U
  bridge : ∀ x, Path x (select x).val
  left : ∀ x, x ∈ U → Set.range (bridge x) ⊆ U
  right : ∀ x, x ∈ V → Set.range (bridge x) ⊆ V
  join : ∀ x y : (U ∩ V : Set X), Nonempty (Path (⟨x.val,x.property.2⟩ : V) ⟨y.val,y.property.2⟩) → Nonempty (Path x y)

namespace Compression
variable {U V : Set X} (c : Compression U V)

def Represents {x y : X} (p : Path x y) : Prop :=
  ∃ s : Path (c.select x) (c.select y),
    (asClass (c.bridge x)).symm.trans ((asClass p).trans (asClass (c.bridge y))) = asClass (s.map continuous_subtype_val)

theorem represents_homotopic {x y : X} {p t : Path x y} (h : p.Homotopic t)
    (ht : c.Represents t) : c.Represents p := by
  obtain ⟨s,hs⟩ := ht
  have he : asClass p = asClass t := Quotient.sound h
  exact ⟨s,by simpa only [he] using hs⟩

theorem represents_trans {x y z : X} (p : Path x y) (t : Path y z)
    (hp : c.Represents p) (ht : c.Represents t) : c.Represents (p.trans t) := by
  obtain ⟨s,hs⟩ := hp
  obtain ⟨v,hv⟩ := ht
  refine ⟨s.trans v,?_⟩
  simp only [Path.map_trans,asClass,Path.Homotopic.Quotient.mk_trans] at hs hv ⊢
  rw [← hs,← hv]
  simp only [Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc (asClass (c.bridge y)),Path.Homotopic.Quotient.trans_symm,Path.Homotopic.Quotient.refl_trans]

theorem represents_left {x y : X} (p : Path x y) (hp : Set.range p ⊆ U) : c.Represents p := by
  have hx := hp ⟨0,p.source⟩
  have hy := hp ⟨1,p.target⟩
  let s := (subpath U (c.bridge x) (c.left x hx)).symm.trans
    ((subpath U p hp).trans (subpath U (c.bridge y) (c.left y hy)))
  refine ⟨s,?_⟩
  have he : s.map continuous_subtype_val = (c.bridge x).symm.trans (p.trans (c.bridge y)) := by
    ext t
    simp only [s,Path.map_trans,Path.trans_apply,Path.symm_apply,subpath]
    split_ifs <;> rfl
  rw [he]
  simp only [asClass,Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm]

theorem represents_right (hV : ForestCover.ThinPaths V) {x y : X} (p : Path x y)
    (hp : Set.range p ⊆ V) : c.Represents p := by
  have hx := hp ⟨0,p.source⟩
  have hy := hp ⟨1,p.target⟩
  have hsx : (c.select x).val ∈ V := c.right x hx ⟨1,(c.bridge x).target⟩
  have hsy : (c.select y).val ∈ V := c.right y hy ⟨1,(c.bridge y).target⟩
  let bx := subpath V (c.bridge x) (c.right x hx)
  let by' := subpath V (c.bridge y) (c.right y hy)
  let pv := subpath V p hp
  let xv : (U ∩ V : Set X) := ⟨(c.select x).val,(c.select x).property,hsx⟩
  let yv : (U ∩ V : Set X) := ⟨(c.select y).val,(c.select y).property,hsy⟩
  obtain ⟨s⟩ := c.join xv yv ⟨bx.symm.trans (pv.trans by')⟩
  let j : C((U ∩ V : Set X),V) := ⟨fun z => ⟨z.val,z.property.2⟩,continuous_subtype_val.subtype_mk _⟩
  let i : C((U ∩ V : Set X),U) := ⟨fun z => ⟨z.val,z.property.1⟩,continuous_subtype_val.subtype_mk _⟩
  let inc : C(V,X) := ⟨Subtype.val,continuous_subtype_val⟩
  have hh := (hV _ _ (bx.symm.trans (pv.trans by')) (s.map j.continuous)).map inc
  refine ⟨s.map i.continuous,?_⟩
  have he₁ : (bx.symm.trans (pv.trans by')).map inc.continuous =
      (c.bridge x).symm.trans (p.trans (c.bridge y)) := by
    rw [Path.map_trans,Path.map_trans,← Path.map_symm]
    rfl
  have he₂ : (s.map j.continuous).map inc.continuous = (s.map i.continuous).map continuous_subtype_val := Path.ext (by rfl)
  rw [he₁,he₂] at hh
  have he : asClass ((c.bridge x).symm.trans (p.trans (c.bridge y))) = asClass ((s.map i.continuous).map continuous_subtype_val) := Quotient.sound hh
  simpa only [asClass,Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm] using he

/-- Removing the centers of attached cells of dimension at least two does not
lose any path class, provided the actual punctured-cell components are joined. -/
theorem represents (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ)
    (hthin : ForestCover.ThinPaths V) {x y : X} (p : Path x y) : c.Represents p :=
  path_cover_induction {U,V} (TwoPotential.cover_open hU hV) (TwoPotential.cover_univ hc)
    (fun p => c.Represents p) (fun h hp => c.represents_homotopic h hp)
    (fun p s hp hs => c.represents_trans p s hp hs) (by
      intro x y p hp
      rcases TwoPotential.small_either p.toContinuousMap hp with h | h
      · exact c.represents_left p h
      · exact c.represents_right hthin p h) p

end Compression
end EilenbergGanea.PathTransport

namespace EilenbergGanea.PathTransport.Compression
open Set CubicalSingular
variable {X : Type*} [TopologicalSpace X] {U V : Set X} (c : Compression U V)
variable (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ) (hthin : ForestCover.ThinPaths V)

include c hU hV hc hthin in
theorem pathConnected [PathConnectedSpace X] : PathConnectedSpace U where
  nonempty := ⟨c.select (Classical.choice inferInstance)⟩
  joined x y := by
    let p := (PathConnectedSpace.joined x.val y.val).somePath
    obtain ⟨s,_⟩ := c.represents hU hV hc hthin p
    let bx := subpath U (c.bridge x.val) (c.left x.val x.property)
    let by' := subpath U (c.bridge y.val) (c.left y.val y.property)
    exact ⟨bx.trans (s.trans by'.symm)⟩

include c hU hV hc hthin in
/-- Actual surjectivity on based fundamental groups, not only on H1. -/
theorem fundamental_surjective (r : U) :
    Function.Surjective (FundamentalGroup.map (⟨Subtype.val,continuous_subtype_val⟩ : C(U,X)) r) := by
  intro g
  obtain ⟨p,rfl⟩ := Quotient.exists_rep g
  obtain ⟨s,hs⟩ := c.represents hU hV hc hthin p
  let b := subpath U (c.bridge r.val) (c.left r.val r.property)
  let t : Path r r := b.trans (s.trans b.symm)
  refine ⟨asClass t,?_⟩
  change asClass (t.map continuous_subtype_val) = asClass p
  have he : t.map continuous_subtype_val = (c.bridge r.val).trans ((s.map continuous_subtype_val).trans (c.bridge r.val).symm) := by
    rw [Path.map_trans,Path.map_trans,← Path.map_symm]
    rfl
  rw [he]
  simp only [asClass,Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm] at hs ⊢
  rw [← hs]
  simp only [Path.Homotopic.Quotient.trans_assoc]
  change (asClass (c.bridge r.val)).trans
    ((asClass (c.bridge r.val)).symm.trans
      ((asClass p).trans ((asClass (c.bridge r.val)).trans (asClass (c.bridge r.val)).symm))) = asClass p
  simp only [Path.Homotopic.Quotient.trans_symm]
  exact (congrArg (fun z : PQ r.val r.val => (asClass (c.bridge r.val)).trans
    ((asClass (c.bridge r.val)).symm.trans z))
      (Path.Homotopic.Quotient.trans_refl (asClass p))).trans
        ((Path.Homotopic.Quotient.trans_assoc _ _ _).symm.trans
          ((congrArg (fun z => z.trans (asClass p))
            (Path.Homotopic.Quotient.trans_symm (asClass (c.bridge r.val)))).trans
              (Path.Homotopic.Quotient.refl_trans (asClass p))))

end EilenbergGanea.PathTransport.Compression


namespace EilenbergGanea.CWCollar.Attachment
open Set Topology CWCover PathTransport CubicalSingular
variable {X J : Type*} [TopologicalSpace X] (a : Attachment X J 2)

noncomputable def annulusPoint : Annulus 2 := Classical.choice inferInstance

theorem annulus_inner (z : Σ _ : J, Annulus 2) :
    (a.annulusHomeomorph z).val = (a.innerHomeomorph ⟨z.1,z.2.val⟩).val := rfl

noncomputable def compressionChoice (x : X) :
    Σ y : a.outer, {p : Path x y.val //
      (x ∈ a.outer → Set.range p ⊆ a.outer) ∧ (x ∈ a.inner → Set.range p ⊆ a.inner)} := by
  by_cases hx : x ∈ a.outer
  · exact ⟨⟨x,hx⟩,Path.refl x,fun _ z hz => by obtain ⟨t,rfl⟩ := hz; exact hx,
      fun hv z hz => by obtain ⟨t,rfl⟩ := hz; exact hv⟩
  · have hv : x ∈ a.inner := by
      have he : x ∈ a.outer ∪ a.inner := by rw [a.outer_union_inner]; trivial
      exact he.resolve_left hx
    let z := a.innerHomeomorph.symm ⟨x,hv⟩
    let w : (a.outer ∩ a.inner : Set X) := a.annulusHomeomorph ⟨z.1,annulusPoint⟩
    let f : C(OpenDisk 2,X) := ⟨fun t => (a.innerHomeomorph ⟨z.1,t⟩).val,
      continuous_subtype_val.comp (a.innerHomeomorph.continuous.comp continuous_sigmaMk)⟩
    have hs : x = f z.2 := congrArg Subtype.val (a.innerHomeomorph.apply_symm_apply ⟨x,hv⟩).symm
    let p : Path x w.val := (((PathConnectedSpace.joined z.2 annulusPoint.val).somePath).map f.continuous).cast hs rfl
    refine ⟨⟨w.val,w.property.1⟩,p,fun ho => False.elim (hx ho),?_⟩
    intro _ y hy
    obtain ⟨t,rfl⟩ := hy
    exact (a.innerHomeomorph ⟨z.1,(PathConnectedSpace.joined z.2 annulusPoint.val).somePath t⟩).property

/-- The punctured-disk overlap is connected inside each open disk, so any
inner path joining overlap points can be replaced there. -/
theorem overlap_join (x y : (a.outer ∩ a.inner : Set X))
    (hp : Nonempty (Path (⟨x.val,x.property.2⟩ : a.inner) ⟨y.val,y.property.2⟩)) : Nonempty (Path x y) := by
  obtain ⟨p⟩ := hp
  let u := a.annulusHomeomorph.symm x
  let v := a.annulusHomeomorph.symm y
  let : TopologicalSpace J := ⊥
  let : DiscreteTopology J := ⟨rfl⟩
  let f : C(a.inner,J) := ⟨fun z => (a.innerHomeomorph.symm z).1,
    (continuous_sigma (fun _ => continuous_const)).comp a.innerHomeomorph.symm.continuous⟩
  have he₀ : f ⟨x.val,x.property.2⟩ = u.1 := by
    have h := congrArg (fun z : a.inner => (a.innerHomeomorph.symm z).1)
      (show (⟨x.val,x.property.2⟩ : a.inner) = a.innerHomeomorph ⟨u.1,u.2.val⟩ from
        Subtype.ext ((congrArg Subtype.val (a.annulusHomeomorph.apply_symm_apply x)).symm.trans (a.annulus_inner u)))
    simpa only [f,ContinuousMap.coe_mk,Homeomorph.symm_apply_apply] using h
  have he₁ : f ⟨y.val,y.property.2⟩ = v.1 := by
    have h := congrArg (fun z : a.inner => (a.innerHomeomorph.symm z).1)
      (show (⟨y.val,y.property.2⟩ : a.inner) = a.innerHomeomorph ⟨v.1,v.2.val⟩ from
        Subtype.ext ((congrArg Subtype.val (a.annulusHomeomorph.apply_symm_apply y)).symm.trans (a.annulus_inner v)))
    simpa only [f,ContinuousMap.coe_mk,Homeomorph.symm_apply_apply] using h
  have he : u.1 = v.1 := by
    have hh : f (p 0) = f (p 1) := (@inferInstance (PreconnectedSpace I)).constant (f.continuous.comp p.continuous)
    simpa only [p.source,p.target,he₀,he₁] using hh
  have hj : Joined u v := by
    obtain ⟨j,u⟩ := u
    obtain ⟨k,v⟩ := v
    dsimp only at he
    subst k
    exact (PathConnectedSpace.joined u v).map continuous_sigmaMk
  exact ⟨(hj.somePath.map a.annulusHomeomorph.continuous).cast
    (a.annulusHomeomorph.apply_symm_apply x).symm (a.annulusHomeomorph.apply_symm_apply y).symm⟩

noncomputable def compression : PathTransport.Compression a.outer a.inner where
  select x := (a.compressionChoice x).1
  bridge x := (a.compressionChoice x).2.val
  left x := (a.compressionChoice x).2.property.1
  right x := (a.compressionChoice x).2.property.2
  join := a.overlap_join

end EilenbergGanea.CWCollar.Attachment


namespace EilenbergGanea.CWCollar
open Set Metric Topology CWCover
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [T2Space X] [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)


theorem lifted_characteristic {n : ℕ} (c : LiftedCell (p:=p) n) (z : Disk n) :
    let := CWCover.cwComplex cov
    characteristic (X:=E) c z = cellLift cov c z := liftedMapFun_disk cov c z

variable {m : ℕ} (hd : ∀ k, m < k → IsEmpty (Cell (X:=X) k))

abbrev baseAttachment := actualAttachment m hd
def liftedAttachment : Attachment E (LiftedCell (p:=p) m) m := by
  let := CWCover.t2Space cov
  let := CWCover.cwComplex cov
  exact actualAttachment m (cwComplex_dimension_le cov m hd)

/-- The radial coordinate is literally preserved by projection, including
all lower-skeleton points, not merely open-cell interiors. -/
theorem lifted_radius (e : E) :
    (liftedAttachment cov hd).radius e = (baseAttachment hd).radius (p e) := by
  let := CWCover.t2Space cov
  let := CWCover.cwComplex cov
  obtain ⟨⟨⟨k,c⟩,z⟩,rfl⟩ := characteristicSum_surjective (X:=E) e
  change (liftedAttachment cov hd).radius (characteristic c z) =
    (baseAttachment hd).radius (p (characteristic c z))
  by_cases hk : k < m
  · rw [(liftedAttachment cov hd).radius_lower
      ⟨characteristic c z,characteristic_mem_lower hk c z⟩]
    rw [lifted_characteristic cov c z,cellLift_project cov c z]
    exact ((baseAttachment hd).radius_lower ⟨characteristic c.1 z,characteristic_mem_lower hk c.1 z⟩).symm
  · have hkm : k = m := by
      by_contra he
      have := hd k (by omega)
      exact isEmptyElim c.1
    subst k
    change (liftedAttachment cov hd).radius ((liftedAttachment cov hd).chart c z) = _
    rw [(liftedAttachment cov hd).radius_chart]
    rw [lifted_characteristic cov c z,cellLift_project cov c z]
    exact ((baseAttachment hd).radius_chart c.1 z).symm

@[simp] theorem lifted_outer : (liftedAttachment cov hd).outer = p ⁻¹' (baseAttachment hd).outer := by
  ext e
  change 0 < (liftedAttachment cov hd).radius e ↔ 0 < (baseAttachment hd).radius (p e)
  rw [lifted_radius cov hd e]
@[simp] theorem lifted_inner : (liftedAttachment cov hd).inner = p ⁻¹' (baseAttachment hd).inner := by
  ext e
  change (liftedAttachment cov hd).radius e < 1 ↔ (baseAttachment hd).radius (p e) < 1
  rw [lifted_radius cov hd e]

def liftedOuterHomeomorph : (liftedAttachment cov hd).outer ≃ₜ p ⁻¹' (baseAttachment hd).outer :=
  Homeomorph.setCongr (lifted_outer cov hd)

def outerProjection : C((liftedAttachment cov hd).outer,(baseAttachment hd).outer) :=
  (⟨(baseAttachment hd).outer.restrictPreimage p,
    (cov.continuous.comp continuous_subtype_val).subtype_mk _⟩ :
    C(p ⁻¹' (baseAttachment hd).outer,(baseAttachment hd).outer)).comp
      (liftedOuterHomeomorph cov hd : C(_, _))

theorem outerProjection_cover : IsCoveringMap (outerProjection cov hd) := by
  exact (cov.restrictPreimage (baseAttachment hd).outer).comp_homeomorph
    (liftedOuterHomeomorph cov hd)

/-- The same parametrized annulus projects to the base annulus. -/
theorem lifted_annulus (c : LiftedCell (p:=p) m) (z : Annulus m) :
    p ((liftedAttachment cov hd).annulusHomeomorph ⟨c,z⟩).val =
      ((baseAttachment hd).annulusHomeomorph ⟨c.1,z⟩).val := by
  let := CWCover.cwComplex cov
  change p (characteristic c z.val.val) = characteristic c.1 z.val.val
  rw [lifted_characteristic cov,cellLift_project cov]

end EilenbergGanea.CWCollar



open Classical Set
namespace EilenbergGanea.CoverKernel
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable {p : E → X} (cov : IsCoveringMap p) (U : Set X)

def projection : C(p ⁻¹' U,U) := ⟨U.restrictPreimage p,(cov.continuous.comp continuous_subtype_val).subtype_mk _⟩
def inclusion : C(U,X) := ⟨Subtype.val,continuous_subtype_val⟩
def totalInclusion : C(p ⁻¹' U,E) := ⟨Subtype.val,continuous_subtype_val⟩

theorem lift_loop_closed {e : E} (γ : Path (p e) (p e))
    (h : γ.Homotopic (Path.refl (p e))) : cov.liftPath γ e γ.source 1 = e := by
  have he := cov.liftPath_apply_one_eq_of_homotopicRel h e γ.source rfl
  change cov.liftPath γ e γ.source 1 = cov.liftPath (ContinuousMap.const _ (p e)) e rfl 1 at he
  rw [cov.liftPath_const (e := e) rfl] at he
  exact he

variable (e : p ⁻¹' U)

def toBase : (FundamentalGroup (p ⁻¹' U) e)ᵐᵒᵖ →* (FundamentalGroup U (projection cov U e))ᵐᵒᵖ :=
  (FundamentalGroup.map (projection cov U) e).op

def toTotal : (FundamentalGroup U (projection cov U e))ᵐᵒᵖ →* (FundamentalGroup X (p e.val))ᵐᵒᵖ :=
  (FundamentalGroup.map (inclusion U) (projection cov U e)).op

theorem toBase_injective : Function.Injective (toBase cov U e) := by
  intro a b he
  apply MulOpposite.unop_injective
  exact (cov.restrictPreimage U).injective_path_homotopic_map e e (congrArg MulOpposite.unop he)

/-- Closed lifting, proved using homotopy lifting, identifies the full kernel. -/
theorem toBase_range [SimplyConnectedSpace E] : (toBase cov U e).range = (toTotal cov U e).ker := by
  apply le_antisymm
  · rintro w ⟨v,rfl⟩
    obtain ⟨γ,hγ⟩ := Quotient.exists_rep v.unop
    have hg : MulOpposite.op (Path.Homotopic.Quotient.mk γ) = v := congrArg MulOpposite.op hγ
    rw [← hg]
    change toTotal cov U e (toBase cov U e (MulOpposite.op (Path.Homotopic.Quotient.mk γ))) = 1
    apply MulOpposite.unop_injective
    change Path.Homotopic.Quotient.mk ((γ.map (projection cov U).continuous).map (inclusion U).continuous) = Path.Homotopic.Quotient.mk (Path.refl (p e.val))
    apply Path.Homotopic.Quotient.eq.mpr
    exact (SimplyConnectedSpace.paths_homotopic (γ.map (totalInclusion U).continuous) (Path.refl e.val)).map ⟨p,cov.continuous⟩
  · intro w hw
    obtain ⟨γ,hγ⟩ := Quotient.exists_rep w.unop
    have hg : MulOpposite.op (Path.Homotopic.Quotient.mk γ) = w := congrArg MulOpposite.op hγ
    have hnull : (γ.map (inclusion U).continuous).Homotopic (Path.refl (p e.val)) := by
      apply Path.Homotopic.Quotient.eq.mp
      change ((toTotal cov U e) (MulOpposite.op (Path.Homotopic.Quotient.mk γ))).unop = (1 : FundamentalGroup X (p e.val))
      rw [hg]
      exact congrArg MulOpposite.unop hw
    let cp := cov.restrictPreimage U
    let t := cp.liftPath γ e γ.source
    have he : (totalInclusion U).comp t = cov.liftPath (γ.map (inclusion U).continuous) e.val (congrArg Subtype.val γ.source) := by
      apply (cov.eq_liftPath_iff' _).mpr
      constructor
      · ext s
        exact congrArg Subtype.val (congrFun (cp.liftPath_lifts γ e γ.source) s)
      · change (t 0).val = e.val
        exact congrArg Subtype.val (cp.liftPath_zero γ e γ.source)
    have ht : t 1 = e := by
      apply Subtype.ext
      change ((totalInclusion U).comp t) 1 = e.val
      rw [he]
      exact lift_loop_closed cov _ hnull
    let δ : Path e e := ⟨t,cp.liftPath_zero γ e γ.source,ht⟩
    refine ⟨MulOpposite.op (Path.Homotopic.Quotient.mk δ),?_⟩
    rw [← hg]
    apply MulOpposite.unop_injective
    change Path.Homotopic.Quotient.mk (δ.map (projection cov U).continuous) = Path.Homotopic.Quotient.mk γ
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext s
    exact congrFun (cp.liftPath_lifts γ e γ.source) s

/-- This is an equivalence with the actual kernel, not an assumed presentation. -/
def fundamentalKernelEquiv [SimplyConnectedSpace E] :
    (FundamentalGroup (p ⁻¹' U) e)ᵐᵒᵖ ≃* (toTotal cov U e).ker :=
  (MonoidHom.ofInjective (toBase_injective cov U e)).trans
    (MulEquiv.subgroupCongr (toBase_range cov U e))

end EilenbergGanea.CoverKernel


namespace EilenbergGanea.PathTransport
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def anchored {r x : X} (q : Path r x) (p : Path x x) : (FundamentalGroup X r)ᵐᵒᵖ :=
  MulOpposite.op (asClass ((q.trans p).trans q.symm))
def difference {r x : X} (q s : Path r x) : (FundamentalGroup X r)ᵐᵒᵖ :=
  MulOpposite.op (asClass (q.trans s.symm))

@[simp] theorem anchored_map (f : C(X,Y)) {r x : X} (q : Path r x) (p : Path x x) :
    (FundamentalGroup.map f r).op (anchored q p) = anchored (q.map f.continuous) (p.map f.continuous) := by
  apply MulOpposite.unop_injective
  change asClass (((q.trans p).trans q.symm).map f.continuous) = _
  rw [Path.map_trans,Path.map_trans,← Path.map_symm]
  rfl

/-- Changing the path to a circle changes its based relation by conjugacy. -/
theorem anchored_conjugate {r x : X} (q s : Path r x) (p : Path x x) :
    anchored q p = difference q s * anchored s p * (difference q s)⁻¹ := by
  apply MulOpposite.unop_injective
  change asClass ((q.trans p).trans q.symm) =
    ((asClass (q.trans s.symm)).trans (asClass ((s.trans p).trans s.symm))).trans (asClass (q.trans s.symm)).symm
  rw [show (asClass (q.trans s.symm)).symm = asClass (s.trans q.symm) by
    rw [asClass,← Path.Homotopic.Quotient.mk_symm,Path.trans_symm,Path.symm_symm]]
  simp only [asClass,Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk s).symm (Path.Homotopic.Quotient.mk s),
    Path.Homotopic.Quotient.symm_trans,Path.Homotopic.Quotient.refl_trans]
  rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk s).symm (Path.Homotopic.Quotient.mk s),
    Path.Homotopic.Quotient.symm_trans,Path.Homotopic.Quotient.refl_trans]

/-- Pointwise equality of anchored curves handles changes of endpoint proofs. -/
theorem anchored_congr {r x y : X} (q : Path r x) (s : Path r y)
    (p : Path x x) (t : Path y y) (hqs : ∀ z, q z = s z) (hpt : ∀ z, p z = t z) :
    anchored q p = anchored s t := by
  have hxy : x = y := by simpa using hqs 1
  subst y
  have hq : q = s := Path.ext (funext hqs)
  have hp : p = t := Path.ext (funext hpt)
  rw [hq,hp]

end EilenbergGanea.PathTransport


namespace EilenbergGanea.CoverMonodromy
open scoped ContinuousMap
variable {X E G : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [Group G] [MulAction G E] {p : E → X}
variable (hp : IsQuotientCoveringMap p G) [SimplyConnectedSpace E] (e : E)

def traversalEquiv : (FundamentalGroup X (p e))ᵐᵒᵖ ≃* G :=
  (hp.fundamentalGroupEquiv (⟨e,rfl⟩ : p ⁻¹' {p e})).op.trans (MulEquiv.opOp G).symm

/-- Monodromy reads exactly the endpoint of a lifted traversal-order loop. -/
theorem traversalEquiv_loop (d : G) (γ : Path e (d • e)) :
    traversalEquiv hp e (MulOpposite.op (Path.Homotopic.Quotient.mk
      ((γ.map hp.continuous).cast rfl (hp.map_smul d).symm))) = d := by
  change (hp.fundamentalGroupToMulOpposite (⟨e,rfl⟩ : p ⁻¹' {p e})
    (Path.Homotopic.Quotient.mk ((γ.map hp.continuous).cast rfl (hp.map_smul d).symm))).unop = d
  apply MulOpposite.op_injective
  change hp.fundamentalGroupToMulOpposite (⟨e,rfl⟩ : p ⁻¹' {p e}) _ = MulOpposite.op d
  rw [hp.fundamentalGroupToMulOpposite_apply_eq_Iff]
  have hh := hp.isCoveringMap.monodromy_eq_of_map_eq
    (γ := Path.Homotopic.Quotient.mk ((γ.map hp.continuous).cast rfl (hp.map_smul d).symm))
    (ex := (⟨e,rfl⟩ : p ⁻¹' {p e})) (ey := (⟨d • e,hp.map_smul d⟩ : p ⁻¹' {p e}))
    (Path.Homotopic.Quotient.mk γ) (by rfl)
  exact (congrArg Subtype.val hh).symm

/-- A pair of lifted anchors differing by a deck translate records that exact
translate, independently of all anchor choices. -/
theorem traversalEquiv_difference (d : G) {z : E}
    (s : Path e (d • z)) (t : Path e z) :
    traversalEquiv hp e (MulOpposite.op (Path.Homotopic.Quotient.mk
      (((s.map hp.continuous).cast rfl (hp.map_smul d).symm).trans
        (t.map hp.continuous).symm))) = d := by
  let γ : Path e (d • e) := s.trans (t.map (hp.continuous_const_smul d)).symm
  have he : (((s.map hp.continuous).cast rfl (hp.map_smul d).symm).trans
        (t.map hp.continuous).symm) =
      ((γ.map hp.continuous).cast rfl (hp.map_smul d).symm) := by
    apply Path.ext
    funext a
    change _ = p ((s.trans (t.map (hp.continuous_const_smul d)).symm) a)
    simp only [Path.trans_apply,Path.cast_coe,Path.map_coe,Path.symm_apply]
    split_ifs <;> simp only [Function.comp_apply,hp.map_smul]
  rw [he]
  exact traversalEquiv_loop hp e d γ

end EilenbergGanea.CoverMonodromy




end

end OAI
