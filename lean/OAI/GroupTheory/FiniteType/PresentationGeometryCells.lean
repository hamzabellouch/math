import Mathlib
import OAI.GroupTheory.FiniteType.PresentationGeometryDescend

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval
namespace PresentationGeometry.Cells
section
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable {k d : ℕ} (f : C(boundary k d, X))

theorem old_fundamentalGroupMap_surjective (hd : 1 < d) (b : X) :
    Function.Surjective (FundamentalGroup.map
      (⟨Adjunction.old f, Adjunction.continuous_old f⟩ : C(X, Space f)) b) := by
  let bU : collar f := ⟨Adjunction.old f b, mem_collar_old f b⟩
  let r : C(collar f, X) := (shellRetraction f).comp (collarToShell f)
  have hr : r bU = b := by simp [r, bU]
  intro g
  obtain ⟨gU, hgU⟩ := collar_fundamentalGroupMap_surjective f hd bU g
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective gU
  let q : Path b b := (p.map r.continuous).cast hr.symm hr.symm
  refine ⟨Path.Homotopic.Quotient.mk q, ?_⟩
  rw [← hgU]
  change Path.Homotopic.Quotient.mk (q.map (Adjunction.continuous_old f)) =
    Path.Homotopic.Quotient.mk (p.map continuous_subtype_val)
  apply Quotient.sound
  apply Path.Homotopic.symm
  refine ⟨{
    toFun := fun z => shellSlide f z.1 (collarToShell f (p z.2))
    continuous_toFun := (shellSlide_continuous f).comp
      (continuous_fst.prodMk ((collarToShell f).continuous.comp
        (p.continuous.comp continuous_snd)))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    simp only [shellSlide_zero, shellInclude_collarToShell, Path.coe_toContinuousMap,
      Path.map_coe, Function.comp_apply]
  · intro t
    change shellSlide f 1 (collarToShell f (p t)) = Adjunction.old f (r (p t))
    exact shellSlide_one f _
  · intro t s hs
    rcases hs with hs | hs
    · subst s
      change shellSlide f t (collarToShell f (p 0)) = (p 0 : Space f)
      rw [p.source]
      simp [bU]
    · have hs' : s = 1 := hs
      subst s
      change shellSlide f t (collarToShell f (p 1)) = (p 1 : Space f)
      rw [p.target]
      simp [bU]

end

open Set Metric
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable {k d : ℕ} (f : C(boundary k d, X))

def collarRetraction : C(collar f, X) := (shellRetraction f).comp (collarToShell f)

@[simp] theorem collarRetraction_old (x : X) :
    collarRetraction f ⟨Adjunction.old f x, mem_collar_old f x⟩ = x := by
  simp [collarRetraction]

def interiorLift (i : Fin k) : C(cellInterior f i, OpenDisk d) :=
  ⟨(characteristic_isOpenEmbedding f i).isEmbedding.toHomeomorph.symm,
    (characteristic_isOpenEmbedding f i).isEmbedding.toHomeomorph.symm.continuous⟩

omit [T2Space X] [CompactSpace X] in
@[simp] theorem interiorLift_disk (i : Fin k) (z : cellInterior f i) :
    Adjunction.disk f (i,interiorInDisk (interiorLift f i z)) = z.1 := by
  rw [← characteristic_on_openDisk]
  exact congrArg Subtype.val
    ((characteristic_isOpenEmbedding f i).isEmbedding.toHomeomorph.apply_symm_apply z)

omit [T2Space X] [CompactSpace X] in
theorem overlapLift_half (i : Fin k) (z : (collar f ∩ cellInterior f i : Set (Space f))) :
    (1/2 : ℝ) < ‖(interiorLift f i ⟨z.1,z.2.2⟩).1‖ := by
  apply (mem_collar_disk_iff f i (interiorInDisk (interiorLift f i ⟨z.1,z.2.2⟩))).mp
  rw [interiorLift_disk]
  exact z.2.1

def overlapShell (i : Fin k) (z : (collar f ∩ cellInterior f i : Set (Space f))) : Shell d :=
  ⟨(interiorLift f i ⟨z.1,z.2.2⟩).1, (overlapLift_half f i z).le,
    (mem_ball_zero_iff.mp (interiorLift f i ⟨z.1,z.2.2⟩).2).le⟩

omit [T2Space X] [CompactSpace X] in
theorem overlapShell_continuous (i : Fin k) : Continuous (overlapShell f i) :=
  (continuous_subtype_val.comp ((interiorLift f i).continuous.comp
    (continuous_subtype_val.subtype_mk (fun z => z.2.2)))).subtype_mk _

def overlapBoundary (i : Fin k) : C((collar f ∩ cellInterior f i : Set (Space f)), boundary k d) :=
  ⟨fun z => shellUnit (i,overlapShell f i z),
    shellUnit_continuous.comp (continuous_const.prodMk (overlapShell_continuous f i))⟩

theorem collarToShell_overlap (i : Fin k) (z : (collar f ∩ cellInterior f i : Set (Space f))) :
    collarToShell f ⟨z.1,z.2.1⟩ = Adjunction.disk (shellAttach f) (i,overlapShell f i z) := by
  apply shellInclude_injective f
  rw [shellInclude_collarToShell,shellInclude_disk]
  exact (interiorLift_disk f i ⟨z.1,z.2.2⟩).symm

@[simp] theorem collarRetraction_overlap (i : Fin k)
    (z : (collar f ∩ cellInterior f i : Set (Space f))) :
    collarRetraction f ⟨z.1,z.2.1⟩ = f (overlapBoundary f i z) := by
  change shellRetraction f (collarToShell f _) = _
  rw [collarToShell_overlap, shellRetraction_disk]
  rfl

end PresentationGeometry.Cells

namespace PresentationGeometry.CellCoverExtension
open Set Cells
variable {X ι Q : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable {k d : ℕ} (f : C(boundary k d, X)) (b : X) (Z : FiberBundleCore ι X Q)

def baseSet : ι ⊕ Fin k → Set (Cells.Space f)
  | .inl j => Subtype.val '' ((collarRetraction f) ⁻¹' Z.baseSet j)
  | .inr i => cellInterior f i

omit [Group Q] [DiscreteTopology Q] in
@[simp] theorem mem_baseSet_old (j : ι) (x : Cells.Space f) :
    x ∈ baseSet f Z (.inl j) ↔ ∃ h : x ∈ collar f, collarRetraction f ⟨x,h⟩ ∈ Z.baseSet j := by
  constructor
  · rintro ⟨⟨x,hx⟩,h,rfl⟩
    exact ⟨hx,h⟩
  · rintro ⟨hx,h⟩
    exact ⟨⟨x,hx⟩,h,rfl⟩

omit [Group Q] [DiscreteTopology Q] in
theorem baseSet_isOpen (a : ι ⊕ Fin k) : IsOpen (baseSet f Z a) := by
  cases a with
  | inl j =>
    exact (collar_isOpen f).isOpenMap_subtype_val _
      ((Z.isOpen_baseSet j).preimage (collarRetraction f).continuous)
  | inr i => exact cellInterior_isOpen f i

omit [Group Q] [DiscreteTopology Q] in
theorem mem_baseSet (x : Cells.Space f) : ∃ a, x ∈ baseSet f Z a := by
  have hx : x ∈ collar f ∪ ⋃ i, cellInterior f i := by rw [collar_union_interiors]; trivial
  rcases hx with hx | hx
  · exact ⟨.inl (Z.indexAt (collarRetraction f ⟨x,hx⟩)),
      (mem_baseSet_old f Z _ x).mpr ⟨hx,Z.mem_baseSet_at _⟩⟩
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact ⟨.inr i,hi⟩

noncomputable def retractAt (x : Cells.Space f) : X := by
  classical
  exact if hx : x ∈ collar f then collarRetraction f ⟨x,hx⟩ else b

@[simp] theorem retractAt_collar (x : collar f) : retractAt f b x.1 = collarRetraction f x := by
  classical
  simp only [retractAt,dite_eq_left x.2]

@[simp] theorem retractAt_old (x : X) : retractAt f b (Adjunction.old f x) = x := by
  exact (retractAt_collar f b ⟨Adjunction.old f x,mem_collar_old f x⟩).trans
    (collarRetraction_old f x)

variable (pot : ι → X → Q)
variable (s : C(boundary k d,Z.TotalSpace))
variable (hs : ∀ c, Z.proj (s c) = f c)

def overlapSection (i : Fin k) : C((collar f ∩ cellInterior f i : Set (Cells.Space f)),Z.TotalSpace) :=
  s.comp (overlapBoundary f i)

include hs in
omit [Group Q] [DiscreteTopology Q] in
@[simp] theorem overlapSection_proj (i : Fin k)
    (x : (collar f ∩ cellInterior f i : Set (Cells.Space f))) :
    Z.proj (overlapSection f Z s i x) = collarRetraction f ⟨x.1,x.2.1⟩ := by
  rw [collarRetraction_overlap]
  exact hs _

noncomputable def potential : ι ⊕ Fin k → Cells.Space f → Q := by
  classical
  exact fun
    | .inl j,x => pot j (retractAt f b x)
    | .inr i,x => if hx : x ∈ collar f ∩ cellInterior f i then
        ((pot (Z.indexAt (retractAt f b x)) (retractAt f b x))⁻¹ *
          (show Q from (overlapSection f Z s i ⟨x,hx⟩).2))⁻¹ else 1

noncomputable def transition (i j : ι ⊕ Fin k) (x : Cells.Space f) (q : Q) : Q :=
  potential f b Z pot s j x * (potential f b Z pot s i x)⁻¹ * q

def mixedCoordinate (j : ι) (i : Fin k) :
    C((baseSet f Z (.inl j) ∩ baseSet f Z (.inr i) : Set (Cells.Space f)),Q) := by
  let lift : C((baseSet f Z (.inl j) ∩ baseSet f Z (.inr i) : Set (Cells.Space f)),Z.TotalSpace) :=
    (overlapSection f Z s i).comp
      ⟨fun x => ⟨x.1,(mem_baseSet_old f Z j x.1).mp x.2.1 |>.choose,x.2.2⟩,
        continuous_subtype_val.subtype_mk _⟩
  refine ⟨fun x => ((Z.localTriv j) (lift x)).2, ?_⟩
  apply continuous_snd.comp
  apply (Z.localTriv j).continuousOn.comp_continuous lift.continuous
  intro x
  change (lift x).1 ∈ Z.baseSet j
  rw [show (lift x).1 = collarRetraction f
      ⟨x.1, (mem_baseSet_old f Z j x.1).mp x.2.1 |>.choose⟩ from
        overlapSection_proj f Z s hs i _]
  exact (mem_baseSet_old f Z j x.1).mp x.2.1 |>.choose_spec

variable (hpot : ∀ i j x q, Z.coordChange i j x q = pot j x * (pot i x)⁻¹ * q)

include hpot in
omit [DiscreteTopology Q] in
theorem mixedCoordinate_formula (j : ι) (i : Fin k)
    (x : (baseSet f Z (.inl j) ∩ baseSet f Z (.inr i) : Set (Cells.Space f))) :
    mixedCoordinate f Z s hs j i x =
      potential f b Z pot s (.inl j) x.1 * (potential f b Z pot s (.inr i) x.1)⁻¹ := by
  classical
  have hx : x.1 ∈ collar f ∩ cellInterior f i :=
    ⟨((mem_baseSet_old f Z j x.1).mp x.2.1).choose,x.2.2⟩
  change Z.coordChange (Z.indexAt (overlapSection f Z s i ⟨x.1,hx⟩).1) j
    (overlapSection f Z s i ⟨x.1,hx⟩).1 (overlapSection f Z s i ⟨x.1,hx⟩).2 = _
  have he : (overlapSection f Z s i ⟨x.1,hx⟩).1 = retractAt f b x.1 := by
    exact (overlapSection_proj f Z s hs i ⟨x.1,hx⟩).trans
      (retractAt_collar f b ⟨x.1,hx.1⟩).symm
  erw [hpot,he]
  simp only [potential,dite_eq_left hx,inv_inv]
  exact mul_assoc _ _ _

include hpot in
omit [DiscreteTopology Q] in
theorem transition_old_new (j : ι) (i : Fin k)
    (x : (baseSet f Z (.inl j) ∩ baseSet f Z (.inr i) : Set (Cells.Space f))) (q : Q) :
    transition f b Z pot s (.inl j) (.inr i) x.1 q =
      (mixedCoordinate f Z s hs j i x)⁻¹ * q := by
  rw [mixedCoordinate_formula f b Z pot s hs hpot]
  simp only [transition,mul_inv_rev,inv_inv]

include hpot in
omit [DiscreteTopology Q] in
theorem transition_new_old (j : ι) (i : Fin k)
    (x : (baseSet f Z (.inl j) ∩ baseSet f Z (.inr i) : Set (Cells.Space f))) (q : Q) :
    transition f b Z pot s (.inr i) (.inl j) x.1 q =
      mixedCoordinate f Z s hs j i x * q := by
  rw [mixedCoordinate_formula f b Z pot s hs hpot]
  rfl

include hs hpot in
theorem continuousOn_transition (i j : ι ⊕ Fin k) :
    ContinuousOn (fun p : Cells.Space f × Q => transition f b Z pot s i j p.1 p.2)
      ((baseSet f Z i ∩ baseSet f Z j) ×ˢ univ) := by
  classical
  by_cases hij : i = j
  · subst j
    simpa [transition] using (continuous_snd : Continuous (Prod.snd : Cells.Space f × Q → Q)).continuousOn
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      rw [continuousOn_iff_continuous_domRestrict]
      let D := ((baseSet f Z (.inl i) ∩ baseSet f Z (.inl j)) ×ˢ (univ : Set Q))
      let c : C(D, collar f) := ⟨fun p => ⟨p.1.1,
        ((mem_baseSet_old f Z i p.1.1).mp p.2.1.1).choose⟩,
        (continuous_fst.comp continuous_subtype_val).subtype_mk _⟩
      have hr : Continuous (fun p : D => (collarRetraction f (c p),p.1.2)) :=
        ((collarRetraction f).continuous.comp c.continuous).prodMk
          (continuous_snd.comp continuous_subtype_val)
      have hc := (Z.continuousOn_coordChange i j).comp_continuous hr (fun p =>
        (show (collarRetraction f (c p),p.1.2) ∈ (Z.baseSet i ∩ Z.baseSet j) ×ˢ univ from
          ⟨⟨((mem_baseSet_old f Z i p.1.1).mp p.2.1.1).choose_spec,
            ((mem_baseSet_old f Z j p.1.1).mp p.2.1.2).choose_spec⟩,mem_univ _⟩))
      convert hc using 1
      funext p
      change transition f b Z pot s (.inl i) (.inl j) p.1.1 p.1.2 =
        Z.coordChange i j (collarRetraction f (c p)) p.1.2
      rw [hpot]
      simp only [transition,potential]
      rw [show retractAt f b p.1.1 = collarRetraction f (c p) from retractAt_collar f b (c p)]
    | inr j =>
      rw [continuousOn_iff_continuous_domRestrict]
      have hc : Continuous (fun p : (baseSet f Z (.inl i) ∩ baseSet f Z (.inr j)) ×ˢ (univ : Set Q) =>
          mixedCoordinate f Z s hs i j ⟨p.1.1,p.2.1⟩) :=
        (mixedCoordinate f Z s hs i j).continuous.comp
          ((continuous_fst.comp continuous_subtype_val).subtype_mk _)
      convert hc.inv.mul (continuous_snd.comp continuous_subtype_val) using 1
      funext p
      exact transition_old_new f b Z pot s hs hpot i j ⟨p.1.1,p.2.1⟩ p.1.2
  | inr i =>
    cases j with
    | inl j =>
      rw [inter_comm,continuousOn_iff_continuous_domRestrict]
      have hc : Continuous (fun p : (baseSet f Z (.inl j) ∩ baseSet f Z (.inr i)) ×ˢ (univ : Set Q) =>
          mixedCoordinate f Z s hs j i ⟨p.1.1,p.2.1⟩) :=
        (mixedCoordinate f Z s hs j i).continuous.comp
          ((continuous_fst.comp continuous_subtype_val).subtype_mk _)
      convert hc.mul (continuous_snd.comp continuous_subtype_val) using 1
      funext p
      exact transition_new_old f b Z pot s hs hpot j i ⟨p.1.1,p.2.1⟩ p.1.2
    | inr j =>
      have hd := cellInterior_pairwiseDisjoint f (by
        intro h; apply hij; exact congrArg Sum.inr h : i ≠ j)
      have he : baseSet f Z (.inr i) ∩ baseSet f Z (.inr j) = ∅ := hd.inter_eq
      rw [he,empty_prod]
      exact continuousOn_empty _

noncomputable def coveringCore : FiberBundleCore (ι ⊕ Fin k) (Cells.Space f) Q where
  baseSet := baseSet f Z
  isOpen_baseSet := baseSet_isOpen f Z
  indexAt x := (mem_baseSet f Z x).choose
  mem_baseSet_at x := (mem_baseSet f Z x).choose_spec
  coordChange := transition f b Z pot s
  coordChange_self := by intros; simp [transition]
  continuousOn_coordChange := continuousOn_transition f b Z pot s hs hpot
  coordChange_comp := by intros; simp only [transition]; group

theorem coveringCore_isCoveringMap :
    IsCoveringMap (coveringCore f b Z pot s hs hpot).proj := FiberBundle.isCoveringMap

@[simp] theorem coveringCore_old_coordChange (i j : ι) (x : X) (q : Q) :
    (coveringCore f b Z pot s hs hpot).coordChange (.inl i) (.inl j) (Adjunction.old f x) q =
      Z.coordChange i j x q := by
  rw [hpot]
  simp only [coveringCore,transition,potential,retractAt_old]

@[simp] theorem mem_coveringCore_old (i : ι) (x : X) :
    Adjunction.old f x ∈ (coveringCore f b Z pot s hs hpot).baseSet (.inl i) ↔ x ∈ Z.baseSet i := by
  change Adjunction.old f x ∈ baseSet f Z (.inl i) ↔ _
  rw [mem_baseSet_old]
  constructor
  · rintro ⟨hx,h⟩
    simpa only [collarRetraction_old] using h
  · intro hx
    exact ⟨mem_collar_old f x,by simpa only [collarRetraction_old] using hx⟩

end PresentationGeometry.CellCoverExtension

end

end OAI
