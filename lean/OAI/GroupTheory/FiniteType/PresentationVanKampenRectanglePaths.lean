import Mathlib
import OAI.GroupTheory.FiniteType.CoreDeck

namespace OAI

noncomputable section
namespace PresentationVanKampen
open scoped unitInterval
variable {X : Type*} [TopologicalSpace X]

theorem rectangle_paths {a b c d : X} (p : Path a b) (q : Path b d)
    (r : Path a c) (s : Path c d) (H : C(I × I, X))
    (hp : ∀ t, H (0,t) = p t) (hq : ∀ t, H (t,1) = q t)
    (hr : ∀ t, H (t,0) = r t) (hs : ∀ t, H (1,t) = s t) :
    (p.trans q).Homotopic (r.trans s) := by
  let pH : Path (H (0,0)) (H (0,1)) :=
    (Path.id.map (continuous_const.prodMk continuous_id)).map H.continuous
  let qH : Path (H (0,1)) (H (1,1)) :=
    (Path.id.map (continuous_id.prodMk continuous_const)).map H.continuous
  let rH : Path (H (0,0)) (H (1,0)) :=
    (Path.id.map (continuous_id.prodMk continuous_const)).map H.continuous
  let sH : Path (H (1,0)) (H (1,1)) :=
    (Path.id.map (continuous_const.prodMk continuous_id)).map H.continuous
  have ha : a = H (0,0) := ((hp 0).trans p.source).symm
  have hd : d = H (1,1) := ((hq 1).trans q.target).symm
  have he₁ : (pH.trans qH).cast ha hd = p.trans q := by
    ext t
    change (pH.trans qH) t = (p.trans q) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hp _
    · exact hq _
  have he₂ : (rH.trans sH).cast ha hd = r.trans s := by
    ext t
    change (rH.trans sH) t = (r.trans s) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hr _
    · exact hs _
  have h := (rectangle_homotopic H).pathCast ha hd
  change ((pH.trans qH).cast ha hd).Homotopic ((rH.trans sH).cast ha hd) at h
  rwa [he₁, he₂] at h

end PresentationVanKampen

namespace PresentationGeometry.Cells
open scoped unitInterval
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable {k d : ℕ} (f : C(boundary k d, X))

@[simp] theorem collarToShell_disk (i : Fin k) (v : Shell d)
    (hv : (1 / 2 : ℝ) < ‖v.1‖) :
    collarToShell f ⟨Adjunction.disk f (i,shellInDisk v),
      (mem_collar_disk_iff f i (shellInDisk v)).mpr hv⟩ =
        Adjunction.disk (shellAttach f) (i,v) := by
  apply shellInclude_injective f
  simp

end PresentationGeometry.Cells

namespace PresentationGeometry.Rose
section
open scoped unitInterval
open PresentationVanKampen
variable {k : ℕ}

def outward (a : Cells.collar (attaching k)) : Path a.1 (basepoint k) where
  toFun t := Cells.shellSlide (attaching k) t (Cells.collarToShell (attaching k) a)
  continuous_toFun := (Cells.shellSlide_continuous (attaching k)).comp
    (continuous_id.prodMk continuous_const)
  source' := by simp
  target' := by rw [Cells.shellSlide_one]; rfl

@[simp] theorem outward_base :
    outward ⟨basepoint k, Cells.mem_collar_old (attaching k) PUnit.unit⟩ =
      Path.refl (basepoint k) := by
  ext t
  change Cells.shellSlide (attaching k) t
    (Cells.collarToShell (attaching k) ⟨Adjunction.old (attaching k) PUnit.unit,_⟩) = _
  simp [basepoint, Path.refl]
  rfl

theorem collar_path_homotopic {a c : Space k} (p : Path a c)
    (hp : Set.range p ⊆ Cells.collar (attaching k)) :
    (p.trans (outward ⟨c,hp p.target_mem_range⟩)).Homotopic
      (outward ⟨a,hp p.source_mem_range⟩) := by
  let H : C(I × I, Space k) :=
    ⟨fun z => Cells.shellSlide (attaching k) z.1
      (Cells.collarToShell (attaching k) ((pathIn p hp) z.2)),
      (Cells.shellSlide_continuous (attaching k)).comp
        (continuous_fst.prodMk ((Cells.collarToShell (attaching k)).continuous.comp
          ((pathIn p hp).continuous.comp continuous_snd)))⟩
  have h := rectangle_paths p (outward ⟨c,hp p.target_mem_range⟩)
    (outward ⟨a,hp p.source_mem_range⟩) (Path.refl (basepoint k)) H
    (fun t => by simp [H, pathIn])
    (fun t => by
      change Cells.shellSlide (attaching k) t
        (Cells.collarToShell (attaching k) ((pathIn p hp) 1)) = _
      rw [(pathIn p hp).target]
      rfl)
    (fun t => by
      change Cells.shellSlide (attaching k) t
        (Cells.collarToShell (attaching k) ((pathIn p hp) 0)) = _
      rw [(pathIn p hp).source]
      rfl)
    (fun t => by
      change Cells.shellSlide (attaching k) 1 _ = _
      rw [Cells.shellSlide_one]
      rfl)
  exact h.trans (Path.Homotopic.trans_refl _)

theorem radialDisk_one_cases (v : Cells.Shell 1) :
    Cells.radialDisk 1 v = edgeLeft ∨ Cells.radialDisk 1 v = edgeRight := by
  have hn : ‖(Cells.radialDisk 1 v).1‖ = 1 := by
    change ‖Cells.radialVector 1 v‖ = 1
    rw [Cells.norm_radialVector]
    simp
  have he : |(Cells.radialDisk 1 v).1 0| = 1 := by
    have hv : (Cells.radialDisk 1 v).1 = fun _ : Fin 1 => (Cells.radialDisk 1 v).1 0 := by
      funext j
      rw [show j = 0 from Subsingleton.elim _ _]
    rw [hv] at hn
    simpa only [pi_norm_const, Real.norm_eq_abs] using hn
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp he with he | he
  · right
    apply Subtype.ext
    funext j
    fin_cases j
    exact he
  · left
    apply Subtype.ext
    funext j
    fin_cases j
    exact he

theorem spoke_outward_mem (a : Cells.collar (attaching k)) :
    Path.Homotopic.Quotient.mk ((spoke a.1).trans (outward a)) ∈
      (freeToFundamental k).range := by
  rcases pointCode_cases a.1 with ⟨_,he⟩ | ⟨i,v,hv,_,he⟩
  · have ha : a = ⟨basepoint k, Cells.mem_collar_old (attaching k) PUnit.unit⟩ :=
      Subtype.ext he
    subst a
    simp only [spoke_base, outward_base]
    have hh := (Path.Homotopic.refl_trans (Path.refl (basepoint k)))
    have hq : Path.Homotopic.Quotient.mk ((Path.refl (basepoint k)).trans (Path.refl _)) =
        Path.Homotopic.Quotient.refl (basepoint k) :=
      Quotient.sound hh
    rw [hq]
    exact (freeToFundamental k).range.one_mem
  · have hlow : (1 / 2 : ℝ) < ‖v.1‖ := by
      have := a.property
      rw [he] at this
      exact (Cells.mem_collar_disk_iff (attaching k) i v).mp this
    let v' : Cells.Shell 1 := ⟨v.1, le_of_lt hlow, mem_closedBall_zero_iff.mp v.property⟩
    let a' : Cells.collar (attaching k) := ⟨edgeMap i v,
      (Cells.mem_collar_disk_iff (attaching k) i v).mpr hlow⟩
    have ha : a = a' := Subtype.ext he
    subst a
    let q : Path v (Cells.radialDisk 1 v') :=
      ⟨⟨fun t => Cells.radialDisk t v',
        Cells.radialDisk_continuous.comp (continuous_id.prodMk continuous_const)⟩,
        Cells.radialDisk_zero v', rfl⟩
    have hend : edgeMap i (Cells.radialDisk 1 v') = basepoint k := by
      rcases radialDisk_one_cases v' with hr | hr <;> rw [hr] <;> simp
    have hout : (q.map (edgeMap i).continuous).cast rfl hend.symm = outward a' := by
      ext t
      change edgeMap i (Cells.radialDisk t v') =
        Cells.shellSlide (attaching k) t (Cells.collarToShell (attaching k) a')
      have hc : Cells.collarToShell (attaching k) a' =
          Adjunction.disk (Cells.shellAttach (attaching k)) (i,v') :=
        Cells.collarToShell_disk (attaching k) i v' hlow
      rw [hc, Cells.shellSlide_disk]
      rfl
    have h := (SimplyConnectedSpace.paths_homotopic
      ((edgeInterval edgeLeft v).trans q)
      (edgeInterval edgeLeft (Cells.radialDisk 1 v'))).map (edgeMap i) |>.pathCast
        (edgeMap_left i).symm hend.symm
    have h' : ((spoke a'.1).trans (outward a')).Homotopic
        ((edgeSpoke i (Cells.radialDisk 1 v')).cast rfl hend.symm) := by
      change ((spoke (edgeMap i v)).trans (outward a')).Homotopic
        (((edgeInterval edgeLeft (Cells.radialDisk 1 v')).map (edgeMap i).continuous).cast
          (edgeMap_left i).symm hend.symm)
      rw [spoke_edge i v hv]
      simpa only [Path.map_trans, Path.cast_trans, Path.cast_rfl_rfl, hout, edgeSpoke] using h
    have hh : Path.Homotopic.Quotient.mk ((spoke a'.1).trans (outward a')) =
        Path.Homotopic.Quotient.mk
          ((edgeSpoke i (Cells.radialDisk 1 v')).cast rfl hend.symm) := Quotient.sound h'
    rw [hh]
    rcases radialDisk_one_cases v' with hr | hr
    · have he : (edgeSpoke i (Cells.radialDisk 1 v')).cast rfl hend.symm =
          Path.refl (basepoint k) := by
        ext t
        change edgeMap i (edgeInterval edgeLeft (Cells.radialDisk 1 v') t) = basepoint k
        rw [hr]
        exact congrArg (fun p : Path (basepoint k) (basepoint k) => p t) (edgeSpoke_left i)
      rw [he]
      exact (freeToFundamental k).range.one_mem
    · have he : (edgeSpoke i (Cells.radialDisk 1 v')).cast rfl hend.symm =
          generatorLoop i := by
        ext t
        change edgeMap i (edgeInterval edgeLeft (Cells.radialDisk 1 v') t) = generatorLoop i t
        rw [hr]
        exact congrArg (fun p : Path (basepoint k) (basepoint k) => p t) (edgeSpoke_right i)
      rw [he]
      refine ⟨FreeGroup.of i, ?_⟩
      simp [freeToFundamental]

end

open scoped unitInterval
open PresentationVanKampen
variable {k : ℕ}

theorem basedPathClass_collar_mem {a c : Space k} (p : Path a c)
    (hp : Set.range p ⊆ Cells.collar (attaching k)) :
    basedPathClass (basepoint k) spoke p ∈ (freeToFundamental k).range := by
  have hout : ∀ x : Cells.collar (attaching k),
      basedPathClass (basepoint k) spoke (outward x) ∈ (freeToFundamental k).range := by
    intro x
    have he : basedPathClass (basepoint k) spoke (outward x) =
        Path.Homotopic.Quotient.mk ((spoke x.1).trans (outward x)) := by
      simp only [basedPathClass, spoke_base, Path.Homotopic.Quotient.mk_trans,
        Path.Homotopic.Quotient.mk_refl]
      have hr : (Path.Homotopic.Quotient.refl (basepoint k)).symm =
          Path.Homotopic.Quotient.refl (basepoint k) := rfl
      rw [hr, Path.Homotopic.Quotient.trans_refl]
    rw [he]
    exact spoke_outward_mem x
  have he := basedPathClass_homotopic (basepoint k) spoke _ _ (collar_path_homotopic p hp)
  rw [basedPathClass_trans] at he
  have hmem := (freeToFundamental k).range.mul_mem
    ((freeToFundamental k).range.inv_mem (hout ⟨c,hp p.target_mem_range⟩))
    (hout ⟨a,hp p.source_mem_range⟩)
  rwa [← he, inv_mul_cancel_left] at hmem

theorem freeToFundamental_surjective (k : ℕ) :
    Function.Surjective (freeToFundamental k) := by
  let U : Option (Fin k) → Set (Space k) := fun i =>
    match i with
    | none => Cells.collar (attaching k)
    | some i => Cells.cellInterior (attaching k) i
  have hU : ∀ i, IsOpen (U i) := by
    intro i
    cases i with
    | none => exact Cells.collar_isOpen (attaching k)
    | some i => exact Cells.cellInterior_isOpen (attaching k) i
  have hcover : Set.univ ⊆ ⋃ i, U i := by
    intro x hx
    have h : x ∈ Cells.collar (attaching k) ∪ ⋃ i, Cells.cellInterior (attaching k) i := by
      rw [Cells.collar_union_interiors]
      trivial
    rcases h with h | h
    · exact Set.mem_iUnion.mpr ⟨none,h⟩
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp h
      exact Set.mem_iUnion.mpr ⟨some i,hi⟩
  have htop := subgroup_eq_top_of_open_cover U hU hcover (basepoint k) spoke
    (by rw [spoke_base]) (freeToFundamental k).range (by
      intro a c p i hp
      cases i with
      | none => exact basedPathClass_collar_mem p hp
      | some i =>
        rw [basedPathClass_interior p i hp]
        exact (freeToFundamental k).range.one_mem)
  intro g
  have hg : g ∈ (freeToFundamental k).range := by rw [htop]; trivial
  exact hg

end PresentationGeometry.Rose

namespace PresentationGeometry.PresentationComplex
variable {k r : ℕ} (w : Fin r → List (Fin k × Bool))

theorem freeToFundamental_surjective : Function.Surjective (freeToFundamental w) :=
  (Cells.old_fundamentalGroupMap_surjective (AttachingLoops.relators w)
    (by norm_num) (Rose.basepoint k)).comp (Rose.freeToFundamental_surjective k)

theorem presentedToFundamental_surjective :
    Function.Surjective (presentedToFundamental w) := by
  intro g
  obtain ⟨a,ha⟩ := freeToFundamental_surjective w g
  exact ⟨PresentedGroup.mk (relatorSet w) a,ha⟩

end PresentationGeometry.PresentationComplex

namespace PresentationGeometry.Rose
section
open scoped unitInterval
open Set
variable {k : ℕ}

def coverSet : Option (Fin k) → Set (Space k)
  | none => Cells.collar (attaching k)
  | some i => Cells.cellInterior (attaching k) i

theorem coverSet_isOpen (i : Option (Fin k)) : IsOpen (coverSet i) := by
  cases i with
  | none => exact Cells.collar_isOpen (attaching k)
  | some i => exact Cells.cellInterior_isOpen (attaching k) i

theorem mem_coverSet (x : Space k) : ∃ i, x ∈ coverSet i := by
  have hx : x ∈ Cells.collar (attaching k) ∪ ⋃ i, Cells.cellInterior (attaching k) i := by
    rw [Cells.collar_union_interiors]; trivial
  rcases hx with h | h
  · exact ⟨none,h⟩
  · obtain ⟨i,hi⟩ := mem_iUnion.mp h
    exact ⟨some i,hi⟩

theorem overlap_coord_ne_zero (i : Fin k)
    (x : (coverSet (none : Option (Fin k)) ∩ coverSet (some i) : Set (Space k))) :
    (openEdgeLift i ⟨x.1,x.property.2⟩).1 0 ≠ 0 := by
  let v := openEdgeLift i ⟨x.1,x.property.2⟩
  have hv : (1 / 2 : ℝ) < ‖v.1‖ := by
    apply (Cells.mem_collar_disk_iff (attaching k) i v).mp
    change edgeMap i v ∈ Cells.collar (attaching k)
    rw [edgeMap_openEdgeLift]
    exact x.property.1
  intro he
  have hz : v.1 = 0 := by
    funext j
    rw [show j = 0 from Subsingleton.elim _ _]
    exact he
  rw [hz, norm_zero] at hv
  norm_num at hv

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

noncomputable def potential (g : Fin k → Q) : Option (Fin k) → Space k → Q := by
  classical
  exact fun
    | none, _ => 1
    | some i, x => if h : x ∈ Cells.cellInterior (attaching k) i then
        if 0 < (openEdgeLift i ⟨x,h⟩).1 0 then (g i)⁻¹ else 1 else 1

omit [TopologicalSpace Q] [DiscreteTopology Q] in
@[simp] theorem potential_none (g : Fin k → Q) (x : Space k) :
    potential g none x = 1 := rfl

omit [DiscreteTopology Q] in
theorem potential_continuous_overlap (g : Fin k → Q) (i : Fin k) :
    Continuous fun x : (coverSet (none : Option (Fin k)) ∩ coverSet (some i) : Set (Space k)) =>
      potential g (some i) x.1 := by
  classical
  let c : (coverSet (none : Option (Fin k)) ∩ coverSet (some i) : Set (Space k)) → ℝ :=
    fun x => (openEdgeLift i ⟨x.1,x.property.2⟩).1 0
  have hc : Continuous c :=
    (continuous_apply 0).comp (continuous_subtype_val.comp ((openEdgeLift i).continuous.comp
      (continuous_subtype_val.subtype_mk (fun x => x.property.2))))
  have hset : {x | 0 < c x} = {x | 0 ≤ c x} := by
    ext x
    exact lt_iff_le_and_ne.trans
      ⟨fun h => h.1, fun h => ⟨h, (overlap_coord_ne_zero i x).symm⟩⟩
  have hcl : IsClopen {x | 0 < c x} := ⟨by rw [hset]; exact isClosed_le continuous_const hc,
    isOpen_lt continuous_const hc⟩
  have hh : Continuous fun x => if 0 < c x then (g i)⁻¹ else (1 : Q) :=
    Continuous.if (by intro x hx; rw [hcl.frontier_eq] at hx; exact hx.elim)
      continuous_const continuous_const
  convert hh using 1
  funext x
  have hx : x.1 ∈ Cells.cellInterior (attaching k) i := x.property.2
  simp only [potential, dite_eq_left hx]
  rfl

noncomputable def transition (g : Fin k → Q) (i j : Option (Fin k))
    (x : Space k) (q : Q) : Q := potential g j x * (potential g i x)⁻¹ * q

theorem continuousOn_transition (g : Fin k → Q) (i j : Option (Fin k)) :
    ContinuousOn (fun p : Space k × Q => transition g i j p.1 p.2)
      ((coverSet i ∩ coverSet j) ×ˢ univ) := by
  classical
  by_cases hij : i = j
  · subst j
    simpa [transition] using (continuous_snd : Continuous (Prod.snd : Space k × Q → Q)).continuousOn
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      rw [continuousOn_iff_continuous_domRestrict]
      have hc : Continuous (fun p : (coverSet (none : Option (Fin k)) ∩ coverSet (some j)) ×ˢ
          (univ : Set Q) =>
          potential g (some j) p.1.1) :=
        (potential_continuous_overlap g j).comp
          ((continuous_fst.comp continuous_subtype_val).subtype_mk (fun p => p.property.1))
      convert hc.mul (continuous_snd.comp continuous_subtype_val) using 1
      funext p
      simp [transition, Set.domRestrict, potential_none]
  | some i =>
    cases j with
    | none =>
      rw [inter_comm]
      rw [continuousOn_iff_continuous_domRestrict]
      have hc : Continuous (fun p : (coverSet (none : Option (Fin k)) ∩ coverSet (some i)) ×ˢ
          (univ : Set Q) =>
          potential g (some i) p.1.1) :=
        (potential_continuous_overlap g i).comp
          ((continuous_fst.comp continuous_subtype_val).subtype_mk (fun p => p.property.1))
      convert hc.inv.mul (continuous_snd.comp continuous_subtype_val) using 1
      funext p
      simp [transition, Set.domRestrict, potential_none]
    | some j =>
      have hd := Cells.cellInterior_pairwiseDisjoint (attaching k) (by
        intro h; apply hij; exact congrArg some h : i ≠ j)
      have he : coverSet (some i) ∩ coverSet (some j) = ∅ := hd.inter_eq
      rw [he, empty_prod]
      exact continuousOn_empty _

noncomputable def coveringCore (g : Fin k → Q) : FiberBundleCore (Option (Fin k)) (Space k) Q where
  baseSet := coverSet
  isOpen_baseSet := coverSet_isOpen
  indexAt x := (mem_coverSet x).choose
  mem_baseSet_at x := (mem_coverSet x).choose_spec
  coordChange := transition g
  coordChange_self := by intros; simp [transition]
  continuousOn_coordChange := continuousOn_transition g
  coordChange_comp := by intros; simp only [transition]; group

theorem coveringCore_isCoveringMap (g : Fin k → Q) :
    IsCoveringMap (coveringCore g).proj := FiberBundle.isCoveringMap

end

open scoped unitInterval
open Set DiscreteCoverCharts
variable {k : ℕ}

theorem edgeMap_mem_interior (i : Fin k) (v : Cells.Disk 1) (hv : ‖v.1‖ < 1) :
    edgeMap i v ∈ Cells.cellInterior (attaching k) i := by
  refine ⟨⟨v.1,mem_ball_zero_iff.mpr hv⟩,?_⟩
  exact Cells.characteristic_on_disk (attaching k) i v

@[simp] theorem openEdgeLift_edgeMap (i : Fin k) (v : Cells.Disk 1) (hv : ‖v.1‖ < 1) :
    openEdgeLift i ⟨edgeMap i v, edgeMap_mem_interior i v hv⟩ = v := by
  have h := edgeMap_openEdgeLift i ⟨edgeMap i v, edgeMap_mem_interior i v hv⟩
  have hn : (i,v) ∉ Cells.boundary k 1 := by
    intro hm
    have he : ‖v.1‖ = 1 := by
      simpa only [Cells.boundary, mem_ofPred_eq, mem_sphere_zero_iff_norm] using hm
    linarith
  exact congrArg Prod.snd ((Adjunction.disk_eq_disk_of_notMem (attaching k) hn).mp h.symm) |>.symm

def edgeNegative : Cells.Disk 1 := ⟨fun _ => -(3/4 : ℝ), by norm_num [Metric.mem_closedBall, dist_pi_def]⟩
def edgePositive : Cells.Disk 1 := ⟨fun _ => (3/4 : ℝ), by norm_num [Metric.mem_closedBall, dist_pi_def]⟩

@[simp] theorem norm_edgeNegative : ‖(edgeNegative : Cells.Disk 1).1‖ = (3/4 : ℝ) := by
  norm_num [edgeNegative, pi_norm_const]
@[simp] theorem norm_edgePositive : ‖(edgePositive : Cells.Disk 1).1‖ = (3/4 : ℝ) := by
  norm_num [edgePositive, pi_norm_const]

def edgeFirst (i : Fin k) : Path (basepoint k) (edgeMap i edgeNegative) :=
  ((edgeInterval edgeLeft edgeNegative).map (edgeMap i).continuous).cast (edgeMap_left i).symm rfl

def edgeMiddle (i : Fin k) : Path (edgeMap i edgeNegative) (edgeMap i edgePositive) :=
  (edgeInterval edgeNegative edgePositive).map (edgeMap i).continuous

def edgeLast (i : Fin k) : Path (edgeMap i edgePositive) (basepoint k) :=
  ((edgeInterval edgePositive edgeRight).map (edgeMap i).continuous).cast rfl (edgeMap_right i).symm

theorem edgeFirst_collar (i : Fin k) : Set.range (edgeFirst i) ⊆ coverSet none := by
  rintro _ ⟨t,rfl⟩
  apply (Cells.mem_collar_disk_iff (attaching k) i (edgeInterval edgeLeft edgeNegative t)).mpr
  have hn : |(edgeInterval edgeLeft edgeNegative t).1 0| ≤
      ‖(edgeInterval edgeLeft edgeNegative t).1‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (edgeInterval edgeLeft edgeNegative t).1 0
  have hv : (edgeInterval edgeLeft edgeNegative t).1 0 = -(1 : ℝ) + (t : ℝ) / 4 := by
    change (Path.segment (fun _ : Fin 1 => (-1 : ℝ)) (fun _ => -(3/4 : ℝ)) t) 0 = _
    simp only [Path.segment_apply, AffineMap.lineMap_apply, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, vadd_eq_add, vsub_eq_sub, smul_eq_mul]
    ring
  rw [hv] at hn
  have ht := t.property
  have hn' := neg_le_abs (-(1 : ℝ) + (t : ℝ) / 4)
  linarith [t.property.1, t.property.2]

theorem edgeMiddle_interior (i : Fin k) : Set.range (edgeMiddle i) ⊆ coverSet (some i) := by
  rintro _ ⟨t,rfl⟩
  apply edgeMap_mem_interior
  have h := (convex_ball (0 : Fin 1 → ℝ) 1).segment_subset
    (mem_ball_zero_iff.mpr (show ‖(edgeNegative : Cells.Disk 1).1‖ < 1 by norm_num))
    (mem_ball_zero_iff.mpr (show ‖(edgePositive : Cells.Disk 1).1‖ < 1 by norm_num))
    ((Path.range_segment edgeNegative.1 edgePositive.1) ▸
      (show Path.segment edgeNegative.1 edgePositive.1 t ∈ Set.range (Path.segment edgeNegative.1 edgePositive.1) from ⟨t,rfl⟩))
  exact mem_ball_zero_iff.mp h

theorem edgeLast_collar (i : Fin k) : Set.range (edgeLast i) ⊆ coverSet none := by
  rintro _ ⟨t,rfl⟩
  apply (Cells.mem_collar_disk_iff (attaching k) i (edgeInterval edgePositive edgeRight t)).mpr
  have hn : |(edgeInterval edgePositive edgeRight t).1 0| ≤
      ‖(edgeInterval edgePositive edgeRight t).1‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (edgeInterval edgePositive edgeRight t).1 0
  have hv : (edgeInterval edgePositive edgeRight t).1 0 = (3/4 : ℝ) + (t : ℝ) / 4 := by
    change (Path.segment (fun _ : Fin 1 => (3/4 : ℝ)) (fun _ => (1 : ℝ)) t) 0 = _
    simp only [Path.segment_apply, AffineMap.lineMap_apply, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, vadd_eq_add, vsub_eq_sub, smul_eq_mul]
    ring
  rw [hv] at hn
  have ht := t.property
  have hn' := le_abs_self ((3/4 : ℝ) + (t : ℝ) / 4)
  linarith [t.property.1, t.property.2]

theorem edge_parts_homotopic (i : Fin k) :
    ((edgeFirst i).trans ((edgeMiddle i).trans (edgeLast i))).Homotopic (generatorLoop i) := by
  have h := (SimplyConnectedSpace.paths_homotopic
    ((edgeInterval edgeLeft edgeNegative).trans
      ((edgeInterval edgeNegative edgePositive).trans (edgeInterval edgePositive edgeRight)))
    (edgeInterval edgeLeft edgeRight)).map (edgeMap i) |>.pathCast
      (edgeMap_left i).symm (edgeMap_right i).symm
  have he : ((edgeInterval edgeLeft edgeRight).map (edgeMap i).continuous).cast
      (edgeMap_left i).symm (edgeMap_right i).symm = generatorLoop i := by
    calc
      _ = (edgeSpoke i edgeRight).cast rfl (edgeMap_right i).symm := by ext t; rfl
      _ = generatorLoop i := edgeSpoke_right i
  rw [he] at h
  simpa only [Path.map_trans, Path.cast_trans, Path.cast_rfl_rfl, edgeFirst, edgeMiddle,
    edgeLast] using h

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

omit [TopologicalSpace Q] [DiscreteTopology Q] in
@[simp] theorem potential_negative (g : Fin k → Q) (i : Fin k) :
    potential g (some i) (edgeMap i edgeNegative) = 1 := by
  have hv : ‖(edgeNegative : Cells.Disk 1).1‖ < 1 := by norm_num
  simp only [potential, dite_eq_left (edgeMap_mem_interior i edgeNegative hv)]
  norm_num [edgeNegative]

omit [TopologicalSpace Q] [DiscreteTopology Q] in
@[simp] theorem potential_positive (g : Fin k → Q) (i : Fin k) :
    potential g (some i) (edgeMap i edgePositive) = (g i)⁻¹ := by
  have hv : ‖(edgePositive : Cells.Disk 1).1‖ < 1 := by norm_num
  simp only [potential, dite_eq_left (edgeMap_mem_interior i edgePositive hv)]
  norm_num [edgePositive]

theorem monodromy_generator (g : Fin k → Q) (i : Fin k) (q : Q) :
    (covering (coveringCore g)).monodromy (Path.Homotopic.Quotient.mk (generatorLoop i))
      ⟨point (coveringCore g) none (basepoint k) q,rfl⟩ =
      ⟨point (coveringCore g) none (basepoint k) (g i * q),rfl⟩ := by
  let Z := coveringCore g
  have hn : point Z none (edgeMap i edgeNegative) q = point Z (some i) (edgeMap i edgeNegative) q := by
    have h := point_change Z none (some i)
      (edgeFirst_collar i (edgeFirst i).target_mem_range)
      (edgeMiddle_interior i (edgeMiddle i).source_mem_range) q
    simpa only [Z, coveringCore, transition, potential_none, potential_negative, inv_one,
      one_mul] using h
  have hp : point Z (some i) (edgeMap i edgePositive) q =
      point Z none (edgeMap i edgePositive) (g i * q) := by
    have h := point_change Z (some i) none
      (edgeMiddle_interior i (edgeMiddle i).target_mem_range)
      (edgeLast_collar i (edgeLast i).source_mem_range) q
    simpa only [Z, coveringCore, transition, potential_none, potential_positive, inv_inv,
      one_mul] using h
  have he : Path.Homotopic.Quotient.mk (generatorLoop i) =
      (Path.Homotopic.Quotient.mk (edgeFirst i)).trans
        ((Path.Homotopic.Quotient.mk (edgeMiddle i)).trans
          (Path.Homotopic.Quotient.mk (edgeLast i))) := by
    simp only [← Path.Homotopic.Quotient.mk_trans]
    exact Quotient.sound (edge_parts_homotopic i).symm
  rw [he]
  rw [IsCoveringMap.monodromy_trans_apply, monodromy_chartPath Z none _ (edgeFirst_collar i)]
  have hn' : (⟨point Z none (edgeMap i edgeNegative) q,rfl⟩ : Z.proj ⁻¹' {edgeMap i edgeNegative}) =
      ⟨point Z (some i) (edgeMap i edgeNegative) q,rfl⟩ := Subtype.ext hn
  rw [hn', IsCoveringMap.monodromy_trans_apply,
    monodromy_chartPath Z (some i) _ (edgeMiddle_interior i)]
  have hp' : (⟨point Z (some i) (edgeMap i edgePositive) q,rfl⟩ : Z.proj ⁻¹' {edgeMap i edgePositive}) =
      ⟨point Z none (edgeMap i edgePositive) (g i * q),rfl⟩ := Subtype.ext hp
  rw [hp', monodromy_chartPath Z none _ (edgeLast_collar i)]

end PresentationGeometry.Rose

end

end OAI
