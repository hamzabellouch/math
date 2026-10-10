import Mathlib
import OAI.GroupTheory.FiniteType.SingularAction

namespace OAI

noncomputable section
namespace CoreDeck
open Set Topology DiscreteCoverCharts
variable {ι X Q : Type} [TopologicalSpace X] [Group Q] [TopologicalSpace Q]
  [DiscreteTopology Q] (Z : FiberBundleCore ι X Q)
  (hZ : ∀ i j x a q, Z.coordChange i j x (a*q) = Z.coordChange i j x a * q)

@[instance_reducible] def leftAction : MulAction Q Z.TotalSpace where
  smul q z := right Z q⁻¹ z
  one_smul z := by
    change right Z ((1:Q)⁻¹) z = z
    obtain ⟨x, a⟩ := z
    simp only [right, inv_one]
    exact congrArg (fun v : Q => (⟨x, v⟩ : Z.TotalSpace)) (@mul_one Q _ a)
  mul_smul p q z := by
    change right Z ((p*q)⁻¹) z = right Z p⁻¹ (right Z q⁻¹ z)
    obtain ⟨x, a⟩ := z
    simp only [right, mul_inv_rev]
    exact congrArg (fun v : Q => (⟨x, v⟩ : Z.TotalSpace)) (@mul_assoc Q _ a q⁻¹ p⁻¹).symm

include hZ in
theorem continuousLeftAction : @ContinuousConstSMul Q Z.TotalSpace _ (leftAction Z).toSMul := by
  let := leftAction Z
  exact ⟨fun q => continuous_right Z hZ q⁻¹⟩

omit [DiscreteTopology Q] in
lemma left_transitive (a b : Z.TotalSpace) (h : Z.proj a = Z.proj b) :
    ∃ q : Q, @SMul.smul Q Z.TotalSpace (leftAction Z).toSMul q a = b := by
  obtain ⟨q,hq⟩ := transitive_fiber Z a b h
  refine ⟨q⁻¹,?_⟩
  change right Z ((q⁻¹)⁻¹) a = b
  simpa only [inv_inv] using hq

omit [DiscreteTopology Q] in
lemma left_free (g h : Q) (a : Z.TotalSpace)
    (he : @SMul.smul Q Z.TotalSpace (leftAction Z).toSMul g a =
      @SMul.smul Q Z.TotalSpace (leftAction Z).toSMul h a) : g = h := by
  have hh := congrArg (fun z : Z.TotalSpace => (z.2 : Q)) he
  change @HMul.hMul Q Q Q _ a.2 g⁻¹ = @HMul.hMul Q Q Q _ a.2 h⁻¹ at hh
  exact inv_injective (mul_left_cancel hh)

end CoreDeck

namespace PresentationGeometry.CellCoverExtension
open Set Topology Cells CWExtension CategoryTheory CategoryTheory.Limits HomologicalComplex SingularChains
open HurewiczConstruction
variable {X ι Q : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
  {k n : ℕ} (f : C(boundary k (n+3),X)) (b : X) (Z : FiberBundleCore ι X Q)
  (pot : ι → X → Q) (s : C(boundary k (n+3),Z.TotalSpace))
  (hs : ∀ c, Z.proj (s c) = f c)
  (hpot : ∀ i j x q, Z.coordChange i j x q = pot j x * (pot i x)⁻¹ * q)
  [Nonempty X] [CWComplex (univ : Set X)] [RelCWComplex.FiniteType (univ : Set X)]
  (hdim : ∀ m, RelCWComplex.cell (univ : Set X) m → m < n+3)

include hdim in

lemma critical_homology_zero_left
    (hgen : letI := CoreDeck.leftAction Z
      letI := CoreDeck.continuousLeftAction Z (CoreDeck.of_potential Z pot hpot)
      Submodule.span (MonoidAlgebra ℤ Q)
        (Set.range (fun i : Fin k => sphereModuleClass (G:=Q) (n+2) (s.comp (boundarySlice i)))) = ⊤) :
    IsZero ((chains (coveringCore f b Z pot s hs hpot).TotalSpace).homology (n+2)) := by
  let := CoreDeck.leftAction Z
  let := CoreDeck.continuousLeftAction Z (CoreDeck.of_potential Z pot hpot)
  have hzero : (homologyMap (map (oldLift f b Z pot s hs hpot)) (n+2)).hom = 0 := by
    apply RepresentationKilling.eq_zero (homologyRep (G:=Q) (X:=Z.TotalSpace) (n+2))
      (homologyMap (map (oldLift f b Z pot s hs hpot)) (n+2)).hom
      (fun i : Fin k => sphereModuleClass (G:=Q) (n+2) (s.comp (boundarySlice i))) hgen
    intro q i
    have hk := deck_attaching_homology_killed f b Z pot s hs hpot rfl i q⁻¹ (n+2) (by omega)
    exact congrArg (fun a => a (SingularSphereCycle.fundamentalClass (n+2))) hk
  have hsur := oldLift_homology_surjective f b Z pot s hs hpot hdim (n+2) (by omega)
  let : Subsingleton ((chains (coveringCore f b Z pot s hs hpot).TotalSpace).homology (n+2)) := by
    constructor
    intro u v
    obtain ⟨u,rfl⟩ := hsur u
    obtain ⟨v,rfl⟩ := hsur v
    change (homologyMap (map (oldLift f b Z pot s hs hpot)) (n+2)).hom u =
      (homologyMap (map (oldLift f b Z pot s hs hpot)) (n+2)).hom v
    rw [hzero]
    rfl
  exact ModuleCat.isZero_of_subsingleton _

include hdim in

theorem coveringCore_connectivity_left [SimplyConnectedSpace Z.TotalSpace]
    (hπ : ∀ p ≤ n+1, ∀ z : Z.TotalSpace, Subsingleton (HomotopyGroup (Fin p) Z.TotalSpace z))
    (hgen : letI := CoreDeck.leftAction Z
      letI := CoreDeck.continuousLeftAction Z (CoreDeck.of_potential Z pot hpot)
      Submodule.span (MonoidAlgebra ℤ Q)
        (Set.range (fun i : Fin k => sphereModuleClass (G:=Q) (n+2) (s.comp (boundarySlice i)))) = ⊤) :
    ∀ p ≤ n+2, ∀ z : (coveringCore f b Z pot s hs hpot).TotalSpace,
      Subsingleton (HomotopyGroup (Fin p) (coveringCore f b Z pot s hs hpot).TotalSpace z) := by
  let := coveringCore_simplyConnected f b Z pot s hs hpot (by omega)
  apply homotopy_trivial_of_homology_zero (n+2)
  intro j hj hjn
  by_cases he : j = n+2
  · subst j
    exact critical_homology_zero_left f b Z pot s hs hpot hdim hgen
  · have hj1 : j ≤ n+1 := by omega
    have hOld : IsZero ((chains Z.TotalSpace).homology j) := by
      cases j with
      | zero => omega
      | succ j => exact homology_zero_of_homotopy (fun p hp z => hπ p (hp.trans hj1) z) ⟨b,(1:Q)⟩
    let := ModuleCat.isZero_iff_subsingleton.mp hOld
    let := (oldLift_homology_surjective f b Z pot s hs hpot hdim j (by omega)).subsingleton
    exact ModuleCat.isZero_of_subsingleton _
end PresentationGeometry.CellCoverExtension

namespace CoreDeck
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {ι X Q : Type} [TopologicalSpace X] [T2Space X]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
  (Z : FiberBundleCore ι X Q)
  (hZ : ∀ i j x a q, Z.coordChange i j x (a*q) = Z.coordChange i j x a * q)
  [CWComplex (univ : Set X)] [SimplyConnectedSpace Z.TotalSpace]

lemma critical_finite (n : ℕ) [Finite (RelCWComplex.cell (univ : Set X) (n+2))]
    (hπ : ∀ p ≤ n+1, ∀ z : Z.TotalSpace,
      Subsingleton (HomotopyGroup (Fin p) Z.TotalSpace z))
    (hzero : ∀ I : Type, IsZero (groupHomology (RegularProductR.rep ℤ Q I) (n+2))) :
    letI := leftAction Z
    letI := continuousLeftAction Z hZ
    Module.Finite (MonoidAlgebra ℤ Q)
      (HurewiczConstruction.homologyModule (G:=Q) (X:=Z.TotalSpace) (n+2)) := by
  let := leftAction Z
  let := continuousLeftAction Z hZ
  let : T2Space Z.TotalSpace := CoveringCellGeometry.hausdorff (DiscreteCoverCharts.covering Z)
  let : Fact (∀ (g : Q) (x : Z.TotalSpace), Z.proj (g • x) = Z.proj x) := ⟨fun _ _ => rfl⟩
  let : PathConnectedSpace (univ : Set Z.TotalSpace) :=
    isPathConnected_iff_pathConnectedSpace.mp isPathConnected_univ
  have hH (j : ℕ) (hj : 0 < j) (hjn : j < n+1+1) :
      IsZero ((SingularChains.chains (univ : Set Z.TotalSpace)).homology j) := by
    apply SingularAction.univ_homology_zero
    cases j with
    | zero => omega
    | succ j =>
      exact HurewiczConstruction.homology_zero_of_homotopy
        (fun p hp z => hπ p (by omega) z) (Classical.choice inferInstance)
  have : Module.Finite (MonoidAlgebra ℤ Q)
      (CWEquivariant.wholeRep (G:=Q) (X:=Z.TotalSpace) (n+2)).ρ.asModule :=
    EquivariantCoverCells.homology_finite (left_free Z) (left_transitive Z)
      (fun x => ⟨⟨x,(1:Q)⟩,rfl⟩) (DiscreteCoverCharts.covering Z) (n+1) hH hzero
  exact SingularAction.finite_of_univ (G:=Q) (X:=Z.TotalSpace) (n+2)
attribute [instance] AddCommGroup.toIntModule
end CoreDeck

namespace PresentationVanKampen
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X]

theorem rectangle_homotopic (H : C(I × I, X)) :
    (((Path.id.map (continuous_const.prodMk continuous_id)).map H.continuous).trans
      ((Path.id.map (continuous_id.prodMk continuous_const)).map H.continuous) :
      Path (H (0,0)) (H (1,1))).Homotopic
    (((Path.id.map (continuous_id.prodMk continuous_const)).map H.continuous).trans
      ((Path.id.map (continuous_const.prodMk continuous_id)).map H.continuous) :
      Path (H (0,0)) (H (1,1))) := by
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  have h := SimplyConnectedSpace.paths_homotopic
    ((Path.id.map (continuous_const.prodMk continuous_id) : Path ((0 : I), (0 : I)) (0,1)).trans
      (Path.id.map (continuous_id.prodMk continuous_const) : Path ((0 : I), (1 : I)) (1,1)))
    ((Path.id.map (continuous_id.prodMk continuous_const) : Path ((0 : I), (0 : I)) (1,0)).trans
      (Path.id.map (continuous_const.prodMk continuous_id) : Path ((1 : I), (0 : I)) (1,1)))
  simpa only [Path.map_trans] using h.map H

end PresentationVanKampen

namespace PresentationGeometry.Rose
section
open scoped unitInterval

variable {k : ℕ}

def edgeMap (i : Fin k) : C(Cells.Disk 1, Space k) :=
  ⟨fun v => Adjunction.disk (attaching k) (i,v),
    (Adjunction.continuous_disk (attaching k)).comp (continuous_const.prodMk continuous_id)⟩

def edgeLeft : Cells.Disk 1 := ⟨fun _ => -1, by simp [Metric.mem_closedBall]⟩
def edgeRight : Cells.Disk 1 := ⟨fun _ => 1, by simp [Metric.mem_closedBall]⟩

@[simp] theorem edgeMap_left (i : Fin k) : edgeMap i edgeLeft = basepoint k := by
  exact Adjunction.disk_boundary (attaching k) ⟨(i,edgeLeft), by simp [Cells.boundary, edgeLeft]⟩

@[simp] theorem edgeMap_right (i : Fin k) : edgeMap i edgeRight = basepoint k := by
  exact Adjunction.disk_boundary (attaching k) ⟨(i,edgeRight), by simp [Cells.boundary, edgeRight]⟩

instance disk_contractible (d : ℕ) : ContractibleSpace (Cells.Disk d) :=
  (convex_closedBall (0 : Fin d → ℝ) 1).contractibleSpace
    ⟨0, Metric.mem_closedBall_self (by norm_num)⟩

def edgeInterval (u v : Cells.Disk 1) : Path u v where
  toFun t := ⟨Path.segment u.1 v.1 t,
    (convex_closedBall (0 : Fin 1 → ℝ) 1).segment_subset u.property v.property
      ((Path.range_segment u.1 v.1) ▸ (show Path.segment u.1 v.1 t ∈ Set.range (Path.segment u.1 v.1) from ⟨t,rfl⟩))⟩
  continuous_toFun := (Path.segment u.1 v.1).continuous.subtype_mk _
  source' := Subtype.ext (Path.segment u.1 v.1).source
  target' := Subtype.ext (Path.segment u.1 v.1).target

def edgeSpoke (i : Fin k) (v : Cells.Disk 1) : Path (basepoint k) (edgeMap i v) :=
  ((edgeInterval edgeLeft v).map (edgeMap i).continuous).cast (edgeMap_left i).symm rfl

@[simp] theorem edgeSpoke_left (i : Fin k) :
    (edgeSpoke i edgeLeft).cast rfl (edgeMap_left i).symm = Path.refl (basepoint k) := by
  have h : edgeInterval edgeLeft edgeLeft = Path.refl edgeLeft := by
    ext t j
    simp [edgeInterval]
  ext t
  change edgeMap i (edgeInterval edgeLeft edgeLeft t) = basepoint k
  rw [h]
  exact edgeMap_left i

@[simp] theorem edgeSpoke_right (i : Fin k) :
    (edgeSpoke i edgeRight).cast rfl (edgeMap_right i).symm = generatorLoop i := by
  ext t
  change Adjunction.disk (attaching k)
    (i, ⟨Path.segment edgeLeft.1 edgeRight.1 t, _⟩) =
    Cells.characteristic (attaching k) i (Path.segment _ _ t)
  exact (Cells.characteristic_on_disk (attaching k) i _).symm

def pointCode (a : Space k) : Point ⊕ (Fin k × Cells.Disk 1) :=
  Quotient.lift (Adjunction.normalize (attaching k)) (fun _ _ h => h) a

@[simp] theorem pointCode_base : pointCode (basepoint k) = Sum.inl PUnit.unit := rfl

@[simp] theorem pointCode_edge (i : Fin k) (v : Cells.Disk 1)
    (hv : ‖v.1‖ < 1) : pointCode (edgeMap i v) = Sum.inr (i,v) := by
  exact Adjunction.normalize_inr_notMem (attaching k) (i,v)
    (by simpa [Cells.boundary, mem_sphere_zero_iff_norm] using (ne_of_lt hv))

theorem pointCode_cases (a : Space k) :
    (pointCode a = Sum.inl PUnit.unit ∧ a = basepoint k) ∨
    ∃ (i : Fin k) (v : Cells.Disk 1), ‖v.1‖ < 1 ∧
      pointCode a = Sum.inr (i,v) ∧ a = edgeMap i v := by
  obtain ⟨x | ⟨i,v⟩, rfl⟩ := Quotient.mk_surjective a
  · exact Or.inl ⟨rfl, rfl⟩
  · by_cases h : (i,v) ∈ Cells.boundary k 1
    · left
      have he := Adjunction.disk_boundary (attaching k) ⟨(i,v), h⟩
      change Adjunction.disk (attaching k) (i,v) = basepoint k at he
      rw [show Quotient.mk (Adjunction.relation (attaching k)) (Sum.inr (i,v)) =
        basepoint k from he]
      exact ⟨rfl,rfl⟩
    · have hv : ‖v.1‖ < 1 := lt_of_le_of_ne (mem_closedBall_zero_iff.mp v.property)
        (by simpa [Cells.boundary, mem_sphere_zero_iff_norm] using h)
      exact Or.inr ⟨i,v,hv,pointCode_edge i v hv,rfl⟩

def edgeData (a : {a : Space k // a ≠ basepoint k}) : Fin k × Cells.Disk 1 :=
  let h := (pointCode_cases a.1).resolve_left (fun h => a.2 h.2)
  (h.choose, h.choose_spec.choose)

theorem edgeData_spec (a : {a : Space k // a ≠ basepoint k}) :
    ‖(edgeData a).2.1‖ < 1 ∧ pointCode a.1 = Sum.inr (edgeData a) ∧
      a.1 = edgeMap (edgeData a).1 (edgeData a).2 := by
  exact ((pointCode_cases a.1).resolve_left (fun h => a.2 h.2)).choose_spec.choose_spec

def spoke (a : Space k) : Path (basepoint k) a := by
  classical
  exact if ha : a = basepoint k then (Path.refl (basepoint k)).cast rfl ha
    else (edgeSpoke (edgeData ⟨a,ha⟩).1 (edgeData ⟨a,ha⟩).2).cast rfl
      (edgeData_spec ⟨a,ha⟩).2.2

@[simp] theorem spoke_base : spoke (basepoint k) = Path.refl (basepoint k) := by
  simp [spoke]

theorem spoke_edge (i : Fin k) (v : Cells.Disk 1) (hv : ‖v.1‖ < 1) :
    spoke (edgeMap i v) = edgeSpoke i v := by
  classical
  have hn : edgeMap i v ≠ basepoint k := by
    intro he
    have := congrArg pointCode he
    rw [pointCode_edge i v hv, pointCode_base] at this
    cases this
  have he : edgeData ⟨edgeMap i v,hn⟩ = (i,v) := by
    have hc := (edgeData_spec ⟨edgeMap i v,hn⟩).2.1
    rw [pointCode_edge i v hv] at hc
    exact (Sum.inr.inj hc).symm
  simp only [spoke, dite_eq_right hn]
  ext t
  change edgeMap (edgeData ⟨edgeMap i v,hn⟩).1
    (edgeInterval edgeLeft (edgeData ⟨edgeMap i v,hn⟩).2 t) = edgeMap i (edgeInterval edgeLeft v t)
  rw [he]

end

open scoped unitInterval
open PresentationVanKampen

variable {k : ℕ}

theorem basedPathClass_edge {u v : Cells.Disk 1} (i : Fin k)
    (hu : ‖u.1‖ < 1) (hv : ‖v.1‖ < 1) (q : Path u v) :
    basedPathClass (basepoint k) spoke (q.map (edgeMap i).continuous) = 1 := by
  have h := (SimplyConnectedSpace.paths_homotopic
    ((edgeInterval edgeLeft u).trans q) (edgeInterval edgeLeft v)).map (edgeMap i)
  have h' : ((edgeSpoke i u).trans (q.map (edgeMap i).continuous)).Homotopic
      (edgeSpoke i v) := by
    simpa only [Path.map_trans, Path.cast_trans, Path.cast_rfl_rfl, edgeSpoke] using
      h.pathCast (edgeMap_left i).symm rfl
  have he : (Path.Homotopic.Quotient.mk ((edgeSpoke i u).trans
    (q.map (edgeMap i).continuous))) = Path.Homotopic.Quotient.mk (edgeSpoke i v) :=
      Quotient.sound h'
  simp only [basedPathClass, spoke_edge i u hu, spoke_edge i v hv,
    ← Path.Homotopic.Quotient.trans_assoc, ← Path.Homotopic.Quotient.mk_trans]
  rw [he, Path.Homotopic.Quotient.trans_symm]
  rfl

def openEdgeLift (i : Fin k) : C(Cells.cellInterior (attaching k) i, Cells.Disk 1) :=
  ⟨fun x => Cells.interiorInDisk
    ((Cells.characteristic_isOpenEmbedding (attaching k) i).isEmbedding.toHomeomorph.symm x),
    Cells.interiorInDisk_isOpenEmbedding.continuous.comp
      (Cells.characteristic_isOpenEmbedding (attaching k) i).isEmbedding.toHomeomorph.symm.continuous⟩

@[simp] theorem edgeMap_openEdgeLift (i : Fin k)
    (a : Cells.cellInterior (attaching k) i) : edgeMap i (openEdgeLift i a) = a.1 := by
  have h := congrArg Subtype.val
    ((Cells.characteristic_isOpenEmbedding (attaching k) i).isEmbedding.toHomeomorph.apply_symm_apply a)
  change Adjunction.disk (attaching k) (i, openEdgeLift i a) = a.1
  rw [← Cells.characteristic_on_disk (attaching k) i]
  exact h

theorem norm_openEdgeLift (i : Fin k) (a : Cells.cellInterior (attaching k) i) :
    ‖(openEdgeLift i a).1‖ < 1 :=
  mem_ball_zero_iff.mp
    ((Cells.characteristic_isOpenEmbedding (attaching k) i).isEmbedding.toHomeomorph.symm a).property

theorem basedPathClass_interior {a c : Space k} (p : Path a c) (i : Fin k)
    (hp : Set.range p ⊆ Cells.cellInterior (attaching k) i) :
    basedPathClass (basepoint k) spoke p = 1 := by
  let a' : Cells.cellInterior (attaching k) i := ⟨a, hp p.source_mem_range⟩
  let c' : Cells.cellInterior (attaching k) i := ⟨c, hp p.target_mem_range⟩
  let q := (pathIn p hp).map (openEdgeLift i).continuous
  have h := basedPathClass_edge i (norm_openEdgeLift i a') (norm_openEdgeLift i c') q
  have ha := edgeMap_openEdgeLift i a'
  have hc := edgeMap_openEdgeLift i c'
  have hcast : ∀ {a c a' c' : Space k} (q : Path a c) (ha : a' = a) (hc : c' = c),
      basedPathClass (basepoint k) spoke (q.cast ha hc) =
        basedPathClass (basepoint k) spoke q := by
    intro a c a' c' q ha hc
    subst a'; subst c'
    rfl
  rw [← hcast _ ha.symm hc.symm] at h
  have he : (q.map (edgeMap i).continuous).cast ha.symm hc.symm = p := by
    ext t
    exact edgeMap_openEdgeLift i ((pathIn p hp) t)
  rwa [he] at h

end PresentationGeometry.Rose

end

end OAI
