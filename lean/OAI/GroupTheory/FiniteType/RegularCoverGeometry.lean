import Mathlib
import OAI.GroupTheory.FiniteType.PresentationGeometryCells
import OAI.GroupTheory.FiniteType.SphereCover

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval
open scoped unitInterval
open Set
namespace RegularCoverGeometry
open Set
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable {p : E → X} (cov : IsCoveringMap p) (e₀ : E)

theorem pathConnected_of_monodromy_transitive [PathConnectedSpace X]
    (h : Function.Surjective (fun γ : FundamentalGroup X (p e₀) =>
      cov.monodromy γ ⟨e₀,rfl⟩)) : PathConnectedSpace E := by
  have hj : ∀ e : E, Joined e₀ e := by
    intro e
    let γ : Path.Homotopic.Quotient (p e) (p e₀) :=
      .mk (PathConnectedSpace.somePath (p e) (p e₀))
    let e' : p ⁻¹' {p e₀} := cov.monodromy γ ⟨e,rfl⟩
    have he : Joined e e'.1 := ⟨(cov.liftPathQuotient γ ⟨e,rfl⟩).out⟩
    obtain ⟨δ,hδ⟩ := h e'
    have h₀ : Joined e₀ (cov.monodromy δ ⟨e₀,rfl⟩).1 :=
      ⟨(cov.liftPathQuotient δ ⟨e₀,rfl⟩).out⟩
    have h₀' : Joined e₀ e'.1 := (congrArg Subtype.val hδ) ▸ h₀
    exact h₀'.trans he.symm
  exact ⟨⟨e₀⟩,fun a b => (hj a).symm.trans (hj b)⟩

theorem simplyConnected_of_monodromy_bijective [PathConnectedSpace X]
    (h : Function.Bijective (fun γ : FundamentalGroup X (p e₀) =>
      cov.monodromy γ ⟨e₀,rfl⟩)) : SimplyConnectedSpace E := by
  let : PathConnectedSpace E := pathConnected_of_monodromy_transitive cov e₀ h.2
  let : Subsingleton (FundamentalGroup E e₀) := ⟨by
    intro a b
    apply cov.injective_path_homotopic_map e₀ e₀
    apply h.1
    exact (cov.monodromy_map a).trans (cov.monodromy_map b).symm⟩
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance,fun x γ => ?_⟩
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPathConnected e₀ x
  have : Subsingleton (FundamentalGroup E x) := e.symm.injective.subsingleton
  exact Path.Homotopic.Quotient.eq.mp
    (Subsingleton.elim (α := FundamentalGroup E x) (Path.Homotopic.Quotient.mk γ)
      (Path.Homotopic.Quotient.mk (Path.refl x)))

end RegularCoverGeometry

namespace CoveringMapNatural
open Set
variable {X Y E F : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace E] [TopologicalSpace F]
  {p : E → X} {q : F → Y} (cp : IsCoveringMap p) (cq : IsCoveringMap q)
  (f : C(X,Y)) (g : C(E,F)) (comm : q ∘ g = f ∘ p)

def fiberMap (x : X) : p ⁻¹' {x} → q ⁻¹' {f x} :=
  fun e => ⟨g e.1,(congrFun comm e.1).trans (congrArg f e.2)⟩

lemma natural {x y : X} (γ : Path.Homotopic.Quotient x y) (e : p ⁻¹' {x}) :
    cq.monodromy (γ.map f) (fiberMap f g comm x e) =
      fiberMap f g comm y (cp.monodromy γ e) := by
  apply cq.monodromy_eq_of_map_eq ((cp.liftPathQuotient γ e).map g)
  erw [← Path.Homotopic.Quotient.map_comp]
  have he : (⟨q,cq.continuous⟩ : C(F,Y)).comp g = f.comp ⟨p,cp.continuous⟩ :=
    ContinuousMap.ext (congrFun comm)
  apply eq_of_heq
  have hh : HEq ((cp.liftPathQuotient γ e).map ((⟨q,cq.continuous⟩ : C(F,Y)).comp g))
      ((cp.liftPathQuotient γ e).map (f.comp ⟨p,cp.continuous⟩)) := by rw [he]
  apply hh.trans
  erw [Path.Homotopic.Quotient.map_comp,cp.map_liftPathQuotient,
    Path.Homotopic.Quotient.map_cast]
  exact (Path.Homotopic.Quotient.cast_heq _ _).trans (Path.Homotopic.Quotient.cast_heq _ _).symm

lemma monodromy_point_bijective [SimplyConnectedSpace E] (e : E) :
    Function.Bijective (fun γ : FundamentalGroup X (p e) => cp.monodromy γ ⟨e,rfl⟩) := by
  constructor
  · intro γ δ h
    have hh : cp.liftPathQuotient γ ⟨e,rfl⟩ =
        (cp.liftPathQuotient δ ⟨e,rfl⟩).cast rfl (congrArg Subtype.val h) :=
      Subsingleton.elim _ _
    have hh' := congrArg (fun κ => κ.map (⟨p,cp.continuous⟩ : C(E,X))) hh
    erw [cp.map_liftPathQuotient,Path.Homotopic.Quotient.map_cast,
      cp.map_liftPathQuotient,Path.Homotopic.Quotient.cast_cast] at hh'
    exact eq_of_heq ((Path.Homotopic.Quotient.cast_heq _ _).symm.trans
      ((heq_of_eq hh').trans (Path.Homotopic.Quotient.cast_heq _ _)))
  · intro z
    let Γ : Path.Homotopic.Quotient e z.1 := .mk (PathConnectedSpace.somePath e z.1)
    refine ⟨(Γ.map ⟨p,cp.continuous⟩).cast rfl z.2.symm,?_⟩
    apply cp.monodromy_eq_of_map_eq Γ
    erw [Path.Homotopic.Quotient.cast_cast]
    exact eq_of_heq (Path.Homotopic.Quotient.cast_heq _ _).symm

include cp cq in
lemma fundamentalMap_injective [SimplyConnectedSpace E] (e : E)
    (hb : Function.Injective (fiberMap f g comm (p e))) :
    Function.Injective (FundamentalGroup.map f (p e)) := by
  intro γ δ h
  apply (monodromy_point_bijective cp e).1
  apply hb
  rw [← natural cp cq f g comm γ ⟨e,rfl⟩,← natural cp cq f g comm δ ⟨e,rfl⟩]
  exact congrArg (fun κ => cq.monodromy κ (fiberMap f g comm (p e) ⟨e,rfl⟩)) h

include cp cq in

theorem simplyConnected_of_old [PathConnectedSpace Y] [SimplyConnectedSpace E]
    (e : E) (hs : Function.Surjective (FundamentalGroup.map f (p e)))
    (hb : Function.Bijective (fiberMap f g comm (p e))) : SimplyConnectedSpace F := by
  apply RegularCoverGeometry.simplyConnected_of_monodromy_bijective cq (g e)
  have hbase : q (g e) = f (p e) := congrFun comm e
  let e' : q ⁻¹' {f (p e)} := fiberMap f g comm (p e) ⟨e,rfl⟩
  have hn (γ : FundamentalGroup X (p e)) :
      cq.monodromy (FundamentalGroup.map f (p e) γ) e' =
        fiberMap f g comm (p e) (cp.monodromy γ ⟨e,rfl⟩) :=
    natural cp cq f g comm γ ⟨e,rfl⟩
  have hm : Function.Bijective (fun γ : FundamentalGroup Y (f (p e)) => cq.monodromy γ e') := by
    constructor
    · intro α β h
      obtain ⟨γ,rfl⟩ := hs α
      obtain ⟨δ,rfl⟩ := hs β
      dsimp only at h
      rw [hn,hn] at h
      exact congrArg (FundamentalGroup.map f (p e))
        ((monodromy_point_bijective cp e).1 (hb.1 h))
    · intro z
      obtain ⟨w,rfl⟩ := hb.2 z
      obtain ⟨γ,rfl⟩ := (monodromy_point_bijective cp e).2 w
      exact ⟨FundamentalGroup.map f (p e) γ,hn γ⟩
  have transport {y : Y} (z : q ⁻¹' {y})
      (hz : Function.Bijective (fun γ : FundamentalGroup Y y => cq.monodromy γ z)) :
      Function.Bijective (fun γ : FundamentalGroup Y (q z.1) => cq.monodromy γ ⟨z.1,rfl⟩) := by
    obtain ⟨z,hz'⟩ := z
    change q z = y at hz'
    subst y
    exact hz
  exact transport e' hm

end CoveringMapNatural

namespace FiberCoreMap
open Set Topology DiscreteCoverCharts
variable {ι κ X Y Q : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Q]
  (Z : FiberBundleCore ι X Q) (W : FiberBundleCore κ Y Q)
  (f : C(X,Y)) (idx : ι → κ)
  (hs : ∀ i x, x ∈ Z.baseSet i → f x ∈ W.baseSet (idx i))
  (ht : ∀ i j x, x ∈ Z.baseSet i ∩ Z.baseSet j → ∀ q,
    W.coordChange (idx i) (idx j) (f x) q = Z.coordChange i j x q)

def map (e : Z.TotalSpace) : W.TotalSpace :=
  point W (idx (Z.indexAt e.1)) (f e.1) e.2

@[simp] lemma map_proj (e : Z.TotalSpace) : W.proj (map Z W f idx e) = f (Z.proj e) := rfl

include hs ht in
lemma map_chart (i : ι) (e : Z.TotalSpace) (he : e.1 ∈ Z.baseSet i) :
    map Z W f idx e = point W (idx i) (f e.1) ((Z.localTriv i) e).2 := by
  unfold map
  erw [point_change W (idx (Z.indexAt e.1)) (idx i)
    (hs _ _ (Z.mem_baseSet_at _)) (hs _ _ he),ht _ _ _ ⟨Z.mem_baseSet_at _,he⟩]
  rfl

include hs ht in
lemma continuous_map : Continuous (map Z W f idx) := by
  apply continuous_iff_continuousAt.mpr
  intro e
  let i := Z.indexAt e.1
  have he : e ∈ (Z.localTriv i).source := Z.mem_baseSet_at e.1
  have hc : ContinuousOn (fun a : Z.TotalSpace =>
      point W (idx i) (f a.1) ((Z.localTriv i) a).2) (Z.localTriv i).source := by
    apply (W.localTriv (idx i)).toOpenPartialHomeomorph.symm.continuousOn.comp
    · exact (f.continuous.comp Z.continuous_proj).continuousOn.prodMk
        (continuous_snd.comp_continuousOn (Z.localTriv i).continuousOn)
    · intro a ha
      exact (W.mem_localTriv_target (idx i) _).mpr (hs i a.1 ha)
  have hc' : ContinuousOn (map Z W f idx) (Z.localTriv i).source :=
    hc.congr (fun a ha => map_chart Z W f idx hs ht i a ha)
  exact hc'.continuousAt ((Z.localTriv i).open_source.mem_nhds he)

def continuousMap : C(Z.TotalSpace,W.TotalSpace) := ⟨map Z W f idx,continuous_map Z W f idx hs ht⟩

include hs ht in
lemma fiber_bijective (x : X) : Function.Bijective
    (fun z : Z.proj ⁻¹' {x} =>
      (⟨map Z W f idx z.1,(map_proj Z W f idx z.1).trans (congrArg f z.2)⟩ : W.proj ⁻¹' {f x})) := by
  let i := Z.indexAt x
  let e := fiberEquiv Z i x (Z.mem_baseSet_at x)
  let e' := fiberEquiv W (idx i) (f x) (hs i x (Z.mem_baseSet_at x))
  have he (z : Z.proj ⁻¹' {x}) :
      (⟨map Z W f idx z.1,(map_proj Z W f idx z.1).trans (congrArg f z.2)⟩ : W.proj ⁻¹' {f x}) =
        e' (e.symm z) := by
    obtain ⟨⟨y,q⟩,hy⟩ := z
    change y = x at hy
    subst y
    apply Subtype.ext
    exact map_chart Z W f idx hs ht i ⟨x,q⟩ (Z.mem_baseSet_at x)
  simpa only [he,Function.comp_def] using e'.bijective.comp e.symm.bijective
end FiberCoreMap

namespace PresentationGeometry.CellCoverExtension
open Set Cells
variable {X ι Q : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
  {k d : ℕ} (f : C(boundary k d,X)) (b : X) (Z : FiberBundleCore ι X Q)
  (pot : ι → X → Q) (s : C(boundary k d,Z.TotalSpace))
  (hs : ∀ c, Z.proj (s c) = f c)
  (hpot : ∀ i j x q, Z.coordChange i j x q = pot j x * (pot i x)⁻¹ * q)

def oldLift : C(Z.TotalSpace,(coveringCore f b Z pot s hs hpot).TotalSpace) :=
  FiberCoreMap.continuousMap Z (coveringCore f b Z pot s hs hpot)
    ⟨Adjunction.old f,Adjunction.continuous_old f⟩ Sum.inl
    (fun i x hx => (mem_coveringCore_old f b Z pot s hs hpot i x).mpr hx)
    (fun i j x _ q => coveringCore_old_coordChange f b Z pot s hs hpot i j x q)

@[simp] lemma oldLift_proj (e : Z.TotalSpace) :
    (coveringCore f b Z pot s hs hpot).proj (oldLift f b Z pot s hs hpot e) =
      Adjunction.old f (Z.proj e) := rfl

lemma oldLift_fiber_bijective (x : X) : Function.Bijective
    (CoveringMapNatural.fiberMap (p := Z.proj)
      (⟨Adjunction.old f,Adjunction.continuous_old f⟩ : C(X,Cells.Space f))
      (oldLift f b Z pot s hs hpot) (funext (oldLift_proj f b Z pot s hs hpot)) x) :=
  FiberCoreMap.fiber_bijective Z (coveringCore f b Z pot s hs hpot)
    ⟨Adjunction.old f,Adjunction.continuous_old f⟩ Sum.inl
    (fun i x hx => (mem_coveringCore_old f b Z pot s hs hpot i x).mpr hx)
    (fun i j x _ q => coveringCore_old_coordChange f b Z pot s hs hpot i j x q) x

theorem coveringCore_simplyConnected [SimplyConnectedSpace Z.TotalSpace] (hd : 1 < d) :
    SimplyConnectedSpace (coveringCore f b Z pot s hs hpot).TotalSpace := by
  let : PathConnectedSpace X := (show Function.Surjective Z.proj from
    fun x => ⟨⟨x,(1 : Q)⟩,rfl⟩).pathConnectedSpace Z.continuous_proj
  let : PathConnectedSpace (Cells.Space f) := Cells.pathConnectedSpace f (by omega)
  exact CoveringMapNatural.simplyConnected_of_old (FiberBundle.isCoveringMap (F := Q) (E := Z.Fiber))
    (coveringCore_isCoveringMap f b Z pot s hs hpot)
    ⟨Adjunction.old f,Adjunction.continuous_old f⟩ (oldLift f b Z pot s hs hpot)
    (funext (oldLift_proj f b Z pot s hs hpot)) ⟨b,(1 : Q)⟩
    (old_fundamentalGroupMap_surjective f hd b)
    (oldLift_fiber_bijective f b Z pot s hs hpot b)

include pot s hs hpot in
lemma fundamentalGroupMap_bijective [SimplyConnectedSpace Z.TotalSpace] (hd : 1 < d) :
    Function.Bijective (FundamentalGroup.map
      (⟨Adjunction.old f,Adjunction.continuous_old f⟩ : C(X,Cells.Space f)) b) :=
  ⟨CoveringMapNatural.fundamentalMap_injective (FiberBundle.isCoveringMap (F := Q) (E := Z.Fiber))
    (coveringCore_isCoveringMap f b Z pot s hs hpot)
    ⟨Adjunction.old f,Adjunction.continuous_old f⟩ (oldLift f b Z pot s hs hpot)
    (funext (oldLift_proj f b Z pot s hs hpot)) ⟨b,(1 : Q)⟩
    (oldLift_fiber_bijective f b Z pot s hs hpot b).1,
    old_fundamentalGroupMap_surjective f hd b⟩

end PresentationGeometry.CellCoverExtension

end

end OAI
