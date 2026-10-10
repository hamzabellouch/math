import Mathlib
import OAI.GroupTheory.FiniteType.RegularCoverGeometry

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval
open scoped unitInterval
open Set
namespace FiberCoreMap
open Set Topology DiscreteCoverCharts
variable {ι κ X Y Q : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Q]
  (Z : FiberBundleCore ι X Q) (W : FiberBundleCore κ Y Q)
  (f : C(X,Y)) (idx : ι → κ)
  (hs : ∀ i x, x ∈ Z.baseSet i → f x ∈ W.baseSet (idx i))
  (ht : ∀ i j x, x ∈ Z.baseSet i ∩ Z.baseSet j → ∀ q,
    W.coordChange (idx i) (idx j) (f x) q = Z.coordChange i j x q)

include hs ht in
lemma map_injective (hf : Function.Injective f) : Function.Injective (map Z W f idx) := by
  intro a b h
  have hx : Z.proj a = Z.proj b := hf (congrArg W.proj h)
  have hh := @(fiber_bijective Z W f idx hs ht (Z.proj a)).1
    ⟨a,rfl⟩ ⟨b,hx.symm⟩ (Subtype.ext h)
  exact congrArg Subtype.val hh

include hs ht in

lemma isEmbedding (hf : IsEmbedding f) : IsEmbedding (map Z W f idx) := by
  let e := Equiv.ofInjective (map Z W f idx) (map_injective Z W f idx hs ht hf.injective)
  let R := Set.range (map Z W f idx)
  have hp (r : R) : W.proj r.1 ∈ Set.range f := by
    obtain ⟨a,ha⟩ := r.2
    exact ⟨Z.proj a,congrArg W.proj ha⟩
  let rb : C(R,Set.range f) :=
    ⟨fun r => ⟨W.proj r.1,hp r⟩,
      (W.continuous_proj.comp continuous_subtype_val).subtype_mk hp⟩
  let B : C(R,X) := (⟨hf.toHomeomorph.symm,hf.toHomeomorph.symm.continuous⟩ : C(Set.range f,X)).comp rb
  have hmap (r : R) : map Z W f idx (e.symm r) = r.1 :=
    congrArg Subtype.val (e.apply_symm_apply r)
  have hfr (r : R) : f (B r) = W.proj r.1 :=
    congrArg Subtype.val (hf.toHomeomorph.apply_symm_apply (rb r))
  have hB (r : R) : Z.proj (e.symm r) = B r := by
    apply hf.injective
    exact (congrArg W.proj (hmap r)).trans (hfr r).symm
  have hi : Continuous e.symm := by
    apply continuous_iff_continuousAt.mpr
    intro r
    let i := Z.indexAt (B r)
    let U : Set R := B ⁻¹' Z.baseSet i
    have hr : r ∈ U := Z.mem_baseSet_at (B r)
    have hU : IsOpen U := (Z.isOpen_baseSet i).preimage B.continuous
    have hW (r : R) (hr : r ∈ U) : (r.1 : W.TotalSpace) ∈ (W.localTriv (idx i)).source := by
      rw [← hmap r]
      exact hs i _ (by change Z.proj (e.symm r) ∈ Z.baseSet i; rw [hB]; exact hr)
    have hEq (r : R) (hr : r ∈ U) : e.symm r =
        point Z i (B r) ((W.localTriv (idx i)) r.1).2 := by
      have hz : Z.proj (e.symm r) ∈ Z.baseSet i := by rw [hB]; exact hr
      have hw : f (Z.proj (e.symm r)) ∈ W.baseSet (idx i) := hs i _ hz
      have hm := map_chart Z W f idx hs ht i (e.symm r) hz
      rw [hmap] at hm
      have hc := congrArg (fun a => ((W.localTriv (idx i)) a).2) hm
      have ht' := (fiberEquiv W (idx i) (f (Z.proj (e.symm r))) hw).left_inv
        ((Z.localTriv i) (e.symm r)).2
      change ((W.localTriv (idx i)) (point W (idx i) (f (Z.proj (e.symm r)))
        ((Z.localTriv i) (e.symm r)).2)).2 = _ at ht'
      rw [ht'] at hc
      rw [hc,← hB]
      exact congrArg Subtype.val ((fiberEquiv Z i (Z.proj (e.symm r)) hz).right_inv ⟨e.symm r,rfl⟩) |>.symm
    have hc : ContinuousOn (fun r : R => point Z i (B r) ((W.localTriv (idx i)) r.1).2) U := by
      apply (Z.localTriv i).toOpenPartialHomeomorph.symm.continuousOn.comp
      · exact B.continuous.continuousOn.prodMk (continuous_snd.comp_continuousOn
          ((W.localTriv (idx i)).continuousOn.comp continuous_subtype_val.continuousOn hW))
      · intro r hr
        exact (Z.mem_localTriv_target i _).mpr hr
    exact (hc.congr hEq).continuousAt (hU.mem_nhds hr)
  let h : Z.TotalSpace ≃ₜ R :=
    { e with
      continuous_toFun := (continuous_map Z W f idx hs ht).subtype_mk _
      continuous_invFun := hi }
  exact IsEmbedding.subtypeVal.comp h.isEmbedding
end FiberCoreMap

open Set Topology unitInterval

namespace CoveringCellGeometry
section
variable {X E A : Type*} [TopologicalSpace X] [TopologicalSpace E]
  [TopologicalSpace A] {p : E → X} (cov : IsCoveringMap p)

abbrev Pullback (f : C(A,X)) := {z : A × E // p z.2 = f z.1}

variable (H : C(I × A,X))

def endpoint (t : I) : C(A,X) := H.comp ⟨fun a => (t,a),continuous_const.prodMk continuous_id⟩

def reverse : C(I × A,X) := H.comp ⟨fun z => (σ z.1,z.2),
  (unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd⟩

@[simp] theorem reverse_apply (t : I) (a : A) : reverse H (t,a) = H (σ t,a) := rfl

@[simp] theorem reverse_reverse : reverse (reverse H) = H := by
  ext ⟨t,a⟩
  simp [reverse,unitInterval.symm_symm]

def familyLift : C(I × Pullback (p := p) (endpoint H 0),E) :=
  cov.liftHomotopy
    (H.comp ⟨fun z => (z.1,z.2.1.1),continuous_fst.prodMk
      (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))⟩)
    ⟨fun z => z.1.2,continuous_snd.comp continuous_subtype_val⟩
    (fun z => z.2.symm)

theorem familyLift_proj (t : I) (z : Pullback (p := p) (endpoint H 0)) :
    p (familyLift cov H (t,z)) = H (t,z.1.1) :=
  congr_fun (cov.liftHomotopy_lifts _ _ _) (t,z)

@[simp] theorem familyLift_zero (z : Pullback (p := p) (endpoint H 0)) :
    familyLift cov H (0,z) = z.1.2 := cov.liftHomotopy_zero _ _ _ z

def transport : C(Pullback (p := p) (endpoint H 0),Pullback (p := p) (endpoint H 1)) where
  toFun z := ⟨(z.1.1,familyLift cov H (1,z)),familyLift_proj cov H 1 z⟩
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((familyLift cov H).continuous.comp (continuous_const.prodMk continuous_id)) |>.subtype_mk _

def backLift : C(I × Pullback (p := p) (endpoint H 1),E) :=
  cov.liftHomotopy
    ((reverse H).comp ⟨fun z => (z.1,z.2.1.1),continuous_fst.prodMk
      (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))⟩)
    ⟨fun z => z.1.2,continuous_snd.comp continuous_subtype_val⟩
    (fun z => by
      change H (σ 0,z.1.1) = p z.1.2
      rw [unitInterval.symm_zero]
      exact z.2.symm)

theorem backLift_proj (t : I) (z : Pullback (p := p) (endpoint H 1)) :
    p (backLift cov H (t,z)) = H (σ t,z.1.1) :=
  congr_fun (cov.liftHomotopy_lifts _ _ _) (t,z)

@[simp] theorem backLift_zero (z : Pullback (p := p) (endpoint H 1)) :
    backLift cov H (0,z) = z.1.2 := cov.liftHomotopy_zero _ _ _ z

theorem backLift_one_proj (z : Pullback (p := p) (endpoint H 1)) :
    p (backLift cov H (1,z)) = endpoint H 0 z.1.1 := by
  exact (backLift_proj cov H 1 z).trans
    (congrArg (fun t => H (t,z.1.1)) unitInterval.symm_one)

def backTransport : C(Pullback (p := p) (endpoint H 1),Pullback (p := p) (endpoint H 0)) where
  toFun z := ⟨(z.1.1,backLift cov H (1,z)),backLift_one_proj cov H z⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      ((backLift cov H).continuous.comp (continuous_const.prodMk continuous_id))

@[simp] theorem back_transport (z : Pullback (p := p) (endpoint H 0)) :
    backTransport cov H (transport cov H z) = z := by
  have heq : (fun t : I => backLift cov H (t,transport cov H z)) =
      (fun t : I => familyLift cov H (σ t,z)) := by
    refine cov.eq_of_comp_eq
      ((backLift cov H).continuous.comp (continuous_id.prodMk continuous_const))
      ((familyLift cov H).continuous.comp (unitInterval.continuous_symm.prodMk continuous_const)) ?_ 0 ?_
    · funext t
      simp only [Function.comp_apply,backLift_proj,familyLift_proj]
      rfl
    · simp [transport]
  apply Subtype.ext
  change (z.1.1,backLift cov H (1,transport cov H z)) = (z.1.1,z.1.2)
  apply Prod.ext
  · rfl
  · have hh := congr_fun heq 1
    simpa only [unitInterval.symm_one,familyLift_zero] using hh

@[simp] theorem transport_back (z : Pullback (p := p) (endpoint H 1)) :
    transport cov H (backTransport cov H z) = z := by
  have heq : (fun t : I => familyLift cov H (t,backTransport cov H z)) =
      (fun t : I => backLift cov H (σ t,z)) := by
    refine cov.eq_of_comp_eq
      ((familyLift cov H).continuous.comp (continuous_id.prodMk continuous_const))
      ((backLift cov H).continuous.comp (unitInterval.continuous_symm.prodMk continuous_const)) ?_ 0 ?_
    · funext t
      simp only [Function.comp_apply,backLift_proj,familyLift_proj,unitInterval.symm_symm]
      rfl
    · simp [backTransport]
  apply Subtype.ext
  change (z.1.1,familyLift cov H (1,backTransport cov H z)) = (z.1.1,z.1.2)
  apply Prod.ext
  · rfl
  · have hh := congr_fun heq 1
    simpa only [unitInterval.symm_one,backLift_zero] using hh

def transportHomeomorph : Pullback (p := p) (endpoint H 0) ≃ₜ
    Pullback (p := p) (endpoint H 1) where
  toFun := transport cov H
  invFun := backTransport cov H
  left_inv := back_transport cov H
  right_inv := transport_back cov H
  continuous_toFun := (transport cov H).continuous
  continuous_invFun := (backTransport cov H).continuous

@[simp] theorem transportHomeomorph_fst (z : Pullback (p := p) (endpoint H 0)) :
    (transportHomeomorph cov H z).1.1 = z.1.1 := rfl

end

section
open Set Topology unitInterval
variable {X E A : Type*} [TopologicalSpace X] [TopologicalSpace E]
  [TopologicalSpace A] {p : E → X} (cov : IsCoveringMap p)

def pullbackCongr {f g : C(A,X)} (h : f = g) :
    Pullback (p := p) f ≃ₜ Pullback (p := p) g := by
  subst g
  exact Homeomorph.refl _

@[simp] theorem pullbackCongr_val {f g : C(A,X)} (h : f = g) (z : Pullback (p := p) f) :
    (pullbackCongr h z).1 = z.1 := by subst g; rfl

def constantPullback (x : X) : A × (p ⁻¹' {x}) ≃ₜ Pullback (p := p) (.const A x) where
  toFun z := ⟨(z.1,z.2.1),z.2.2⟩
  invFun z := (z.1.1,⟨z.1.2,z.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

variable [ContractibleSpace A]

def contractionPoint (A : Type*) [TopologicalSpace A] [ContractibleSpace A] : A :=
  (id_nullhomotopic A).choose

def contraction (A : Type*) [TopologicalSpace A] [ContractibleSpace A] :
    (ContinuousMap.const A (contractionPoint A)).Homotopy (ContinuousMap.id A) :=
  (id_nullhomotopic A).choose_spec.some.symm

variable (f : C(A,X))

def contractionImage : C(I × A,X) := f.comp (contraction A).toContinuousMap

@[simp] theorem contractionImage_zero : endpoint (contractionImage f) 0 =
    ContinuousMap.const A (f (contractionPoint A)) := by
  ext a
  exact congrArg f ((contraction A).apply_zero a)

@[simp] theorem contractionImage_one : endpoint (contractionImage f) 1 = f := by
  ext a
  exact congrArg f ((contraction A).apply_one a)

def pullbackTrivialization : A × (p ⁻¹' {f (contractionPoint A)}) ≃ₜ Pullback (p := p) f :=
  (constantPullback (p := p) (A := A) (f (contractionPoint A))).trans
    ((pullbackCongr (contractionImage_zero f).symm).trans
      ((transportHomeomorph cov (contractionImage f)).trans
        (pullbackCongr (contractionImage_one f))))

@[simp] theorem pullbackTrivialization_fst (z : A × (p ⁻¹' {f (contractionPoint A)})) :
    (pullbackTrivialization cov f z).1.1 = z.1 := by
  simp only [pullbackTrivialization,Homeomorph.trans_apply,pullbackCongr_val,transportHomeomorph_fst]
  rfl

@[simp] theorem pullbackTrivialization_symm_fst (z : Pullback (p := p) f) :
    ((pullbackTrivialization cov f).symm z).1 = z.1.1 := by
  have h := pullbackTrivialization_fst cov f ((pullbackTrivialization cov f).symm z)
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

def characteristicLift (j : p ⁻¹' {f (contractionPoint A)}) : C(A,E) where
  toFun a := (pullbackTrivialization cov f (a,j)).1.2
  continuous_toFun := continuous_snd.comp (continuous_subtype_val.comp
    ((pullbackTrivialization cov f).continuous.comp (continuous_id.prodMk continuous_const)))

theorem characteristicLift_proj (j : p ⁻¹' {f (contractionPoint A)}) (a : A) :
    p (characteristicLift cov f j a) = f a := by
  exact (pullbackTrivialization cov f (a,j)).2.trans
    (congrArg f (pullbackTrivialization_fst cov f (a,j)))

def sheet : C(Pullback (p := p) f,p ⁻¹' {f (contractionPoint A)}) :=
  ⟨fun z => ((pullbackTrivialization cov f).symm z).2,
    continuous_snd.comp (pullbackTrivialization cov f).symm.continuous⟩

@[simp] theorem characteristicLift_sheet (z : Pullback (p := p) f) :
    characteristicLift cov f (sheet cov f z) z.1.1 = z.1.2 := by
  have hpair : (z.1.1,sheet cov f z) = (pullbackTrivialization cov f).symm z := by
    apply Prod.ext
    · exact (pullbackTrivialization_symm_fst cov f z).symm
    · rfl
  change (pullbackTrivialization cov f (z.1.1,sheet cov f z)).1.2 = z.1.2
  rw [hpair,Homeomorph.apply_symm_apply]

@[simp] theorem sheet_characteristicLift (j : p ⁻¹' {f (contractionPoint A)}) (a : A) :
    sheet cov f ⟨(a,characteristicLift cov f j a),characteristicLift_proj cov f j a⟩ = j := by
  have hpb : (⟨(a,characteristicLift cov f j a),characteristicLift_proj cov f j a⟩ :
      Pullback (p := p) f) = pullbackTrivialization cov f (a,j) := by
    apply Subtype.ext
    exact Prod.ext (pullbackTrivialization_fst cov f (a,j)).symm rfl
  change ((pullbackTrivialization cov f).symm _).2 = j
  rw [hpb,Homeomorph.symm_apply_apply]

theorem characteristicLift_fiber_injective (a : A) :
    Function.Injective (fun j => characteristicLift cov f j a) := by
  intro j k h
  have he : (⟨(a,characteristicLift cov f j a),characteristicLift_proj cov f j a⟩ :
      Pullback (p := p) f) =
      ⟨(a,characteristicLift cov f k a),characteristicLift_proj cov f k a⟩ := by
    apply Subtype.ext
    exact Prod.ext rfl h
  have hh := congrArg (sheet cov f) he
  simpa only [sheet_characteristicLift] using hh

end

open Set
variable {X E A B : Type} [TopologicalSpace X] [TopologicalSpace E]
  [TopologicalSpace A] [TopologicalSpace B] [ContractibleSpace A] [PreconnectedSpace B]
  {p : E → X} (cov : IsCoveringMap p) (f : C(A,X)) (i : C(B,A))
  (s : C(B,E)) (hs : p ∘ s = f ∘ i) (b : B)

include cov hs b in

theorem exists_extension : ∃ L : C(A,E), p ∘ L = f ∧ L.comp i = s := by
  let j := sheet cov f ⟨(i b,s b),congrFun hs b⟩
  let L := characteristicLift cov f j
  refine ⟨L,funext (characteristicLift_proj cov f j),?_⟩
  apply DFunLike.coe_injective
  refine cov.eq_of_comp_eq (L.comp i).continuous s.continuous ?_ b ?_
  · funext z
    exact (characteristicLift_proj cov f j (i z)).trans (congrFun hs z).symm
  · exact characteristicLift_sheet cov f ⟨(i b,s b),congrFun hs b⟩

include cov hs b in
lemma boundary_nullhomotopic : ∃ e : E, s.Homotopic (ContinuousMap.const B e) := by
  obtain ⟨L,_,hL⟩ := exists_extension cov f i s hs b
  obtain ⟨a,⟨H⟩⟩ := id_nullhomotopic A
  refine ⟨L a,?_⟩
  rw [← hL]
  exact ⟨(ContinuousMap.Homotopy.refl L).comp (H.comp (ContinuousMap.Homotopy.refl i))⟩

end CoveringCellGeometry

end

end OAI
