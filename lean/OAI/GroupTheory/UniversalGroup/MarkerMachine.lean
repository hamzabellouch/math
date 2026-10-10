import OAI.GroupTheory.UniversalGroup.Markers

namespace OAI

universe u v w x

namespace Higman.FreeBasis

section
variable {X : Type*}

noncomputable def erase (S : Set X) : FreeGroup X →* FreeGroup X := by
  classical
  exact FreeGroup.lift (fun x ↦ if x ∈ S then FreeGroup.of x else 1)

open Classical in
@[simp] theorem erase_of (S : Set X) (x : X) : erase S (FreeGroup.of x) =
    if x ∈ S then FreeGroup.of x else 1 := by
  classical
  simp [erase]

abbrev span (S : Set X) : Subgroup (FreeGroup X) := Subgroup.closure (FreeGroup.of '' S)

theorem erase_eq_self_iff (S : Set X) (g : FreeGroup X) : erase S g = g ↔ g ∈ span S := by
  classical
  constructor
  · intro hg
    have hle : (erase S).range ≤ span S := by
      rw [erase,FreeGroup.range_lift_eq_closure]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨x,rfl⟩
      by_cases hx : x ∈ S
      · simp only [hx,ite_true]
        exact Subgroup.subset_closure ⟨x,hx,rfl⟩
      · simp only [hx,ite_false]
        exact Subgroup.one_mem _
    exact hle ⟨g,hg⟩
  · have hle : span S ≤ (erase S).eqLocus (MonoidHom.id _) := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨x,hx,rfl⟩
      change erase S (FreeGroup.of x) = FreeGroup.of x
      simp [hx]
    exact fun hg ↦ hle hg

theorem erase_comp (S T : Set X) : (erase S).comp (erase T) = erase (S ∩ T) := by
  classical
  apply FreeGroup.ext_hom
  intro x
  by_cases hxS : x ∈ S <;> by_cases hxT : x ∈ T <;> simp [hxS,hxT]

theorem span_inter (S T : Set X) : span S ⊓ span T = span (S ∩ T) := by
  apply le_antisymm
  · intro g hg
    apply (erase_eq_self_iff _ _).mp
    rw [← erase_comp]
    change erase S (erase T g) = g
    rw [(erase_eq_self_iff T g).mpr hg.2,(erase_eq_self_iff S g).mpr hg.1]
  · exact le_inf (Subgroup.closure_mono (Set.image_mono Set.inter_subset_left))
      (Subgroup.closure_mono (Set.image_mono Set.inter_subset_right))

theorem of_mem_span_iff (S : Set X) (x : X) : FreeGroup.of x ∈ span S ↔ x ∈ S := by
  classical
  constructor
  · intro h
    by_contra hx
    have he := (erase_eq_self_iff S (FreeGroup.of x)).mpr h
    simp only [erase_of,hx,ite_false] at he
    exact FreeGroup.of_ne_one x he.symm
  · intro hx
    exact Subgroup.subset_closure ⟨x,hx,rfl⟩

end

variable {X : Type*} {G : Type*} [Group G]

theorem map_span_inf (d : FreeGroup X →* G) (r : G →* FreeGroup X)
    (hr : r.comp d = MonoidHom.id _) (U V : Set X) (A : Subgroup G)
    (hsupport : A.map r ≤ span U)
    (hletters : ∀ x ∈ U, d (FreeGroup.of x) ∈ A) :
    (span V).map d ⊓ A = (span (V ∩ U)).map d := by
  apply le_antisymm
  · rintro g ⟨⟨w,hw,rfl⟩,hA⟩
    refine ⟨w,?_,rfl⟩
    rw [← span_inter]
    refine ⟨hw,?_⟩
    have hh := hsupport (Subgroup.mem_map.mpr ⟨d w,hA,rfl⟩)
    change w ∈ span U
    simpa only [← MonoidHom.comp_apply,hr,MonoidHom.id_apply] using hh
  · apply le_inf
    · exact Subgroup.map_mono (Subgroup.closure_mono (Set.image_mono Set.inter_subset_left))
    · rw [span,MonoidHom.map_closure]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact hletters x hx.2

end Higman.FreeBasis

namespace Higman.DecoratedMarker
open Monoid Coprod
variable {G : Type u} [Group G] {T : Type v} [Group T] {Q : Type w}

theorem eq_inclusion_of_right_eq_one (x : Base G T Q) (hx : (test x).right = 1) :
    x = inclusion (test x).left := by
  apply (decomposition (G := G) (T := T) (Q := Q)).injective
  change test x = test (inclusion (test x).left)
  rw [← MonoidHom.comp_apply,test_comp]
  apply SemidirectProduct.ext
  · rfl
  · exact hx

end Higman.DecoratedMarker

namespace Higman.MarkerEmbedding

section
open Monoid Coprod DecoratedMarker
variable {G : Type u} [Group G] {D : Type v} [Group D]
    {T : Type w} [Group T] {P Q : Type*}

@[simp] theorem test_embedding (f : D →* T) (o : P → T) (q : P → Q)
    (w : P → G) (x : Base G D P) :
    test (embedding f o q w x) =
      SemidirectProduct.map (kernelMap f o q w) f (kernelMap_shift f o q w) (test x) := by
  change (test.comp inverse) _ = _
  rw [test_comp_inverse]
  rfl

@[simp] theorem embedding_inclusion (f : D →* T) (o : P → T) (q : P → Q)
    (w : P → G) (x : Kernel G D P) :
    embedding f o q w (inclusion x) = inclusion (kernelMap f o q w x) := by
  simp only [embedding,MonoidHom.comp_apply]
  rw [← MonoidHom.comp_apply (test : Base G D P →* _),test_comp]
  simp

theorem kernel_intersection (f : D →* T) (hf : Function.Injective f)
    (o : P → T) (q : P → Q) (w : P → G) (R : Subgroup (Kernel G T Q)) :
    R.map inclusion ⊓ (embedding f o q w).range =
      (R ⊓ (kernelMap f o q w).range).map inclusion := by
  apply le_antisymm
  · rintro _ ⟨⟨a,ha,rfl⟩,⟨x,hx⟩⟩
    have hxright : (test x).right = 1 := by
      apply hf
      have he := congrArg (fun y : Base G T Q ↦ (test y).right) hx
      simp only [test_embedding,SemidirectProduct.map_right] at he
      rw [← MonoidHom.comp_apply,test_comp] at he
      simpa only [SemidirectProduct.right_inl,map_one] using he
    have hx' := eq_inclusion_of_right_eq_one x hxright
    refine ⟨a,⟨ha,?_⟩,rfl⟩
    refine ⟨(test x).left,?_⟩
    apply inclusion_injective
    rw [← embedding_inclusion,← hx']
    exact hx
  · rintro _ ⟨a,⟨ha,⟨x,hx⟩⟩,rfl⟩
    refine ⟨⟨a,ha,rfl⟩,inclusion x,?_⟩
    rw [embedding_inclusion,hx]

lemma projection_kernelMap (f : D →* T) (o : P → T) (q : P → Q) (w : P → G) :
    (Coprod.snd : Kernel G T Q →* FreeGroup (T × Q)).comp (kernelMap f o q w) =
      (FreeGroup.map (index f o q)).comp (Coprod.snd : Kernel G D P →* _) := by
  apply Coprod.hom_ext
  · apply MonoidHom.ext
    intro g
    simp
  · apply FreeGroup.ext_hom
    intro x
    simp

lemma range_projection_support (f : D →* T) (o : P → T) (q : P → Q) (w : P → G) :
    (kernelMap f o q w).range.map Coprod.snd ≤ FreeBasis.span (Set.range (index f o q)) := by
  rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
  have he := DFunLike.congr_fun (projection_kernelMap f o q w) x
  change Coprod.snd (kernelMap f o q w x) ∈ FreeBasis.span (Set.range (index f o q))
  rw [show Coprod.snd (kernelMap f o q w x) = FreeGroup.map (index f o q) (Coprod.snd x) from he]
  have hm : FreeGroup.map (index f o q) (Coprod.snd x) ∈ (FreeGroup.map (index f o q)).range :=
    ⟨Coprod.snd x,rfl⟩
  simpa only [FreeGroup.range_map,FreeBasis.span] using hm

lemma decorated_letter_mem_range (f : D →* T) (o : P → T) (q : P → Q) (w : P → G)
    (v : T × Q → G) (x : T × Q) (hx : x ∈ Set.range (index f o q)) :
    DecoratedFreeBasis.inclusion v (FreeGroup.of x) ∈ (kernelMap f o q w).range := by
  obtain ⟨⟨d,p⟩,rfl⟩ := hx
  refine ⟨inl (v (index f o q (d,p)) * (w p)⁻¹) * inr (FreeGroup.of (d,p)),?_⟩
  simp [mul_assoc]

theorem decorated_kernel_intersection (f : D →* T) (o : P → T) (q : P → Q)
    (w : P → G) (v : T × Q → G) (V : Set (T × Q)) :
    (FreeBasis.span V).map (DecoratedFreeBasis.inclusion v) ⊓ (kernelMap f o q w).range =
      (FreeBasis.span (V ∩ Set.range (index f o q))).map (DecoratedFreeBasis.inclusion v) :=
  FreeBasis.map_span_inf (DecoratedFreeBasis.inclusion v) Coprod.snd
    (DecoratedFreeBasis.projection_comp v) (Set.range (index f o q)) V _
    (range_projection_support f o q w) (decorated_letter_mem_range f o q w v)

def decoratedSubgroup (v : T × Q → G) (V : Set (T × Q)) : Subgroup (Base G T Q) :=
  (FreeBasis.span V).map (inclusion.comp (DecoratedFreeBasis.inclusion v))

theorem decorated_intersection (f : D →* T) (hf : Function.Injective f)
    (o : P → T) (q : P → Q) (w : P → G) (v : T × Q → G) (V : Set (T × Q)) :
    decoratedSubgroup v V ⊓ (embedding f o q w).range =
      decoratedSubgroup v (V ∩ Set.range (index f o q)) := by
  rw [decoratedSubgroup,← Subgroup.map_map,kernel_intersection f hf o q w,
    decorated_kernel_intersection,Subgroup.map_map]
  rfl

theorem decoratedSubgroup_eq_closure (v : T × Q → G) (V : Set (T × Q)) :
    decoratedSubgroup v V =
      Subgroup.closure ((fun x : T × Q ↦ coefficient (v x) * marker x.1 x.2) '' V) := by
  rw [decoratedSubgroup,FreeBasis.span,MonoidHom.map_closure,Set.image_image]
  congr 1

end

open DecoratedMarker
variable {G : Type u} [Group G] {T : Type v} [Group T] {Q : Type w}
  {D : Type*} [Group D] {P : Type*}

def pullDecoration (f : D →* T) (o : P → T) (q : P → Q) (w : P → G)
    (v : T × Q → G) (x : D × P) : G := v (index f o q x) * (w x.2)⁻¹

@[simp] lemma embedding_decorated (f : D →* T) (o : P → T) (q : P → Q) (w : P → G)
    (v : T × Q → G) (x : D × P) :
    embedding f o q w (coefficient (pullDecoration f o q w v x) * marker x.1 x.2) =
      coefficient (v (index f o q x)) * marker (index f o q x).1 (index f o q x).2 := by
  rw [map_mul,embedding_coefficient,embedding_marker,← mul_assoc,← map_mul]
  simp [pullDecoration,index]

lemma map_decoratedSubgroup (f : D →* T) (o : P → T) (q : P → Q) (w : P → G)
    (v : T × Q → G) (W : Set (D × P)) :
    (decoratedSubgroup (pullDecoration f o q w v) W).map (embedding f o q w) =
      decoratedSubgroup v (index f o q '' W) := by
  rw [decoratedSubgroup_eq_closure,MonoidHom.map_closure,decoratedSubgroup_eq_closure]
  simp only [Set.image_image,embedding_decorated]

theorem comap_decoratedSubgroup [Nonempty P] (f : D →* T) (hf : Function.Injective f)
    (o : P → T) (q : P → Q) (w : P → G) (hi : Function.Injective (index f o q))
    (v : T × Q → G) (V : Set (T × Q)) :
    (decoratedSubgroup v V).comap (embedding f o q w) =
      decoratedSubgroup (pullDecoration f o q w v) (index f o q ⁻¹' V) := by
  apply Subgroup.map_injective (embedding_injective f hf o q w hi)
  rw [Subgroup.map_comap_eq,inf_comm,decorated_intersection f hf,
    map_decoratedSubgroup,Set.image_preimage_eq_inter_range]

end Higman.MarkerEmbedding

namespace Higman.PartialIso
variable {H : Type u} [Group H] {G : Type u} [Group G]

noncomputable def ofEmbeddings (i j : H →* G) (hi : Function.Injective i)
    (hj : Function.Injective j) : PartialIso G where
  source := i.range
  target := j.range
  equiv := (MonoidHom.ofInjective hi).symm.trans (MonoidHom.ofInjective hj)

@[simp] theorem ofEmbeddings_apply (i j : H →* G) (hi : Function.Injective i)
    (hj : Function.Injective j) (x : H) :
    ((ofEmbeddings i j hi hj).equiv (MonoidHom.ofInjective hi x) : G) = j x := by
  change j ((MonoidHom.ofInjective hi).symm ((MonoidHom.ofInjective hi) x)) = j x
  rw [MulEquiv.symm_apply_apply]

lemma ofEmbeddings_invariant_iff (i j : H →* G) (hi : Function.Injective i)
    (hj : Function.Injective j) (R : Subgroup G) :
    (ofEmbeddings i j hi hj).Invariant R ↔ R.comap i = R.comap j := by
  constructor
  · intro h
    ext x
    simpa only [ofEmbeddings_apply,MonoidHom.ofInjective_apply,Subgroup.mem_comap] using
      (h (MonoidHom.ofInjective hi x)).symm
  · intro h a
    obtain ⟨x,rfl⟩ := (MonoidHom.ofInjective hi).surjective a
    rw [ofEmbeddings_apply]
    change x ∈ R.comap j ↔ x ∈ R.comap i
    rw [h]

end Higman.PartialIso
namespace Higman.MarkerMachine
open DecoratedMarker MarkerEmbedding

structure Edge (G T : Type u) [Group G] [Group T] (Q : Type u) where
  Domain : Type u
  [domainGroup : Group Domain]
  inputLinear : Domain →* T
  outputLinear : Domain →* T
  input_injective : Function.Injective inputLinear
  output_injective : Function.Injective outputLinear
  inputOffset : T
  outputOffset : T
  inputState : Q
  outputState : Q
  weight : G

attribute [instance] Edge.domainGroup
variable {G T Q : Type u} [Group G] [Group T]

namespace Edge
variable (e : Edge G T Q)

def input (d : e.Domain) : T × Q := (e.inputLinear d * e.inputOffset,e.inputState)
def output (d : e.Domain) : T × Q := (e.outputLinear d * e.outputOffset,e.outputState)

def inputMap : Base G e.Domain Unit →* Base G T Q :=
  embedding e.inputLinear (fun _ ↦ e.inputOffset) (fun _ ↦ e.inputState) (fun _ ↦ 1)
def outputMap : Base G e.Domain Unit →* Base G T Q :=
  embedding e.outputLinear (fun _ ↦ e.outputOffset) (fun _ ↦ e.outputState) (fun _ ↦ e.weight)

lemma input_index_injective : Function.Injective
    (index e.inputLinear (fun _ : Unit ↦ e.inputOffset) (fun _ ↦ e.inputState)) :=
  index_injective e.inputLinear e.input_injective _ _ (Function.injective_of_subsingleton _)
lemma output_index_injective : Function.Injective
    (index e.outputLinear (fun _ : Unit ↦ e.outputOffset) (fun _ ↦ e.outputState)) :=
  index_injective e.outputLinear e.output_injective _ _ (Function.injective_of_subsingleton _)

lemma inputMap_injective : Function.Injective e.inputMap :=
  embedding_injective e.inputLinear e.input_injective _ _ _ e.input_index_injective
lemma outputMap_injective : Function.Injective e.outputMap :=
  embedding_injective e.outputLinear e.output_injective _ _ _ e.output_index_injective

noncomputable def partialIso : PartialIso (Base G T Q) :=
  PartialIso.ofEmbeddings e.inputMap e.outputMap e.inputMap_injective e.outputMap_injective

lemma inputMap_decorated (v : G) (d : e.Domain) :
    e.inputMap (coefficient v * marker d ()) =
      coefficient v * marker (e.input d).1 (e.input d).2 := by
  simp [inputMap,input]

lemma outputMap_decorated (v : G) (d : e.Domain) :
    e.outputMap (coefficient v * marker d ()) =
      coefficient (v * e.weight) * marker (e.output d).1 (e.output d).2 := by
  simp [outputMap,output,map_mul,mul_assoc]

end Edge
end Higman.MarkerMachine

namespace Higman.MarkerEmbedding
open DecoratedMarker
variable {G : Type u} [Group G] {T : Type v} [Group T] {Q : Type w}

lemma decoratedSubgroup_congr {v w : T × Q → G} {V : Set (T × Q)}
    (h : ∀ x ∈ V, v x = w x) : decoratedSubgroup v V = decoratedSubgroup w V := by
  rw [decoratedSubgroup_eq_closure,decoratedSubgroup_eq_closure]
  congr 1
  apply Set.image_congr
  intro x hx
  rw [h x hx]

end Higman.MarkerEmbedding
namespace Higman.MarkerMachine.Edge
open DecoratedMarker MarkerEmbedding
variable {G T Q : Type u} [Group G] [Group T] (e : Edge G T Q)

theorem invariant (v : T × Q → G) (V : Set (T × Q))
    (hV : ∀ d, e.input d ∈ V ↔ e.output d ∈ V)
    (hv : ∀ d, e.input d ∈ V → v (e.output d) = v (e.input d) * e.weight) :
    e.partialIso.Invariant (decoratedSubgroup v V) := by
  rw [partialIso,PartialIso.ofEmbeddings_invariant_iff]
  unfold inputMap outputMap
  rw [comap_decoratedSubgroup e.inputLinear e.input_injective _ _ _ e.input_index_injective,
    comap_decoratedSubgroup e.outputLinear e.output_injective _ _ _ e.output_index_injective]
  have he : index e.inputLinear (fun _ : Unit ↦ e.inputOffset) (fun _ ↦ e.inputState) ⁻¹' V =
      index e.outputLinear (fun _ : Unit ↦ e.outputOffset) (fun _ ↦ e.outputState) ⁻¹' V := by
    ext x
    exact hV x.1
  rw [← he]
  apply decoratedSubgroup_congr
  rintro ⟨d,p⟩ hd
  change v (e.input d) * (1 : G)⁻¹ = v (e.output d) * e.weight⁻¹
  change e.input d ∈ V at hd
  rw [hv d hd]
  simp

lemma invariant_decorated_iff (R : Subgroup (Base G T Q)) (hR : e.partialIso.Invariant R)
    (a : G) (d : e.Domain) :
    coefficient (a * e.weight) * marker (e.output d).1 (e.output d).2 ∈ R ↔
      coefficient a * marker (e.input d).1 (e.input d).2 ∈ R := by
  have hh := hR (MonoidHom.ofInjective e.inputMap_injective (coefficient a * marker d ()))
  change ((PartialIso.ofEmbeddings e.inputMap e.outputMap _ _).equiv
    (MonoidHom.ofInjective e.inputMap_injective (coefficient a * marker d ())) :
    Base G T Q) ∈ R ↔ _ at hh
  simpa only [PartialIso.ofEmbeddings_apply,MonoidHom.ofInjective_apply,
    inputMap_decorated,outputMap_decorated] using hh

lemma source_fg [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented e.Domain] :
    e.partialIso.source.FG := by
  have : Group.IsFinitelyPresented (G × e.Domain) := finitelyPresented_prod
  obtain ⟨n,p,hp,_⟩ := Group.IsFinitelyPresented.out (G := Base G e.Domain Unit)
  have : Group.FG (Base G e.Domain Unit) := Group.fg_of_surjective hp
  exact (Group.fg_iff_subgroup_fg e.inputMap.range).mp inferInstance

end Higman.MarkerMachine.Edge

namespace Higman.MarkerMachine
open DecoratedMarker MarkerEmbedding
variable {G T Q : Type u} [Group G] [Group T]

inductive Reach (es : List (Edge G T Q)) (seed : T × Q) : T × Q → Prop
  | start : Reach es seed seed
  | forward (e : Edge G T Q) (he : e ∈ es) (d : e.Domain) :
      Reach es seed (e.input d) → Reach es seed (e.output d)
  | backward (e : Edge G T Q) (he : e ∈ es) (d : e.Domain) :
      Reach es seed (e.output d) → Reach es seed (e.input d)

lemma reach_iff (es : List (Edge G T Q)) (seed : T × Q) (e : Edge G T Q) (he : e ∈ es)
    (d : e.Domain) : Reach es seed (e.input d) ↔ Reach es seed (e.output d) :=
  ⟨Reach.forward e he d,Reach.backward e he d⟩

def word (v : T × Q → G) (c : T × Q) : Base G T Q :=
  coefficient (v c) * marker c.1 c.2

theorem orbit_eq (es : List (Edge G T Q)) (seed : T × Q) (v : T × Q → G)
    (hv : ∀ e ∈ es, ∀ d, Reach es seed (e.input d) →
      v (e.output d) = v (e.input d) * e.weight) :
    Orbit.subgroup (es.map Edge.partialIso) {word v seed} =
      decoratedSubgroup v {c | Reach es seed c} := by
  apply le_antisymm
  · apply Orbit.minimal
    · rintro x (rfl : x = word v seed)
      rw [decoratedSubgroup_eq_closure]
      exact Subgroup.subset_closure ⟨seed,Reach.start,rfl⟩
    · intro p hp
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
      exact e.invariant v _ (reach_iff es seed e he) (hv e he)
  · rw [decoratedSubgroup_eq_closure]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨c,hc,rfl⟩
    change word v c ∈ Orbit.subgroup (es.map Edge.partialIso) {word v seed}
    induction hc with
    | start => exact Orbit.subset _ _ (Set.mem_singleton _)
    | forward e he d hr ih =>
      have hinv := Orbit.invariant (es.map Edge.partialIso) {word v seed} e.partialIso
        (List.mem_map.mpr ⟨e,he,rfl⟩)
      change coefficient (v (e.output d)) * marker (e.output d).1 (e.output d).2 ∈ _
      rw [hv e he d hr]
      exact (e.invariant_decorated_iff _ hinv (v (e.input d)) d).mpr ih
    | backward e he d hr ih =>
      have hinv := Orbit.invariant (es.map Edge.partialIso) {word v seed} e.partialIso
        (List.mem_map.mpr ⟨e,he,rfl⟩)
      apply (e.invariant_decorated_iff _ hinv (v (e.input d)) d).mp
      rw [← hv e he d (Reach.backward e he d hr)]
      exact ih

theorem benign [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented T] [Finite Q]
    (es : List (Edge G T Q)) (hD : ∀ e ∈ es, Group.IsFinitelyPresented e.Domain)
    (seed : T × Q) (v : T × Q → G)
    (hv : ∀ e ∈ es, ∀ d, Reach es seed (e.input d) →
      v (e.output d) = v (e.input d) * e.weight) :
    IsBenign (decoratedSubgroup v {c | Reach es seed c}) := by
  have : Group.IsFinitelyPresented (G × T) := finitelyPresented_prod
  rw [← orbit_eq es seed v hv]
  apply Orbit.benign _ _ _ (Set.finite_singleton _)
  intro p hp
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
  have := hD e he
  exact e.source_fg

end Higman.MarkerMachine

end OAI
