import OAI.GroupTheory.Hyperbolic.Spheres

namespace OAI

namespace Release075
open Equiv PermCycles

/-- Unlike an ordinary filling, this records *every* connected component.
The only nontriangular interior faces allowed are isolated two-dart spheres,
created when an exterior cancellable pair is folded. -/
structure FullFilling {E V : Type} (flip : E → E) (color : E → V)
    (face : E → E → E → Prop) (w : List E) where
  Dart : Type
  [dartFintype : Fintype Dart]
  reverse : Perm Dart
  next : Perm Dart
  reverse_involutive : Function.Involutive reverse
  reverse_ne : ∀ a, reverse a ≠ a
  label : Dart → E
  reverse_label : ∀ a, label (reverse a) = flip (label a)
  color_next : ∀ a, color (label ((reverse*next) a)) = color (label a)
  planar : PlanarMap reverse next
  boundary : List Dart
  boundary_cycle : IsBoundary next boundary
  boundary_word : boundary.map label = w
  cells : ∀ a, a ∉ boundary →
    ((next^3) a = a ∧ next a ≠ a ∧ face (label a) (label (next a)) (label ((next^2) a))) ∨
      (next a = reverse a ∧ (next^2) a = a)

attribute [instance] FullFilling.dartFintype

theorem IsBoundary.of_injective_map {A B : Type*} {f : Perm A} {g : Perm B}
    {l : List B} {e : B → A} (he : Function.Injective e) (hg : ∀ b, e (g b) = f (e b))
    (h : IsBoundary f (l.map e)) : IsBoundary g l := by
  classical
  refine ⟨h.1.of_map _,?_⟩
  intro b hb
  apply he
  rw [hg,h.2 _ (List.mem_map.mpr ⟨b,hb,rfl⟩)]
  exact formPerm_embedding ⟨e,he⟩ l b

namespace TriangleFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Discarding components disjoint from the outer face makes an ordinary
filling into a full filling, with no exceptional faces. -/
noncomputable abbrev full {w : List E} (D : TriangleFilling flip color face w) :
    FullFilling flip color face w where
  Dart := D.ActiveDart
  reverse := D.activeReverse
  next := D.activeNext
  reverse_involutive := D.activeReverse_involutive
  reverse_ne := D.activeReverse_ne
  label a := D.label a.val
  reverse_label a := D.reverse_label a.val
  color_next a := D.color_next a.val
  planar := D.active_planar
  boundary := D.boundary.pmap (fun a h => ⟨a,D.active_of_mem h⟩) (fun _ h => h)
  boundary_cycle := by
    apply IsBoundary.of_injective_map (f := D.next) Subtype.val_injective (fun _ => rfl)
    simpa only [List.map_pmap,List.pmap_eq_map,List.map_id_fun',id_eq] using D.boundary_cycle
  boundary_word := by simpa only [List.map_pmap,List.pmap_eq_map] using D.boundary_word
  cells := by
    intro a ha
    have hn : a.val ∉ D.boundary := by
      intro h
      apply ha
      exact List.mem_pmap.mpr ⟨a.val,h,rfl⟩
    have ht := D.triangular a.val a.property hn
    exact Or.inl ⟨Subtype.ext ht.1,fun he => ht.2.1 (congrArg Subtype.val he),ht.2.2⟩

end TriangleFilling

namespace FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable {w : List E} (D : FullFilling flip color face w)

def Bigon (a : D.Dart) : Prop := D.next a = D.reverse a ∧ (D.next^2) a = a

theorem bigon_reverse (a : D.Dart) : D.Bigon (D.reverse a) ↔ D.Bigon a := by
  have step (a : D.Dart) (h : D.Bigon a) : D.Bigon (D.reverse a) := by
    have hna : D.next (D.reverse a) = a := by
      rw [← h.1]
      exact h.2
    exact ⟨hna.trans (D.reverse_involutive a).symm,by
      simp only [pow_two,Perm.mul_apply,hna,h.1]⟩
  exact ⟨fun h => D.reverse_involutive a ▸ step _ h,step _⟩

theorem bigon_next (a : D.Dart) : D.Bigon (D.next a) ↔ D.Bigon a := by
  constructor
  · intro h
    have hna : D.next a = D.reverse a := by
      have h2 : D.next (D.next a) = a := D.next.injective h.2
      have hh : D.reverse (D.next a) = a := h.1.symm.trans h2
      exact (D.reverse_involutive (D.next a)).symm.trans (congrArg D.reverse hh)
    exact ⟨hna,D.next.injective h.2⟩
  · intro h
    rw [h.1]
    exact (D.bigon_reverse a).mpr h

/-- Integral corner evaluation, with the outer face omitted. -/
noncomputable def trace (F : E → E → E → M) : M :=
  ∑ a, if a ∈ D.boundary then 0 else
    F (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))

noncomputable abbrev rotate (n : ℕ) : FullFilling flip color face (w.rotate n) where
  Dart := D.Dart
  reverse := D.reverse
  next := D.next
  reverse_involutive := D.reverse_involutive
  reverse_ne := D.reverse_ne
  label := D.label
  reverse_label := D.reverse_label
  color_next := D.color_next
  planar := D.planar
  boundary := D.boundary.rotate n
  boundary_cycle := D.boundary_cycle.rotate n
  boundary_word := by rw [List.map_rotate,D.boundary_word]
  cells := by intro a ha; exact D.cells a (by simpa only [List.mem_rotate] using ha)

theorem trace_rotate (n : ℕ) (F : E → E → E → M) : (D.rotate n).trace F = D.trace F := by
  unfold trace
  dsimp only [rotate]
  simp only [List.mem_rotate]

noncomputable abbrev mirror (hflip : Function.Involutive flip)
    (hface : ∀ a b c, face a b c → face (flip a) (flip c) (flip b)) :
    FullFilling flip color face (w.reverse.map flip) where
  Dart := D.Dart
  reverse := D.reverse
  next := D.next⁻¹
  reverse_involutive := D.reverse_involutive
  reverse_ne := D.reverse_ne
  label := flip ∘ D.label
  reverse_label := by intro a; simp only [Function.comp_apply,D.reverse_label]
  color_next := by
    intro a
    simp only [Function.comp_apply,Perm.mul_apply,D.reverse_label]
    rw [hflip]
    have h := D.color_next (D.next⁻¹ a)
    simpa only [Perm.mul_apply,perm_apply_inv,D.reverse_label] using h.symm
  planar := D.planar.inv_right D.reverse_involutive
  boundary := D.boundary.reverse
  boundary_cycle := D.boundary_cycle.reverse
  boundary_word := by rw [← List.map_map,List.map_reverse,D.boundary_word]
  cells := by
    intro a hn
    rcases D.cells a (by simpa only [List.mem_reverse] using hn) with ht | hb
    · have he := inv_cycle_three D.next ht.1
      refine Or.inl ⟨he.2.2,?_,?_⟩
      · intro h
        apply ht.2.1
        have hh := congrArg D.next h
        simpa only [perm_apply_inv] using hh.symm
      · simp only [Function.comp_apply,he.1,he.2.1]
        exact hface _ _ _ ht.2.2
    · have he : D.next⁻¹ a = D.next a := by
        apply D.next.injective
        simpa only [perm_apply_inv,pow_two,Perm.mul_apply] using hb.2.symm
      refine Or.inr ⟨he.trans hb.1,?_⟩
      rw [pow_two,Perm.mul_apply,he]
      exact D.next.symm_apply_apply a

theorem trace_mirror (hflip : Function.Involutive flip)
    (hface : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (F : E → E → E → M)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c)
    (hdeg : ∀ a b, F a b a = 0) :
    (D.mirror hflip hface).trace F = - D.trace F := by
  rw [trace,trace,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [mirror,Function.comp_apply]
  by_cases ha : a ∈ D.boundary
  · simp only [List.mem_reverse,ha,ite_true,neg_zero]
  simp only [List.mem_reverse,ha,ite_false]
  rcases D.cells a ha with ht | hb
  · have he := inv_cycle_three D.next ht.1
    rw [he.1,he.2.1]
    exact hmir _ _ _ ht.2.2
  · have he : ((D.next⁻¹)^2) a = a := by
      rw [inv_pow]
      apply (D.next^2).injective
      simpa only [perm_apply_inv,pow_two,Perm.mul_apply] using hb.2.symm
    rw [he,hb.2,hdeg,hdeg,neg_zero]

end FullFilling
end Release075

namespace Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- A closed full filling is a disjoint union of triangular spheres and the
explicit isolated bigons. Consequently its integral cyclic evaluation vanishes. -/
theorem trace_empty
    (hempty : ∀ D : TriangleSphere flip color face, IsEmpty D.Dipole → IsEmpty D.Dart)
    (F : E → E → E → M)
    (hrot : ∀ a b c, face a b c → F b c a = F a b c)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c)
    (hdeg : ∀ a b, F a b a = 0)
    (D : FullFilling flip color face []) : D.trace F = 0 := by
  have hb : D.boundary = [] := List.map_eq_nil_iff.mp D.boundary_word
  let hr : ∀ a, ¬D.Bigon (D.reverse a) ↔ ¬D.Bigon a := fun a => not_congr (D.bigon_reverse a)
  let hf : ∀ a, ¬D.Bigon (D.next a) ↔ ¬D.Bigon a := fun a => not_congr (D.bigon_next a)
  let S : TriangleSphere flip color face := {
    Dart := {a : D.Dart // ¬D.Bigon a}
    reverse := D.reverse.subtypePerm hr
    next := D.next.subtypePerm hf
    reverse_involutive := fun a => Subtype.ext (D.reverse_involutive a.val)
    reverse_ne := fun a h => D.reverse_ne a.val (congrArg Subtype.val h)
    label := D.label ∘ Subtype.val
    reverse_label := fun a => D.reverse_label a.val
    color_next := fun a => D.color_next a.val
    planar := by
      simpa only [PlanarMap,← Nat.card_eq_fintype_card] using
        D.planar.restrict (fun a => ¬D.Bigon a) hr hf
    triangular := by
      intro a
      have ht := (D.cells a.val (by simp [hb])).resolve_right a.property
      exact ⟨Subtype.ext ht.1,fun h => ht.2.1 (congrArg Subtype.val h),ht.2.2⟩ }
  have hz := TriangleSphere.cornerSum_eq_zero hempty F hrot hmir S
  let f : D.Dart → M := fun a => F (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))
  have hpart := (Equiv.sumCompl D.Bigon).sum_comp f
  have hsum : (∑ a : {a : D.Dart // D.Bigon a}, f a.val) +
      (∑ a : {a : D.Dart // ¬D.Bigon a}, f a.val) = ∑ a, f a := by
    simpa only [Fintype.sum_sum_type,Equiv.sumCompl_apply_inl,Equiv.sumCompl_apply_inr] using hpart
  have hbig : (∑ a : {a : D.Dart // D.Bigon a}, f a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    dsimp only [f]
    rw [a.property.2,hdeg]
  have htri : (∑ a : {a : D.Dart // ¬D.Bigon a}, f a.val) = 0 := hz
  rw [hbig,htri,zero_add] at hsum
  simpa only [trace,hb,List.not_mem_nil,ite_false] using hsum.symm

end Release075.FullFilling

namespace Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

omit [AddCommGroup M] in
theorem bigon_component {w : List E} (D : FullFilling flip color face w)
    {a b : D.Dart} (ha : D.Bigon a) (h : components D.reverse D.next a b) :
    b = a ∨ b = D.reverse a := by
  have hn : D.next (D.reverse a) = a := by rw [← ha.1]; exact ha.2
  exact (components_pred D.reverse D.next (fun z => z=a ∨ z=D.reverse a)
    (pair_invariant D.reverse rfl (D.reverse_involutive a))
    (pair_invariant D.next ha.1 hn) h).mp (Or.inl rfl)

/-- Exterior cancellation retains all components and preserves the face chain. -/
theorem fold {w : List E} (D : FullFilling flip color face w)
    (hflip : Function.Involutive flip) (hne : ∀ e, color e ≠ color (flip e))
    {a b : D.Dart} {l : List D.Dart} (hb : D.boundary = b::a::l)
    (hl : D.label a = flip (D.label b)) (F : E → E → E → M)
    (hdeg : ∀ a b, F a b a = 0) :
    ∃ D' : FullFilling flip color face (l.map D.label), D'.trace F = D.trace F := by
  have hbound : IsBoundary D.next (b::a::l) := hb ▸ D.boundary_cycle
  have hab : a ≠ b := fun h => hbound.1.notMem (by simp [h])
  have hba : D.next b = a := by simpa using hbound.step 0 (by simp)
  obtain ⟨r',f',hi',hn',hp',hl',hc',hra,hrb,hfa,hfb,hm,_,heq⟩ :=
    fold_pair D.reverse D.next D.reverse_involutive D.reverse_ne D.label flip hflip
      color hne D.reverse_label D.color_next D.planar hab hba hl
  have hrest := hbound.erase_pair
  rw [←heq] at hrest
  let D' : FullFilling flip color face (l.map D.label) := {
    Dart := D.Dart
    reverse := r'
    next := f'
    reverse_involutive := hi'
    reverse_ne := hn'
    label := D.label
    reverse_label := hl'
    color_next := hc'
    planar := hp'
    boundary := l
    boundary_cycle := hrest.1
    boundary_word := rfl
    cells := by
      intro z hz
      by_cases hza : z = a
      · subst z
        exact Or.inr ⟨hfa.trans hra.symm,by simp only [pow_two,Perm.mul_apply,hfa,hfb]⟩
      by_cases hzb : z = b
      · subst z
        exact Or.inr ⟨hfb.trans hrb.symm,by simp only [pow_two,Perm.mul_apply,hfa,hfb]⟩
      have hzo : z ∉ b::a::l := by simp only [List.mem_cons]; tauto
      have hstep := hrest.2 z hzo
      have he (n : ℕ) := same_outside_boundary_pow hbound hrest.2 hzo n
      rcases D.cells z (by rwa [hb]) with ht | hg
      · exact Or.inl ⟨(he 3).trans ht.1,hstep ▸ ht.2.1,by
          simpa only [hstep,he 2] using ht.2.2⟩
      · have hrz : r' z = D.reverse z := by
          apply (D.bigon_component hg (hm ?_)).resolve_left (hn' z)
          exact (show Perm.SameCycle.setoid r' ≤ components r' f' from le_sup_left)
            (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl r' z))
        exact Or.inr ⟨hstep.trans (hg.1.trans hrz.symm),(he 2).trans hg.2⟩ }
  refine ⟨D',?_⟩
  unfold trace
  apply Finset.sum_congr rfl
  intro z _
  change (if z ∈ l then 0 else F (D.label z) (D.label (f' z)) (D.label ((f'^2) z))) = _
  by_cases hz : z ∈ l
  · have hzo : z ∈ D.boundary := by rw [hb]; simp only [List.mem_cons]; tauto
    simp only [hz,hzo,ite_true]
  by_cases hza : z = a
  · subst z
    have hzo : a ∈ D.boundary := by rw [hb]; simp
    simp only [hz,hzo,ite_false,ite_true,pow_two,Perm.mul_apply,hfa,hfb,hdeg]
  by_cases hzb : z = b
  · subst z
    have hzo : b ∈ D.boundary := by rw [hb]; simp
    simp only [hz,hzo,ite_false,ite_true,pow_two,Perm.mul_apply,hfa,hfb,hdeg]
  have hzo : z ∉ b::a::l := by simp only [List.mem_cons]; tauto
  have hD : z ∉ D.boundary := by rwa [hb]
  simp only [hz,hD,ite_false,hrest.2 z hzo,
    same_outside_boundary_pow hbound hrest.2 hzo 2]

end Release075.FullFilling

end OAI
