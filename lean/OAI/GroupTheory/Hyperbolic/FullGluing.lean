import OAI.GroupTheory.Hyperbolic.FullFilling

namespace OAI

namespace Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem wedge {w w' : List E} (D : FullFilling flip color face w)
    (D' : FullFilling flip color face w')
    {a : D.Dart} {b : D'.Dart} {l : List D.Dart} {l' : List D'.Dart}
    (ha : D.boundary = a::l) (hb : D'.boundary = b::l')
    (hc : color (flip (D.label a)) = color (flip (D'.label b)))
    (F : E → E → E → M) :
    ∃ C : FullFilling flip color face (w++w'), C.trace F = D.trace F + D'.trace F := by
  let : DecidableEq (D.Dart ⊕ D'.Dart) := Classical.decEq _
  let r := D.reverse.sumCongr D'.reverse
  let f := D.next.sumCongr D'.next
  let lab : D.Dart ⊕ D'.Dart → E := Sum.elim D.label D'.label
  let g := Equiv.swap (Sum.inl a) (Sum.inr b) * f
  let bd := (D.boundary.map Sum.inl) ++ (D'.boundary.map Sum.inr)
  have hleft : IsBoundary f ((a::l).map Sum.inl) :=
    (ha ▸ D.boundary_cycle).conjugate ⟨Sum.inl,Sum.inl_injective⟩ (fun _ => rfl)
  have hright : IsBoundary f ((b::l').map Sum.inr) :=
    (hb ▸ D'.boundary_cycle).conjugate ⟨Sum.inr,Sum.inr_injective⟩ (fun _ => rfl)
  have hdis : List.Disjoint ((a::l).map (@Sum.inl D.Dart D'.Dart))
      ((b::l').map Sum.inr) := by
    intro z hz hz'
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz
    obtain ⟨y,_,hy⟩ := List.mem_map.mp hz'
    cases hy
  have hbd : IsBoundary g bd := by
    dsimp [g,bd]
    rw [ha,hb]
    exact hleft.join hright hdis
  have hsep : ¬ components r f (Sum.inl a) (Sum.inr b) := by
    intro h
    exact (components_pred r f leftPred (leftPred_sumCongr _ _)
      (leftPred_sumCongr _ _) h).mp True.intro
  have hr : ∀ z, lab (r z) = flip (lab z) := by
    intro z; cases z with
    | inl x => exact D.reverse_label x
    | inr x => exact D'.reverse_label x
  have hcol : ∀ z, color (lab ((r*f) z)) = color (lab z) := by
    intro z; cases z with
    | inl x => exact D.color_next x
    | inr x => exact D'.color_next x
  have hcg : ∀ z, color (lab ((r*g) z)) = color (lab z) := by
    apply swap_color_preserving r f (color ∘ lab) hcol
    change color (lab (r (Sum.inl a))) = color (lab (r (Sum.inr b)))
    rw [hr,hr]
    exact hc
  have hsame : ∀ z, z ∉ bd → g z = f z := by
    intro z hz
    apply hleft.swap_outside hright z
    simpa only [bd,ha,hb,List.map_cons] using hz
  let C : FullFilling flip color face (w++w') := {
    Dart := D.Dart ⊕ D'.Dart
    reverse := r
    next := g
    reverse_involutive := by
      intro z
      cases z with
      | inl x => exact congrArg Sum.inl (D.reverse_involutive x)
      | inr x => exact congrArg Sum.inr (D'.reverse_involutive x)
    reverse_ne := by
      intro z he
      cases z with
      | inl x => exact D.reverse_ne x (Sum.inl.inj he)
      | inr x => exact D'.reverse_ne x (Sum.inr.inj he)
    label := lab
    reverse_label := hr
    color_next := hcg
    planar := (D.planar.sum D'.planar).join_right hsep
    boundary := bd
    boundary_cycle := hbd
    boundary_word := by
      simp only [bd,List.map_append,List.map_map]
      change D.boundary.map D.label ++ D'.boundary.map D'.label = w++w'
      rw [D.boundary_word,D'.boundary_word]
    cells := by
      intro z hn
      have hpow (n : ℕ) : (g^n) z = (f^n) z := by
        symm
        apply same_outside_boundary_pow hbd
        · intro z hz; exact (hsame z hz).symm
        · exact hn
      cases z with
      | inl x =>
        have hxn : x ∉ D.boundary := by
          intro hx; apply hn; exact List.mem_append_left _ (List.mem_map.mpr ⟨x,hx,rfl⟩)
        have he (n : ℕ) : (f^n) (Sum.inl x) = Sum.inl ((D.next^n) x) :=
          (pow_intertwine D.next f Sum.inl (fun _ => rfl) n x).symm
        rcases D.cells x hxn with ht | hb
        · refine Or.inl ⟨?_,?_,?_⟩
          · rw [hpow 3,he 3,ht.1]
          · rw [hsame _ hn]; intro hh; exact ht.2.1 (Sum.inl.inj hh)
          · rw [hsame _ hn,hpow 2,he 2]
            exact ht.2.2
        · refine Or.inr ⟨?_,?_⟩
          · rw [hsame _ hn]; exact congrArg Sum.inl hb.1
          · rw [hpow 2,he 2,hb.2]
      | inr x =>
        have hxn : x ∉ D'.boundary := by
          intro hx; apply hn; exact List.mem_append_right _ (List.mem_map.mpr ⟨x,hx,rfl⟩)
        have he (n : ℕ) : (f^n) (Sum.inr x) = Sum.inr ((D'.next^n) x) :=
          (pow_intertwine D'.next f Sum.inr (fun _ => rfl) n x).symm
        rcases D'.cells x hxn with ht | hb
        · refine Or.inl ⟨?_,?_,?_⟩
          · rw [hpow 3,he 3,ht.1]
          · rw [hsame _ hn]; intro hh; exact ht.2.1 (Sum.inr.inj hh)
          · rw [hsame _ hn,hpow 2,he 2]
            exact ht.2.2
        · refine Or.inr ⟨?_,?_⟩
          · rw [hsame _ hn]; exact congrArg Sum.inr hb.1
          · rw [hpow 2,he 2,hb.2] }
  refine ⟨C,?_⟩
  unfold trace
  rw [Fintype.sum_sum_type]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro x _
    have hx : Sum.inl x ∈ bd ↔ x ∈ D.boundary := by
      simp only [bd,List.mem_append,List.mem_map,Sum.inl.injEq]
      simp only [Sum.inr_ne_inl,exists_false,and_false,or_false,exists_eq_right]
    by_cases hxb : x ∈ D.boundary
    · simp only [C,hx,hxb,ite_true]
    have hn := not_congr hx |>.mpr hxb
    have hpow (n : ℕ) : (g^n) (Sum.inl x) = Sum.inl ((D.next^n) x) := by
      exact (same_outside_boundary_pow hbd (fun z hz => (hsame z hz).symm) hn n).symm.trans
        (pow_intertwine D.next f Sum.inl (fun _ => rfl) n x).symm
    simp only [C,hx,hxb,ite_false,hpow 2,hsame _ hn]
    rfl
  · apply Finset.sum_congr rfl
    intro x _
    have hx : Sum.inr x ∈ bd ↔ x ∈ D'.boundary := by
      simp only [bd,List.mem_append,List.mem_map,Sum.inr.injEq]
      simp only [Sum.inl_ne_inr,exists_false,and_false,false_or,exists_eq_right]
    by_cases hxb : x ∈ D'.boundary
    · simp only [C,hx,hxb,ite_true]
    have hn := not_congr hx |>.mpr hxb
    have hpow (n : ℕ) : (g^n) (Sum.inr x) = Sum.inr ((D'.next^n) x) := by
      exact (same_outside_boundary_pow hbd (fun z hz => (hsame z hz).symm) hn n).symm.trans
        (pow_intertwine D'.next f Sum.inr (fun _ => rfl) n x).symm
    simp only [C,hx,hxb,ite_false,hpow 2,hsame _ hn]
    rfl

end Release075.FullFilling

namespace Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

noncomputable abbrev reword {w w' : List E} (D : FullFilling flip color face w)
    (h : w = w') : FullFilling flip color face w' := h ▸ D

theorem trace_reword {w w' : List E} (D : FullFilling flip color face w)
    (h : w = w') (F : E → E → E → M) : (D.reword h).trace F = D.trace F := by
  subst w'; rfl

theorem rotateAppend {u v : List E} (D : FullFilling flip color face (u++v))
    (F : E → E → E → M) :
    ∃ D' : FullFilling flip color face (v++u), D'.trace F = D.trace F := by
  refine ⟨(D.rotate u.length).reword (List.rotate_append_length_eq u v),?_⟩
  rw [trace_reword,trace_rotate]

theorem foldHead (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    {e : E} {w : List E} (D : FullFilling flip color face (e::flip e::w))
    (F : E → E → E → M) (hdeg : ∀ a b, F a b a = 0) :
    ∃ D' : FullFilling flip color face w, D'.trace F = D.trace F := by
  obtain ⟨b,bs,hb,he,hbs⟩ := List.map_eq_cons_iff.mp D.boundary_word
  obtain ⟨a,l,ha,hae,hl⟩ := List.map_eq_cons_iff.mp hbs
  have hbound : D.boundary = b::a::l := by rw [hb,ha]
  have hab : D.label a = flip (D.label b) := by rw [he,hae]
  obtain ⟨D',ht⟩ := D.fold hi hn hbound hab F hdeg
  exact ⟨D'.reword hl,(trace_reword D' hl F).trans ht⟩

theorem erase (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    (u v : List E) (e : E) (D : FullFilling flip color face (u++e::flip e::v))
    (F : E → E → E → M) (hdeg : ∀ a b, F a b a = 0) :
    ∃ D' : FullFilling flip color face (u++v), D'.trace F = D.trace F := by
  obtain ⟨D₁,h₁⟩ := D.rotateAppend F
  change FullFilling flip color face (e::flip e::(v++u)) at D₁
  obtain ⟨D₂,h₂⟩ := D₁.foldHead hi hn F hdeg
  obtain ⟨D₃,h₃⟩ := D₂.rotateAppend (u := v) (v := u) F
  exact ⟨D₃,h₃.trans (h₂.trans h₁)⟩

theorem erase_reverse (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    (u v p : List E) (D : FullFilling flip color face (u ++ reverseWord flip p ++ p ++ v))
    (F : E → E → E → M) (hdeg : ∀ a b, F a b a = 0) :
    ∃ D' : FullFilling flip color face (u++v), D'.trace F = D.trace F := by
  induction p generalizing u with
  | nil =>
    have he : u ++ reverseWord flip [] ++ [] ++ v = u++v := by
      simp only [reverseWord_nil,List.append_nil]
    exact ⟨D.reword he,trace_reword D he F⟩
  | cons e p ih =>
    have he : u ++ reverseWord flip (e::p) ++ (e::p) ++ v =
        (u++reverseWord flip p) ++ flip e :: flip (flip e) :: (p++v) := by
      simp only [reverseWord_cons,List.append_assoc,List.nil_append,List.cons_append,hi e]
    obtain ⟨D₁,h₁⟩ := (D.reword he).erase hi hn (u++reverseWord flip p) (p++v) (flip e) F hdeg
    have he' : (u++reverseWord flip p) ++ (p++v) =
        u ++ reverseWord flip p ++ p ++ v := by simp only [List.append_assoc]
    obtain ⟨D₂,h₂⟩ := ih u (D₁.reword he')
    exact ⟨D₂,h₂.trans ((trace_reword D₁ he' F).trans (h₁.trans (trace_reword D he F)))⟩

theorem trace_palindrome
    (hempty : ∀ D : TriangleSphere flip color face, IsEmpty D.Dipole → IsEmpty D.Dart)
    (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    (F : E → E → E → M)
    (hrot : ∀ a b c, face a b c → F b c a = F a b c)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c)
    (hdeg : ∀ a b, F a b a = 0)
    (w : List E) (D : FullFilling flip color face (reverseWord flip w ++ w)) :
    D.trace F = 0 := by
  have he : reverseWord flip w ++ w = [] ++ reverseWord flip w ++ w ++ [] := by
    simp only [List.nil_append,List.append_nil]
  obtain ⟨D',h⟩ := (D.reword he).erase_reverse hi hn [] [] w F hdeg
  rw [trace_reword] at h
  exact h.symm.trans (D'.trace_empty hempty F hrot hmir hdeg)

/-- The signed triangle chain of a full disk depends only on its typed boundary.
This is proved by actual exterior folds, retaining detached components. -/
theorem trace_unique
    (hempty : ∀ D : TriangleSphere flip color face, IsEmpty D.Dipole → IsEmpty D.Dart)
    (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    (hf : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (F : E → E → E → M)
    (hrot : ∀ a b c, face a b c → F b c a = F a b c)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c)
    (hdeg : ∀ a b, F a b a = 0)
    {x : V} {w : List E} (hw : WordPath flip color x x w)
    (D D' : FullFilling flip color face w) : D.trace F = D'.trace F := by
  cases w with
  | nil => rw [trace_empty hempty F hrot hmir hdeg,trace_empty hempty F hrot hmir hdeg]
  | cons e es =>
    let B := D.mirror hi hf
    have hne : reverseWord flip (e::es) ≠ [] := by
      simp only [reverseWord,List.map_eq_nil_iff,List.reverse_eq_nil_iff,
        ne_eq,List.cons_ne_nil,not_false_eq_true]
    obtain ⟨f,fs,he⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨a,l,ha,hal,_⟩ := List.map_eq_cons_iff.mp (B.boundary_word.trans he)
    obtain ⟨b,l',hb,hbl,_⟩ := List.map_eq_cons_iff.mp D'.boundary_word
    have hrev := hw.reverse hi
    rw [he] at hrev
    obtain ⟨C,hC⟩ := B.wedge D' ha hb (by rw [hal,hbl]; exact hrev.source.trans hw.source.symm) F
    have hzero := C.trace_palindrome hempty hi hn F hrot hmir hdeg (e::es)
    have hz : B.trace F + D'.trace F = 0 := hC.symm.trans hzero
    have hm : B.trace F = -D.trace F := D.trace_mirror hi hf F hmir hdeg
    rw [hm] at hz
    exact neg_add_eq_zero.mp hz

end Release075.FullFilling

namespace Release075.FullFilling
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Cyclic reindexing of corners of genuine triangles. -/
theorem trace_cyclic {w : List E} (D : FullFilling flip color face w)
    (ht : ∀ a, a ∉ D.boundary → (D.next^3) a = a)
    (F : E → E → E → M) : D.trace (fun a b c => F b c a) = D.trace F := by
  let f : D.Dart → M := fun a => if a ∈ D.boundary then 0 else
    F (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))
  have hsum := Equiv.sum_comp D.next f
  rw [trace]
  change _ = ∑ a, f a
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro a _
  have hm := D.boundary_cycle.mem_iff a
  by_cases ha : a ∈ D.boundary
  · simp only [f,ha,hm,ite_true]
  · have h3 : (D.next^2) (D.next a) = a := by
      simpa only [pow_succ,Perm.mul_apply] using ht a ha
    simp only [f,ha,hm,ite_false,h3]
    rw [pow_two,Perm.mul_apply]

theorem trace_add {w : List E} (D : FullFilling flip color face w)
    (F H : E → E → E → M) : D.trace (fun a b c => F a b c + H a b c) = D.trace F + D.trace H := by
  unfold trace
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp only [add_zero]

theorem trace_cyclic_sum {w : List E} (D : FullFilling flip color face w)
    (ht : ∀ a, a ∉ D.boundary → (D.next^3) a = a)
    (F : E → E → E → M) :
    D.trace (fun a b c => F a b c + F b c a + F c a b) = 3 • D.trace F := by
  rw [trace_add,trace_add,trace_cyclic D ht F]
  have hh : D.trace (fun a b c => F c a b) = D.trace F :=
    (D.trace_cyclic ht (fun a b c => F b c a)).trans (D.trace_cyclic ht F)
  rw [hh]
  simp only [succ_nsmul,zero_nsmul,zero_add]

end Release075.FullFilling

namespace Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M N : Type} [AddCommGroup M] [AddCommGroup N]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem trace_map {w : List E} (D : FullFilling flip color face w)
    (F : E → E → E → M) (f : M →+ N) :
    f (D.trace F) = D.trace (fun a b c => f (F a b c)) := by
  unfold trace
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp only [map_zero]

theorem trace_congr {w : List E} (D : FullFilling flip color face w)
    {F H : E → E → E → M}
    (h : ∀ a, a ∉ D.boundary →
      F (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a)) =
      H (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))) : D.trace F = D.trace H := by
  unfold trace
  apply Finset.sum_congr rfl
  intro a _
  split_ifs with ha
  · rfl
  · exact h a ha

/-- Integral Stokes accounting for an antisymmetric edge evaluation. -/
theorem trace_edge {w : List E} (D : FullFilling flip color face w)
    (F : E → M) (hf : ∀ e, F (flip e) = -F e) :
    D.trace (fun a _ _ => F a) = -(w.map F).sum := by
  let f : D.Dart → M := F ∘ D.label
  have hz : ∑ a, f a = 0 := by
    apply Finset.sum_involution (fun a _ => D.reverse a)
    · intro a _
      simp only [f,Function.comp_apply,D.reverse_label,hf,add_neg_cancel]
    · intro a _ _; exact D.reverse_ne a
    · intro a _; exact Finset.mem_univ _
    · intro a _; exact D.reverse_involutive a
  have hb : (∑ a, if a ∈ D.boundary then f a else 0) = (w.map F).sum := by
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun a => a ∈ D.boundary) = D.boundary.toFinset := by ext; simp
    rw [he,List.sum_toFinset _ D.boundary_cycle.1]
    change (D.boundary.map (F ∘ D.label)).sum = _
    rw [← List.map_map,D.boundary_word]
  have hpart : (∑ a, if a ∈ D.boundary then f a else 0) +
      D.trace (fun a _ _ => F a) = ∑ a, f a := by
    rw [trace,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp only [add_zero,zero_add,f,Function.comp_apply]
  rw [hb,hz] at hpart
  apply eq_neg_iff_add_eq_zero.mpr
  rw [add_comm]
  exact hpart

end Release075.FullFilling

namespace Release075.TriangleFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem full_triangular {w : List E} (D : TriangleFilling flip color face w)
    (a : D.full.Dart) (ha : a ∉ D.full.boundary) :
    (D.full.next^3) a = a ∧ D.full.next a ≠ a ∧
      face (D.full.label a) (D.full.label (D.full.next a)) (D.full.label ((D.full.next^2) a)) := by
  have hn : a.val ∉ D.boundary := by
    intro h
    apply ha
    exact List.mem_pmap.mpr ⟨a.val,h,rfl⟩
  have ht := D.triangular a.val a.property hn
  exact ⟨Subtype.ext ht.1,fun he => ht.2.1 (congrArg Subtype.val he),ht.2.2⟩

end Release075.TriangleFilling

end OAI
