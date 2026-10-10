import OAI.GroupTheory.Hyperbolic.RePairing

namespace OAI

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A finite genus-zero map with a prescribed exterior walk. Other components
are allowed but ignored; only the component meeting the boundary must be filled.
This handles components detached by folds, spurs, and empty boundary words. -/
structure TriangleFilling {E V : Type} (flip : E → E) (color : E → V)
    (face : E → E → E → Prop) (w : List E) where
  Dart : Type
  [finiteDart : Fintype Dart]
  reverse : Perm Dart
  next : Perm Dart
  reverse_involutive : Function.Involutive reverse
  reverse_ne : ∀ d, reverse d ≠ d
  label : Dart → E
  reverse_label : ∀ d, label (reverse d) = flip (label d)
  color_next : ∀ d, color (label ((reverse*next) d)) = color (label d)
  planar : PlanarMap reverse next
  boundary : List Dart
  boundary_cycle : IsBoundary next boundary
  boundary_word : boundary.map label = w
  triangular : ∀ d, (∃ b ∈ boundary, components reverse next d b) → d ∉ boundary →
    (next^3) d = d ∧ next d ≠ d ∧ face (label d) (label (next d)) (label ((next^2) d))

attribute [instance] TriangleFilling.finiteDart

namespace TriangleFilling
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

noncomputable def empty : TriangleFilling flip color face [] where
  Dart := Fin 0
  reverse := 1
  next := 1
  reverse_involutive := fun _ => rfl
  reverse_ne := by intro d; exact Fin.elim0 d
  label := Fin.elim0
  reverse_label := by intro d; exact Fin.elim0 d
  color_next := by intro d; exact Fin.elim0 d
  planar := by
    simp only [PlanarMap,one_mul,cycleCount_one,componentCount_one,Fintype.card_fin]
  boundary := []
  boundary_cycle := ⟨by simp,by simp⟩
  boundary_word := rfl
  triangular := by intro d; exact Fin.elim0 d

noncomputable def rotate {w : List E} (D : TriangleFilling flip color face w) (n : ℕ) :
    TriangleFilling flip color face (w.rotate n) where
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
  triangular := by
    intro d hd hn
    apply D.triangular d
    · obtain ⟨b,hb,hdb⟩ := hd
      exact ⟨b,List.mem_rotate.mp hb,hdb⟩
    · simpa only [List.mem_rotate] using hn

end TriangleFilling
end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem PlanarMap.involution (r : Perm A) (h : Function.Involutive r) : PlanarMap r r := by
  have hr : r*r = 1 := Equiv.ext h
  have hc : componentCount r r = cycleCount r := by
    simp only [componentCount,components,sup_idem,cycleCount,Cycles]
  simp only [PlanarMap,hr,cycleCount_one,hc]
  omega

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

noncomputable def backtrack (hflip : Function.Involutive flip) (e : E) :
    TriangleFilling flip color face [e,flip e] where
  Dart := Fin 2
  reverse := Equiv.swap 0 1
  next := Equiv.swap 0 1
  reverse_involutive := Equiv.swap_apply_self 0 1
  reverse_ne := by intro a; fin_cases a <;> norm_num [Equiv.swap_apply_def,Fin.ext_iff]
  label := fun d => if d = 0 then e else flip e
  reverse_label := by
    intro d
    fin_cases d <;> norm_num [Equiv.swap_apply_def,Fin.ext_iff]
    exact (hflip e).symm
  color_next := by intro d; simp only [Perm.mul_apply,Equiv.swap_apply_self]
  planar := PlanarMap.involution _ (Equiv.swap_apply_self 0 1)
  boundary := [0,1]
  boundary_cycle := ⟨by decide,by intro a _; fin_cases a <;> simp⟩
  boundary_word := by simp
  triangular := by intro d _ hn; fin_cases d <;> simp at hn

end Release075.TriangleFilling

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

theorem IsBoundary.step {f : Perm A} {l : List A} (h : IsBoundary f l)
    (n : ℕ) (hn : n+1 < l.length) : f l[n] = l[n+1] := by
  rw [h.2 _ (List.getElem_mem _)]
  exact List.formPerm_apply_lt_getElem l h.1 n hn

theorem IsBoundary.erase_pair {f : Perm A} {a b : A} {l : List A}
    (h : IsBoundary f (b::a::l)) :
    IsBoundary (Equiv.swap b (f a)*f) l ∧
    (∀ z, z ∉ b::a::l → (Equiv.swap b (f a)*f) z = f z) := by
  constructor
  · refine ⟨h.1.of_cons.of_cons,?_⟩
    intro z hz
    cases l with
    | nil => simp at hz
    | cons c cs =>
      have hfa : f a = c := h.step 1 (by simp)
      have hcb : c ∉ [b,a] := by
        have hh := h.1
        simp only [List.nodup_cons,List.mem_cons] at hh ⊢
        tauto
      have hperm : (b::a::c::cs : List A).formPerm =
          Equiv.swap b c * (Equiv.swap b a * (c::cs).formPerm) := by
        simpa only [List.formPerm_pair, List.cons_append, List.nil_append] using formPerm_concat b c [a] cs hcb
      have hmem : (c::cs).formPerm z ∈ c::cs := List.formPerm_apply_mem_of_mem hz
      have hnb : (c::cs).formPerm z ≠ b := by
        intro he; apply h.1.notMem; rw [←he]; exact List.mem_cons_of_mem a hmem
      have hna : (c::cs).formPerm z ≠ a := by
        intro he; apply h.1.of_cons.notMem; rwa [←he]
      have hzfull : z ∈ b::a::c::cs := List.mem_cons_of_mem b (List.mem_cons_of_mem a hz)
      rw [Perm.mul_apply, hfa, h.2 z hzfull, hperm]
      simp only [Perm.mul_apply, Equiv.swap_apply_self,
        Equiv.swap_apply_of_ne_of_ne hnb hna]
  · intro z hz
    have hfz := (h.not_mem_iff z).mpr hz
    have hfa := (h.mem_iff a).mpr (by simp)
    apply Equiv.swap_apply_of_ne_of_ne
    · intro he; apply hfz; simp [he]
    · intro he; apply hfz; rwa [he]

theorem same_outside_boundary_pow {f g : Perm A} {l : List A}
    (hb : IsBoundary f l) (he : ∀ z, z ∉ l → g z = f z)
    {a : A} (ha : a ∉ l) (n : ℕ) : (g^n) a = (f^n) a := by
  have ho (k : ℕ) : (f^k) a ∉ l := by
    induction k with
    | zero => exact ha
    | succ k ih =>
      rw [pow_succ',Perm.mul_apply]
      exact (hb.not_mem_iff _).mpr ih
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ',Perm.mul_apply,ih,he _ (ho n)]

end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

theorem components_pred [Fintype A] (r f : Perm A) (p : A → Prop)
    (hr : ∀ a, p (r a) ↔ p a) (hf : ∀ a, p (f a) ↔ p a)
    {a b : A} (h : components r f a b) : p a ↔ p b := by
  have hh : components r f ≤ Setoid.ker p := by
    apply sup_le
    · intro x y h; exact propext (invariant_pred_sameCycle r p hr h)
    · intro x y h; exact propext (invariant_pred_sameCycle f p hf h)
  exact propext_iff.mp (hh h)

theorem pair_invariant (f : Perm A) {a b : A} (ha : f a = b) (hb : f b = a) (z : A) :
    (f z = a ∨ f z = b) ↔ (z = a ∨ z = b) := by
  constructor
  · rintro (h | h)
    · exact Or.inr (f.injective (h.trans hb.symm))
    · exact Or.inl (f.injective (h.trans ha.symm))
  · rintro (rfl | rfl)
    · exact Or.inr ha
    · exact Or.inl hb

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- A genuine reverse-edge deletion, retaining the external word even when the
outside partners reconnect. The detached tree is an ignored separate component. -/
theorem fold {w : List E} (D : TriangleFilling flip color face w)
    (hflip : Function.Involutive flip) (hne : ∀ e, color e ≠ color (flip e))
    {a b : D.Dart} {l : List D.Dart} (hb : D.boundary = b::a::l)
    (hl : D.label a = flip (D.label b)) :
    Nonempty (TriangleFilling flip color face (l.map D.label)) := by
  have hbound : IsBoundary D.next (b::a::l) := hb ▸ D.boundary_cycle
  have hab : a ≠ b := fun h => hbound.1.notMem (by simp [h])
  have hba : D.next b = a := by simpa using hbound.step 0 (by simp)
  obtain ⟨r',f',hi',hn',hp',hl',hc',hra,hrb,hfa,hfb,hm,_,heq⟩ :=
    fold_pair D.reverse D.next D.reverse_involutive D.reverse_ne D.label flip hflip
      color hne D.reverse_label D.color_next D.planar hab hba hl
  have hrest := hbound.erase_pair
  rw [←heq] at hrest
  have hnot (z : D.Dart) (hz : z ∈ l) : ¬(z = a ∨ z = b) := by
    rintro (rfl | rfl)
    · exact hbound.1.of_cons.notMem hz
    · exact hbound.1.notMem (List.mem_cons_of_mem a hz)
  refine ⟨{
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
    triangular := ?_ }⟩
  intro z hz hzl
  obtain ⟨c,hcl,hzc⟩ := hz
  have hnotpair : ¬(z = a ∨ z = b) := by
    intro hp
    exact hnot c hcl ((components_pred r' f' (fun x => x=a ∨ x=b)
      (pair_invariant r' hra hrb) (pair_invariant f' hfa hfb) hzc).mp hp)
  have hzo : z ∉ b::a::l := by simp only [List.mem_cons]; tauto
  have htri := D.triangular z ⟨c,by rw [hb]; simp only [List.mem_cons]; tauto,hm hzc⟩
    (by rwa [hb])
  have he (n : ℕ) := same_outside_boundary_pow hbound hrest.2 hzo n
  refine ⟨?_,?_,?_⟩
  · rw [he 3]; exact htri.1
  · have hstep : f' z = D.next z := hrest.2 z hzo
    rw [hstep]
    exact htri.2.1
  · simpa only [hrest.2 z hzo,he 2] using htri.2.2

end Release075.TriangleFilling

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

theorem IsBoundary.join {f : Perm A} {x y : A} {xs ys : List A}
    (hx : IsBoundary f (x::xs)) (hy : IsBoundary f (y::ys))
    (hd : List.Disjoint (x::xs) (y::ys)) :
    IsBoundary (Equiv.swap x y * f) ((x::xs) ++ (y::ys)) := by
  refine ⟨List.nodup_append.mpr ⟨hx.1,hy.1,by rintro z hz t ht rfl; exact hd hz ht⟩,?_⟩
  intro z hz
  rw [formPerm_concat x y xs ys (fun h => hd h (by simp))]
  simp only [Perm.mul_apply]
  congr 1
  rcases List.mem_append.mp hz with hz|hz
  · rw [List.formPerm_apply_of_notMem (fun h => hd hz h),hx.2 z hz]
  · rw [List.formPerm_apply_of_notMem (fun h => hd h (List.formPerm_apply_mem_of_mem hz)),
      hy.2 z hz]

theorem IsBoundary.swap_outside {f : Perm A} {x y : A} {xs ys : List A}
    (hx : IsBoundary f (x::xs)) (hy : IsBoundary f (y::ys))
    (z : A) (hz : z ∉ (x::xs) ++ (y::ys)) :
    (Equiv.swap x y * f) z = f z := by
  have hn := not_or.mp (List.mem_append.not.mp hz)
  apply Equiv.swap_apply_of_ne_of_ne
  · intro he; apply (hx.not_mem_iff z).mpr hn.1; simp [he]
  · intro he; apply (hy.not_mem_iff z).mpr hn.2; simp [he]

end Release075

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

def Active {w : List E} (D : TriangleFilling flip color face w) (a : D.Dart) : Prop :=
  ∃ b ∈ D.boundary, components D.reverse D.next a b

theorem active_iff_of_components {w : List E} (D : TriangleFilling flip color face w)
    {a b : D.Dart} (h : components D.reverse D.next a b) : D.Active a ↔ D.Active b := by
  constructor <;> rintro ⟨c,hc,hc'⟩
  · exact ⟨c,hc,(components D.reverse D.next).trans ((components D.reverse D.next).symm h) hc'⟩
  · exact ⟨c,hc,(components D.reverse D.next).trans h hc'⟩

theorem active_reverse {w : List E} (D : TriangleFilling flip color face w) (a : D.Dart) :
    D.Active (D.reverse a) ↔ D.Active a :=
  D.active_iff_of_components ((show Perm.SameCycle.setoid D.reverse ≤
    components D.reverse D.next from le_sup_left)
      (Perm.sameCycle_apply_left.mpr (Perm.SameCycle.refl _ _)))

theorem active_next {w : List E} (D : TriangleFilling flip color face w) (a : D.Dart) :
    D.Active (D.next a) ↔ D.Active a :=
  D.active_iff_of_components ((show Perm.SameCycle.setoid D.next ≤
    components D.reverse D.next from le_sup_right)
      (Perm.sameCycle_apply_left.mpr (Perm.SameCycle.refl _ _)))

theorem active_of_mem {w : List E} (D : TriangleFilling flip color face w)
    {a : D.Dart} (ha : a ∈ D.boundary) : D.Active a :=
  ⟨a,ha,(components D.reverse D.next).refl _⟩

/-- Wedge two disks at their initial boundary corner. No component of either
input that was disjoint from its boundary becomes an active component. -/
theorem wedge {w w' : List E} (D : TriangleFilling flip color face w)
    (D' : TriangleFilling flip color face w')
    {a : D.Dart} {b : D'.Dart} {l : List D.Dart} {l' : List D'.Dart}
    (ha : D.boundary = a::l) (hb : D'.boundary = b::l')
    (hc : color (flip (D.label a)) = color (flip (D'.label b))) :
    Nonempty (TriangleFilling flip color face (w++w')) := by
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
  let act : D.Dart ⊕ D'.Dart → Prop := Sum.elim D.Active D'.Active
  have har : ∀ z, act (r z) ↔ act z := by
    intro z; cases z with
    | inl x => exact D.active_reverse x
    | inr x => exact D'.active_reverse x
  have haf : ∀ z, act (f z) ↔ act z := by
    intro z; cases z with
    | inl x => exact D.active_next x
    | inr x => exact D'.active_next x
  have haa : act (Sum.inl a) := D.active_of_mem (by rw [ha]; simp)
  have hab : act (Sum.inr b) := D'.active_of_mem (by rw [hb]; simp)
  have hag : ∀ z, act (g z) ↔ act z := by
    intro z
    change act (Equiv.swap (Sum.inl a) (Sum.inr b) (f z)) ↔ act z
    rw [color_swap act (propext (iff_of_true haa hab))]
    exact haf z
  have hact : ∀ z, (∃ c ∈ bd, components r g z c) → act z := by
    rintro z ⟨c,hc,hzc⟩
    apply (components_pred r g act har hag hzc).mpr
    rcases List.mem_append.mp hc with hc|hc
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      exact D.active_of_mem hd
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      exact D'.active_of_mem hd
  refine ⟨{
    Dart := D.Dart ⊕ D'.Dart
    reverse := r
    next := g
    reverse_involutive := ?_
    reverse_ne := ?_
    label := lab
    reverse_label := hr
    color_next := hcg
    planar := (D.planar.sum D'.planar).join_right hsep
    boundary := bd
    boundary_cycle := hbd
    boundary_word := ?_
    triangular := ?_ }⟩
  · intro z
    cases z with
    | inl x => exact congrArg Sum.inl (D.reverse_involutive x)
    | inr x => exact congrArg Sum.inr (D'.reverse_involutive x)
  · intro z he
    cases z with
    | inl x => exact D.reverse_ne x (Sum.inl.inj he)
    | inr x => exact D'.reverse_ne x (Sum.inr.inj he)
  · simp only [bd,List.map_append,List.map_map]
    change D.boundary.map D.label ++ D'.boundary.map D'.label = w++w'
    rw [D.boundary_word,D'.boundary_word]
  · intro z hz hn
    have hzact := hact z hz
    have hpow (n : ℕ) : (g^n) z = (f^n) z := by
      symm
      apply same_outside_boundary_pow hbd
      · intro z hz; exact (hsame z hz).symm
      · exact hn

    cases z with
    | inl x =>
      have hxn : x ∉ D.boundary := by
        intro hx; apply hn; exact List.mem_append_left _ (List.mem_map.mpr ⟨x,hx,rfl⟩)
      have ht := D.triangular x hzact hxn
      have he (n : ℕ) : (f^n) (Sum.inl x) = Sum.inl ((D.next^n) x) :=
        (pow_intertwine D.next f Sum.inl (fun _ => rfl) n x).symm
      refine ⟨?_,?_,?_⟩
      · rw [hpow 3,he 3,ht.1]
      · rw [hsame _ hn]; intro hh; exact ht.2.1 (Sum.inl.inj hh)
      · rw [hsame _ hn,hpow 2,he 2]
        exact ht.2.2
    | inr x =>
      have hxn : x ∉ D'.boundary := by
        intro hx; apply hn; exact List.mem_append_right _ (List.mem_map.mpr ⟨x,hx,rfl⟩)
      have ht := D'.triangular x hzact hxn
      have he (n : ℕ) : (f^n) (Sum.inr x) = Sum.inr ((D'.next^n) x) :=
        (pow_intertwine D'.next f Sum.inr (fun _ => rfl) n x).symm
      refine ⟨?_,?_,?_⟩
      · rw [hpow 3,he 3,ht.1]
      · rw [hsame _ hn]; intro hh; exact ht.2.1 (Sum.inr.inj hh)
      · rw [hsame _ hn,hpow 2,he 2]
        exact ht.2.2

end Release075.TriangleFilling

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq

theorem dipoleReverse_involutive : Function.Involutive dipoleReverse := by
  intro j; fin_cases j <;> simp

theorem dipoleReverse_ne (j : Fin 6) : dipoleReverse j ≠ j := by
  fin_cases j <;> norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]

theorem dipoleReverse_count : cycleCount dipoleReverse = 3 := by
  have h := card_eq_mul_cycles dipoleReverse 2 (orbit_card_involution dipoleReverse
    dipoleReverse_involutive dipoleReverse_ne)
  have hh : (6:ℕ) = 2 * cycleCount dipoleReverse := by
    simpa only [Fintype.card_fin,cycleCount,Nat.card_eq_fintype_card] using h
  omega

theorem dipoleVertex_count : cycleCount (dipoleReverse*dipoleFace) = 3 := by
  have hi : Function.Involutive (dipoleReverse*dipoleFace) := by
    intro j; fin_cases j <;> simp [Perm.mul_apply]
  have hn : ∀ j, (dipoleReverse*dipoleFace) j ≠ j := by
    intro j; fin_cases j <;> norm_num [dipoleReverse,dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
  have h := card_eq_mul_cycles (dipoleReverse*dipoleFace) 2
    (orbit_card_involution _ hi hn)
  have hh : (6:ℕ) = 2 * cycleCount (dipoleReverse*dipoleFace) := by
    simpa only [Fintype.card_fin,cycleCount,Nat.card_eq_fintype_card] using h
  omega

theorem dipole_components (a b : Fin 6) : components dipoleReverse dipoleFace a b := by
  let s := components dipoleReverse dipoleFace
  have hr (j : Fin 6) : s j (dipoleReverse j) :=
    (show Perm.SameCycle.setoid dipoleReverse ≤ s from le_sup_left)
      (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl _ _))
  have hf (j : Fin 6) : s j (dipoleFace j) :=
    (show Perm.SameCycle.setoid dipoleFace ≤ s from le_sup_right)
      (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl _ _))
  have h01 : s 0 1 := by simpa only [dipoleFace_zero] using hf 0
  have h12 : s 1 2 := by simpa only [dipoleFace_one] using hf 1
  have h03 : s 0 3 := by simpa only [dipoleReverse_zero] using hr 0
  have h34 : s 3 4 := by simpa only [dipoleFace_three] using hf 3
  have h45 : s 4 5 := by simpa only [dipoleFace_four] using hf 4
  have h0 (j : Fin 6) : s 0 j := by
    fin_cases j
    · exact s.refl 0
    · exact h01
    · exact s.trans h01 h12
    · exact h03
    · exact s.trans h03 h34
    · exact s.trans (s.trans h03 h34) h45
  exact s.trans (s.symm (h0 a)) (h0 b)

theorem dipoleComponent_count : componentCount dipoleReverse dipoleFace = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨Quotient.mk _ 0,?_⟩
  intro z
  obtain ⟨j,rfl⟩ := Quotient.mk_surjective z
  exact Quotient.sound (dipole_components j 0)

theorem dipole_planar : PlanarMap dipoleReverse dipoleFace := by
  simp only [PlanarMap,dipoleReverse_count,dipoleFace_count,dipoleVertex_count,
    dipoleComponent_count,Fintype.card_fin]

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

def triLabel (a b c : E) (j : Fin 6) : E :=
  if j=0 then a else if j=1 then b else if j=2 then c else
  if j=3 then flip a else if j=4 then flip c else flip b

noncomputable def triangle (hflip : Function.Involutive flip)
    (hrot : ∀ a b c, face a b c → face b c a)
    (a b c : E) (hab : color a = color (flip b))
    (hbc : color b = color (flip c)) (hca : color c = color (flip a))
    (hface : face (flip a) (flip c) (flip b)) :
    TriangleFilling flip color face [a,b,c] where
  Dart := Fin 6
  reverse := dipoleReverse
  next := dipoleFace
  reverse_involutive := dipoleReverse_involutive
  reverse_ne := dipoleReverse_ne
  label := triLabel (flip := flip) a b c
  reverse_label := by
    intro j; fin_cases j <;> simp [triLabel]
    all_goals exact (hflip _).symm
  color_next := by
    intro j; fin_cases j <;> simp [Perm.mul_apply,triLabel,hab,hbc,hca]
  planar := dipole_planar
  boundary := [0,1,2]
  boundary_cycle := by
    constructor
    · decide
    · intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl|rfl|rfl <;> simp [List.formPerm_cons_cons,Equiv.swap_apply_def]
  boundary_word := by simp [triLabel]
  triangular := by
    intro j _ hj
    fin_cases j
    · simp at hj
    · simp at hj
    · simp at hj
    · norm_num [pow_succ',Perm.mul_apply,triLabel,dipoleFace,Equiv.swap_apply_def,Fin.ext_iff]
      exact hface
    · norm_num [pow_succ',Perm.mul_apply,triLabel,dipoleFace,Equiv.swap_apply_def,Fin.ext_iff]
      exact hrot _ _ _ hface
    · norm_num [pow_succ',Perm.mul_apply,triLabel,dipoleFace,Equiv.swap_apply_def,Fin.ext_iff]
      exact hrot _ _ _ (hrot _ _ _ hface)

end Release075.TriangleFilling

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

omit [Fintype A] in
theorem cycleCount_inv (f : Perm A) : cycleCount f⁻¹ = cycleCount f := by
  apply Nat.card_congr
  exact Quotient.congr (Equiv.refl A) (fun _ _ => Perm.sameCycle_inv)

omit [Fintype A] in
theorem components_inv_right (r f : Perm A) : components r f⁻¹ = components r f := by
  have hf : Perm.SameCycle.setoid f⁻¹ = Perm.SameCycle.setoid f :=
    Setoid.ext (fun _ _ => Perm.sameCycle_inv)
  simp only [components,hf]

theorem PlanarMap.inv_right {r f : Perm A} (hi : Function.Involutive r)
    (hp : PlanarMap r f) : PlanarMap r f⁻¹ := by
  have hr : r⁻¹ = r := by
    apply inv_eq_of_mul_eq_one_left
    exact Equiv.ext hi
  have hc : cycleCount (r*f⁻¹) = cycleCount (r*f) := by
    rw [cycleCount_mul_comm]
    have he : f⁻¹*r = (r*f)⁻¹ := by rw [mul_inv_rev,hr]
    rw [he,cycleCount_inv]
  simpa only [PlanarMap,cycleCount_inv,hc,componentCount,components_inv_right] using hp

omit [Fintype A] in
theorem perm_apply_inv (f : Perm A) (a : A) : f (f⁻¹ a) = a := f.apply_symm_apply a

omit [Fintype A] in
theorem inv_cycle_three (f : Perm A) {a : A} (h : (f^3) a = a) :
    f⁻¹ a = (f^2) a ∧ (f⁻¹^2) a = f a ∧ (f⁻¹^3) a = a := by
  have he : f⁻¹ a = (f^2) a := by
    apply f.injective
    rw [perm_apply_inv]
    exact h.symm
  refine ⟨he,?_,?_⟩
  · rw [pow_two,Perm.mul_apply,he]
    change f⁻¹ (f (f a)) = f a
    exact f.symm_apply_apply _
  · rw [inv_pow]
    apply (f^3).injective
    rw [perm_apply_inv,h]

end Release075.PermCycles

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

theorem IsBoundary.reverse {f : Perm A} {l : List A} (h : IsBoundary f l) :
    IsBoundary f⁻¹ l.reverse := by
  refine ⟨List.nodup_reverse.mpr h.1,?_⟩
  intro a ha
  have ha' := List.mem_reverse.mp ha
  have hb : f⁻¹ a ∈ l := by
    apply (h.mem_iff _).mp
    simpa only [perm_apply_inv] using ha'
  rw [List.formPerm_reverse]
  apply l.formPerm.injective
  rw [←h.2 _ hb,perm_apply_inv,perm_apply_inv]

end Release075

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Reverse the orientation of the whole filling, not just its boundary word. -/
noncomputable def mirror {w : List E} (D : TriangleFilling flip color face w)
    (hflip : Function.Involutive flip)
    (hface : ∀ a b c, face a b c → face (flip a) (flip c) (flip b)) :
    TriangleFilling flip color face (w.reverse.map flip) where
  Dart := D.Dart
  reverse := D.reverse
  next := D.next⁻¹
  reverse_involutive := D.reverse_involutive
  reverse_ne := D.reverse_ne
  label := flip ∘ D.label
  reverse_label := by
    intro a
    simp only [Function.comp_apply,D.reverse_label]
  color_next := by
    intro a
    simp only [Function.comp_apply,Perm.mul_apply,D.reverse_label]
    rw [hflip]
    have h := D.color_next (D.next⁻¹ a)
    simpa only [Perm.mul_apply,perm_apply_inv,D.reverse_label] using h.symm
  planar := D.planar.inv_right D.reverse_involutive
  boundary := D.boundary.reverse
  boundary_cycle := D.boundary_cycle.reverse
  boundary_word := by rw [←List.map_map,List.map_reverse,D.boundary_word]
  triangular := by
    intro a ha hn
    have ha' : ∃ b ∈ D.boundary, components D.reverse D.next a b := by
      obtain ⟨b,hb,hab⟩ := ha
      refine ⟨b,List.mem_reverse.mp hb,?_⟩
      rw [components_inv_right] at hab
      exact hab
    have ht := D.triangular a ha' (by simpa only [List.mem_reverse] using hn)
    have he := inv_cycle_three D.next ht.1
    refine ⟨he.2.2,?_,?_⟩
    · intro h
      apply ht.2.1
      have hh := congrArg D.next h
      simpa only [perm_apply_inv] using hh.symm
    · simp only [Function.comp_apply,he.1,he.2.1]
      exact hface _ _ _ ht.2.2

end Release075.TriangleFilling

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Existence of a finite labelled genus-zero filling. This abbreviation contains
no geometric assertion outside the fully specified finite map. -/
def Fillable (flip : E → E) (color : E → V) (face : E → E → E → Prop) (w : List E) : Prop :=
  Nonempty (TriangleFilling flip color face w)

namespace Fillable

theorem empty : Fillable flip color face [] := ⟨TriangleFilling.empty⟩

theorem rotateAppend {u v : List E} (h : Fillable flip color face (u++v)) :
    Fillable flip color face (v++u) := by
  obtain ⟨D⟩ := h
  have h' : Nonempty (TriangleFilling flip color face ((u++v).rotate u.length)) :=
    ⟨D.rotate u.length⟩
  simpa only [Fillable, List.rotate_append_length_eq] using h'

theorem mirror {w : List E} (h : Fillable flip color face w)
    (hi : Function.Involutive flip)
    (hf : ∀ a b c, face a b c → face (flip a) (flip c) (flip b)) :
    Fillable flip color face (w.reverse.map flip) := by
  obtain ⟨D⟩ := h
  exact ⟨D.mirror hi hf⟩

theorem foldHead (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    {e : E} {w : List E} (h : Fillable flip color face (e::flip e::w)) :
    Fillable flip color face w := by
  obtain ⟨D⟩ := h
  obtain ⟨b,bs,hb,he,hbs⟩ := List.map_eq_cons_iff.mp D.boundary_word
  obtain ⟨a,l,ha,hae,hl⟩ := List.map_eq_cons_iff.mp hbs
  have hbound : D.boundary = b::a::l := by rw [hb,ha]
  have hab : D.label a = flip (D.label b) := by rw [he,hae]
  have hf := D.fold hi hn hbound hab
  rwa [hl] at hf

theorem erase (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    (u v : List E) (e : E) (h : Fillable flip color face (u++e::flip e::v)) :
    Fillable flip color face (u++v) := by
  have h' : Fillable flip color face (e::flip e::(v++u)) := h.rotateAppend
  exact (h'.foldHead hi hn).rotateAppend

/-- Concatenate loops based at the same boundary corner. Empty words are allowed. -/
theorem app {u v : List E} (hu : Fillable flip color face u) (hv : Fillable flip color face v)
    (hbase : ∀ e es f fs, u = e::es → v = f::fs →
      color (flip e) = color (flip f)) : Fillable flip color face (u++v) := by
  cases u with
  | nil => exact hv
  | cons e es =>
    cases v with
    | nil => simpa only [List.append_nil] using hu
    | cons f fs =>
      obtain ⟨D⟩ := hu
      obtain ⟨D'⟩ := hv
      obtain ⟨a,l,ha,hal,_⟩ := List.map_eq_cons_iff.mp D.boundary_word
      obtain ⟨b,l',hb,hbl,_⟩ := List.map_eq_cons_iff.mp D'.boundary_word
      apply D.wedge D' ha hb
      rw [hal,hbl]
      exact hbase e es f fs rfl rfl

theorem backtrack (hi : Function.Involutive flip) (e : E) :
    Fillable flip color face [e,flip e] := ⟨TriangleFilling.backtrack hi e⟩

/-- Attach a stem, retaining its two directed traversals in the prescribed walk. -/
theorem stem (hi : Function.Involutive flip) {w : List E}
    (h : Fillable flip color face w) (e : E)
    (hc : ∀ a l, w = a::l → color (flip a) = color e) :
    Fillable flip color face (e::w++[flip e]) := by
  have hb : Fillable flip color face [flip e,e] := by
    have h' := backtrack (color := color) (face := face) hi (flip e)
    rwa [hi e] at h'
  have hh : Fillable flip color face ([flip e,e]++w) := hb.app h (by
    intro a l b m ha hm
    have hae : a = flip e := (List.cons.inj ha).1.symm
    rw [hae,hi]
    exact (hc b m hm).symm)
  exact rotateAppend (u := [flip e]) (v := e::w) hh

end Fillable
end Release075

end OAI
