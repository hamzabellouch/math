import OAI.GroupTheory.Hyperbolic.Words

namespace OAI

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

noncomputable def activeCount {w : List E} (D : TriangleFilling flip color face w) : ℕ :=
  (Finset.univ.filter D.Active).card

/-- The six oriented incidences of two faces which cancel across their common
edge. Outside partners may reconnect arbitrarily elsewhere in the filling. -/
structure Dipole {w : List E} (D : TriangleFilling flip color face w) where
  dart : Fin 6 ↪ D.Dart
  next_dart : ∀ j, D.next (dart j) = dart (dipoleFace j)
  reverse_zero : D.reverse (dart 0) = dart 3
  not_boundary : ∀ j, dart j ∉ D.boundary
  active : D.Active (dart 0)
  color10 : color (D.label (dart 1)) ≠ color (D.label (dart 0))
  color21 : color (D.label (dart 2)) ≠ color (D.label (dart 1))
  label51 : D.label (dart 5) = flip (D.label (dart 1))
  label42 : D.label (dart 4) = flip (D.label (dart 2))

/-- A labeled cancellation decreases the number of active darts. The isolated
pair remains harmlessly as a component disjoint from the prescribed boundary. -/
theorem Dipole.cancel {w : List E} {D : TriangleFilling flip color face w} (P : D.Dipole) :
    ∃ D' : TriangleFilling flip color face w, D'.activeCount < D.activeCount := by
  let e := P.dart
  have h14 : color (D.label (e 1)) = color (D.label (e 4)) := by
    have h := D.color_next (P.dart 1)
    simp only [Perm.mul_apply,P.next_dart,dipoleFace_one,D.reverse_label] at h
    exact h.symm.trans (congrArg color P.label42.symm)
  obtain ⟨r',hi',hn',hp',hc',he',heq,hm⟩ :=
    isolate_dipole D.reverse D.next D.reverse_involutive D.reverse_ne
      (color ∘ D.label) D.color_next e P.next_dart P.reverse_zero
      P.color10 P.color21 h14 D.planar
  have hl₁ : ∀ z, D.label (rePair D.reverse (e 1) (e 5) z) = flip (D.label z) :=
    rePair_labels D.reverse D.label flip D.reverse_label
      ((D.reverse_label (e 1)).trans P.label51.symm)
  have hl' : ∀ z, D.label (r' z) = flip (D.label z) := by
    rw [heq]
    exact rePair_labels _ D.label flip hl₁ ((hl₁ (e 2)).trans P.label42.symm)
  let D' : TriangleFilling flip color face w := {
    Dart := D.Dart
    reverse := r'
    next := D.next
    reverse_involutive := hi'
    reverse_ne := hn'
    label := D.label
    reverse_label := hl'
    color_next := hc'
    planar := hp'
    boundary := D.boundary
    boundary_cycle := D.boundary_cycle
    boundary_word := D.boundary_word
    triangular := by
      intro z hz hn
      obtain ⟨b,hb,hzb⟩ := hz
      exact D.triangular z ⟨b,hb,hm hzb⟩ hn }
  refine ⟨D',?_⟩
  have hle : ∀ z, D'.Active z → D.Active z := by
    rintro z ⟨b,hb,hzb⟩
    exact ⟨b,hb,hm hzb⟩
  have hnot : ¬ D'.Active (e 0) := by
    rintro ⟨b,hb,heb⟩
    have hmem : b ∈ Set.range e := (components_pred r' D.next (fun z => z ∈ Set.range e)
      (range_invariant r' dipoleReverse e he')
      (range_invariant D.next dipoleFace e P.next_dart) heb).mp ⟨0,rfl⟩
    obtain ⟨j,rfl⟩ := hmem
    exact P.not_boundary j hb
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro z hz
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hz ⊢
    exact hle z hz
  · intro he
    have hmem : e 0 ∈ Finset.univ.filter D.Active := by
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact P.active
    rw [← he] at hmem
    exact hnot (Finset.mem_filter.mp hmem).2

/-- Minimizing active size, not an assumed reduced-diagram axiom, produces a
filling with no cancellable adjacent labelled pair. -/
theorem exists_noDipole {w : List E} (h : Fillable flip color face w) :
    ∃ D : TriangleFilling flip color face w, IsEmpty D.Dipole := by
  have hex : ∃ n : ℕ, ∃ D : TriangleFilling flip color face w, D.activeCount = n := by
    obtain ⟨D⟩ := h
    exact ⟨D.activeCount,D,rfl⟩
  obtain ⟨D,hD⟩ := Nat.find_spec hex
  refine ⟨D,⟨fun P => ?_⟩⟩
  obtain ⟨D',hless⟩ := P.cancel
  have hmin := Nat.find_min' hex (show ∃ A : TriangleFilling flip color face w,
      A.activeCount = D'.activeCount from ⟨D',rfl⟩)
  omega

end Release075.TriangleFilling

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

noncomputable def triangleEmbedding (f : Perm A) (a : A)
    (hp : (f^3) a = a) (hn : f a ≠ a) : Fin 3 ↪ A where
  toFun i := (f^i.val) a
  inj' := by
    intro i j h
    apply Fin.ext
    have hm : Function.minimalPeriod (f : A → A) a = 3 :=
      (orbit_card_eq_minimalPeriod f a).symm.trans (orbit_card_three f a hp hn)
    exact Function.iterate_injOn_Iio_minimalPeriod (f := (f : A → A))
      (x := a) (by rw [hm]; exact i.isLt) (by rw [hm]; exact j.isLt) h

noncomputable def trianglePairEmbedding (f : Perm A) (a b : A)
    (hpa : (f^3) a = a) (hna : f a ≠ a) (hpb : (f^3) b = b) (hnb : f b ≠ b)
    (hab : ¬ f.SameCycle a b) : Fin 6 ↪ A :=
  let ca := triangleEmbedding f a hpa hna
  let cb := triangleEmbedding f b hpb hnb
  let e : Fin 3 ⊕ Fin 3 ↪ A := {
    toFun := Sum.elim ca cb
    inj' := by
      intro i j h
      cases i with
      | inl i => cases j with
        | inl j => exact congrArg Sum.inl (ca.injective h)
        | inr j =>
          change ca i = cb j at h
          have hh : f.SameCycle a b := by
            have hi : f.SameCycle a (ca i) := (Perm.SameCycle.refl f a).pow_right
            have hj : f.SameCycle b (cb j) := (Perm.SameCycle.refl f b).pow_right
            exact hi.trans (by rw [h]; exact hj.symm)
          exact (hab hh).elim
      | inr i => cases j with
        | inl j =>
          change cb i = ca j at h
          have hh : f.SameCycle b a := by
            have hi : f.SameCycle b (cb i) := (Perm.SameCycle.refl f b).pow_right
            have hj : f.SameCycle a (ca j) := (Perm.SameCycle.refl f a).pow_right
            exact hi.trans (by rw [h]; exact hj.symm)
          exact (hab hh.symm).elim
        | inr j => exact congrArg Sum.inr (cb.injective h) }
  finSumFinEquiv.symm.toEmbedding.trans e

 theorem trianglePairEmbedding_values (f : Perm A) (a b : A)
    (hpa : (f^3) a = a) (hna : f a ≠ a) (hpb : (f^3) b = b) (hnb : f b ≠ b)
    (hab : ¬ f.SameCycle a b) :
    let e := trianglePairEmbedding f a b hpa hna hpb hnb hab
    e 0 = a ∧ e 1 = f a ∧ e 2 = (f^2) a ∧
    e 3 = b ∧ e 4 = f b ∧ e 5 = (f^2) b := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable {w : List E} (D : TriangleFilling flip color face w)

/-- A genuinely triangular face cannot use both orientations of one geometric
edge: its three differently colored vertices and the endpoint matching forbid it. -/
theorem reverse_not_sameCycle (a : D.Dart) (ha : D.Active a) (hna : a ∉ D.boundary)
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a) :
    ¬ D.next.SameCycle a (D.reverse a) := by
  obtain ⟨hp,hn,hface⟩ := D.triangular a ha hna
  obtain ⟨h01,h12,h20⟩ := hf _ _ _ hface
  intro h
  have hm : D.reverse a ∈ orbit D.next a := (mem_orbit _ _ _).mpr h
  rw [orbit_eq_image D.next a (by omega : 0 < 3) hp] at hm
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
  fin_cases i
  · exact D.reverse_ne a hi.symm
  · have h := D.color_next ((D.next^2) a)
    have h3 : D.next ((D.next^2) a) = a := by simpa only [pow_succ',Perm.mul_apply] using hp
    simp only [Perm.mul_apply,h3,← hi] at h
    exact h12 h
  · have h := D.color_next (D.next a)
    have hr : D.reverse ((D.next^2) a) = a := by rw [hi,D.reverse_involutive]
    change color (D.label (D.reverse ((D.next^2) a))) = color (D.label (D.next a)) at h
    rw [hr] at h
    exact h01 h

/-- Internal reversal of a link walk creates a cancellable pair, when the face
labels are determined by two consecutive sides. -/
theorem dipole_of_link_backtrack
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (hflip : ∀ e, flip (flip e) = e)
    (hmirror : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (hunique : ∀ a b c c', face a b c → face a b c' → c = c')
    (x : D.Dart) (hx : D.Active x) (hnx : x ∉ D.boundary)
    (hnb : (D.reverse*D.next) x ∉ D.boundary)
    (hback : D.label x = D.label ((D.reverse*D.next) ((D.reverse*D.next) x))) :
    Nonempty D.Dipole := by
  let a := D.next x
  let b := D.reverse a
  have ha : D.Active a := (D.active_next x).mpr hx
  have hna : a ∉ D.boundary := (D.boundary_cycle.not_mem_iff x).mpr hnx
  have hb : D.Active b := (D.active_reverse a).mpr ha
  obtain ⟨hp,hne,hfa⟩ := D.triangular a ha hna
  obtain ⟨hp',hne',hfb⟩ := D.triangular b hb hnb
  have hx3 := (D.triangular x hx hnx).1
  have hax : (D.next^2) a = x := by
    change (D.next^2) (D.next x) = x
    simpa only [pow_succ,Perm.mul_apply] using hx3
  have h42 : D.label (D.next b) = flip (D.label ((D.next^2) a)) := by
    have he : D.label x = flip (D.label (D.next b)) := hback.trans (D.reverse_label (D.next b))
    rw [hax,he,hflip]
  have h51 : D.label ((D.next^2) b) = flip (D.label (D.next a)) := by
    apply hunique (D.label b) (D.label (D.next b)) _ _ hfb
    rw [h42]
    change face (D.label (D.reverse a)) (flip (D.label ((D.next^2) a))) (flip (D.label (D.next a)))
    rw [D.reverse_label]
    exact hmirror _ _ _ hfa
  have hab : ¬ D.next.SameCycle a b := D.reverse_not_sameCycle a ha hna hf
  let e := trianglePairEmbedding D.next a b hp hne hp' hne' hab
  obtain ⟨he0,he1,he2,he3,he4,he5⟩ := trianglePairEmbedding_values D.next a b hp hne hp' hne' hab
  have hnext : ∀ j, D.next (e j) = e (dipoleFace j) := by
    have h3 : D.next ((D.next^2) a) = a := by simpa only [pow_succ',Perm.mul_apply] using hp
    have h3' : D.next ((D.next^2) b) = b := by simpa only [pow_succ',Perm.mul_apply] using hp'
    intro j
    fin_cases j <;> first | rfl | exact h3 | exact h3'
  have hnb' : b ∉ D.boundary := hnb
  have hn2a : (D.next^2) a ∉ D.boundary := by
    rw [hax]; exact hnx
  have hn1a : D.next a ∉ D.boundary := (D.boundary_cycle.not_mem_iff a).mpr hna
  have hn1b : D.next b ∉ D.boundary := (D.boundary_cycle.not_mem_iff b).mpr hnb'
  have hn2b : (D.next^2) b ∉ D.boundary :=
    (D.boundary_cycle.not_mem_iff (D.next b)).mpr hn1b
  obtain ⟨h01,h12,_⟩ := hf _ _ _ hfa
  refine ⟨{
    dart := e
    next_dart := hnext
    reverse_zero := by rw [he0,he3]
    not_boundary := by
      intro j
      fin_cases j <;> assumption
    active := by rw [he0]; exact ha
    color10 := by rw [he1,he0]; exact h01.symm
    color21 := by rw [he2,he1]; exact h12.symm
    label51 := by rw [he5,he1]; exact h51
    label42 := by rw [he4,he2]; exact h42 }⟩

theorem noDipole_link_reduced
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (hflip : ∀ e, flip (flip e) = e)
    (hmirror : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (hunique : ∀ a b c c', face a b c → face a b c' → c = c')
    (hD : IsEmpty D.Dipole)
    (x : D.Dart) (hx : D.Active x) (hnx : x ∉ D.boundary)
    (hnb : (D.reverse*D.next) x ∉ D.boundary) :
    D.label x ≠ D.label ((D.reverse*D.next) ((D.reverse*D.next) x)) := by
  intro h
  obtain ⟨P⟩ := D.dipole_of_link_backtrack hf hflip hmirror hunique x hx hnx hnb h
  exact hD.false P

end Release075.TriangleFilling

namespace Release075
namespace CyclicLink
variable {A V : Type*} {G : SimpleGraph V}

/-- The actual link walk traced by successive corners, without assuming its image
is simple. This is why reduced closed walks, rather than only cycles, are needed. -/
def walk (f : A → A) (label : A → V) (adj : ∀ a, G.Adj (label a) (label (f a)))
    (n : ℕ) (a : A) : G.Walk (label a) (label (f^[n] a)) :=
  match n with
  | 0 => .nil
  | n+1 => (walk f label adj n (f a)).cons (adj a)

@[simp] theorem length_walk (f : A → A) (label : A → V)
    (adj : ∀ a, G.Adj (label a) (label (f a))) (n : ℕ) (a : A) :
    (walk f label adj n a).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [walk,ih]

theorem getVert_walk (f : A → A) (label : A → V)
    (adj : ∀ a, G.Adj (label a) (label (f a))) (n : ℕ) (a : A)
    (i : ℕ) (hi : i ≤ n) : (walk f label adj n a).getVert i = label (f^[i] a) := by
  induction n generalizing a i with
  | zero =>
    have : i = 0 := by omega
    subst i
    rfl
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [walk,SimpleGraph.Walk.getVert_cons_succ,Function.iterate_succ_apply]
        using ih (f a) i (by omega)

theorem reduced_walk (f : A → A) (label : A → V)
    (adj : ∀ a, G.Adj (label a) (label (f a)))
    (reduced : ∀ a, label a ≠ label (f (f a))) (n : ℕ) (a : A) :
    ReducedWalk (walk f label adj n a) := by
  intro i hi he
  simp only [length_walk] at hi
  rw [getVert_walk _ _ _ _ _ _ (by omega),getVert_walk _ _ _ _ _ _ hi] at he
  apply reduced (f^[i] a)
  simpa only [show i+2 = (i+1)+1 by omega,Function.iterate_succ_apply'] using he

/-- A finite corner orbit mapping without link reversals has at least the link's
actual girth. No injectivity of the whole orbit image is needed. -/
theorem orbit_card_ge [Fintype A] (f : Equiv.Perm A) (label : A → V)
    (adj : ∀ a, G.Adj (label a) (label (f a)))
    (reduced : ∀ a, label a ≠ label (f (f a)))
    (k : ℕ) (hgirth : ∀ v (p : G.Walk v v), p.IsCycle → k ≤ p.length) (a : A) :
    k ≤ (PermCycles.orbit f a).card := by
  rw [PermCycles.orbit_card_eq_minimalPeriod]
  let n := Function.minimalPeriod (f : A → A) a
  have hn : 0 < n := PermCycles.minimalPeriod_pos f a
  have hp : f^[n] a = a := Function.iterate_minimalPeriod
  let p := (walk f label adj n a).copy rfl (congrArg label hp)
  have hr : ReducedWalk p := by
    intro i hi
    simpa only [p,SimpleGraph.Walk.length_copy,SimpleGraph.Walk.getVert_copy] using
      reduced_walk f label adj reduced n a i (by simpa only [p,SimpleGraph.Walk.length_copy] using hi)
  have hh := reduced_closed_length_ge k hgirth p (by simpa [p] using hn) hr
  simpa [p] using hh

end CyclicLink
end Release075

end OAI
