import OAI.GroupTheory.Hyperbolic.Planarity

namespace OAI

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem cycleCount_mul_comm (f g : Perm A) : cycleCount (f*g) = cycleCount (g*f) :=
  cycleCount_intertwine (f*g) (g*f) g (fun _ => rfl)

omit [Fintype A] in
theorem components_comm (f g : Perm A) : components f g = components g f := sup_comm _ _

omit [Fintype A] in
theorem componentCount_comm (f g : Perm A) : componentCount f g = componentCount g f := by
  simp only [componentCount,components_comm f g]

theorem PlanarMap.symm {f g : Perm A} (h : PlanarMap f g) : PlanarMap g f := by
  simpa only [PlanarMap,cycleCount_mul_comm g f,componentCount_comm g f,
    Nat.add_comm (cycleCount g) (cycleCount f)] using h

/-- Cutting a cycle does not create positive genus. The component split is proved,
not presumed from a drawing. -/
theorem PlanarMap.swap_left {f g : Perm A} (hp : PlanarMap f g) {a b : A}
    (hab : f.SameCycle a b) : PlanarMap (Equiv.swap a b * f) g := by
  by_cases he : a = b
  · subst b
    rw [Equiv.swap_self]
    change PlanarMap (1*f) g
    rwa [one_mul]
  let f' := Equiv.swap a b * f
  have hc : cycleCount f' = cycleCount f + 1 := by
    simpa only [cycleCount,Nat.card_eq_fintype_card] using cycles_card_swap_of_same f he hab
  have hns : ¬ f'.SameCycle a b := swap_splits f he hab
  have hret : Equiv.swap a b * f' = f := by
    dsimp [f']; rw [←mul_assoc,Equiv.swap_mul_self,one_mul]
  have hj : components f g = joinPair (components f' g) a b := by
    have h := components_swap_of_not_same f' g hns
    rwa [hret] at h
  have hprod : Equiv.swap a b * (f'*g) = f*g := by rw [←mul_assoc,hret]
  by_cases hrel : components f' g a b
  · have hcomp : componentCount f g = componentCount f' g := by
      simp only [componentCount,hj,joinPair_eq_of_rel _ hrel]
    have hb := euler_bound f' g
    have hh := cycleCount_swap_le (f'*g) a b
    rw [hprod] at hh
    change PlanarMap f' g
    dsimp [PlanarMap] at hp ⊢
    omega
  · have hcomp : componentCount f g + 1 = componentCount f' g := by
      simpa only [componentCount,hj] using card_joinPair (components f' g) hrel
    have hh : cycleCount (f*g) + 1 = cycleCount (f'*g) := by
      have h := cycleCount_swap_of_not_same (f'*g)
        (fun h => hrel (sameCycle_mul_le_components f' g h))
      rwa [hprod] at h
    change PlanarMap f' g
    dsimp [PlanarMap] at hp ⊢
    omega

theorem PlanarMap.swap_right {f g : Perm A} (hp : PlanarMap f g) {a b : A}
    (hab : g.SameCycle a b) : PlanarMap f (Equiv.swap a b * g) :=
  (hp.symm.swap_left hab).symm

/-- Joining two separate planar components along a chosen cycle slot is planar. -/
theorem PlanarMap.join_left {f g : Perm A} (hp : PlanarMap f g) {a b : A}
    (hab : ¬ components f g a b) : PlanarMap (Equiv.swap a b * f) g := by
  have hnf : ¬ f.SameCycle a b := fun h => hab
    ((show Perm.SameCycle.setoid f ≤ components f g from le_sup_left) h)
  have hnp : ¬ (f*g).SameCycle a b := fun h => hab (sameCycle_mul_le_components f g h)
  have hc := cycleCount_swap_of_not_same f hnf
  have hd := cycleCount_swap_of_not_same (f*g) hnp
  have hj := components_swap_of_not_same f g hnf
  have hcomp : componentCount (Equiv.swap a b*f) g + 1 = componentCount f g := by
    simpa only [componentCount,hj] using card_joinPair (components f g) hab
  rw [←mul_assoc] at hd
  dsimp [PlanarMap] at hp ⊢
  omega

theorem PlanarMap.join_right {f g : Perm A} (hp : PlanarMap f g) {a b : A}
    (hab : ¬ components f g a b) : PlanarMap f (Equiv.swap a b * g) := by
  apply PlanarMap.symm
  apply hp.symm.join_left
  rwa [components_comm]

omit [Fintype A] in
theorem swap_color_preserving {C : Type*} (r f : Perm A) (color : A → C)
    (hc : ∀ a, color ((r*f) a) = color a) {a b : A}
    (hab : color (r a) = color (r b)) :
    ∀ z, color ((r*(Equiv.swap a b * f)) z) = color z := by
  intro z
  change (color ∘ r) (Equiv.swap a b (f z)) = color z
  rw [color_swap (color ∘ r) hab]
  exact hc z

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

omit [Fintype A] in
theorem rePair_color {C : Type*} (r f : Perm A) (hi : Function.Involutive r)
    (color : A → C) (hc : ∀ z, color ((r*f) z) = color z) {a b : A}
    (hl : color (r a) = color b) (hr : color a = color (r b)) :
    ∀ z, color ((rePair r a b*f) z) = color z := by
  intro z
  rw [rePair_vertex r f hi]
  change color (Equiv.swap (r a) b (Equiv.swap a (r b) ((r*f) z))) = color z
  rw [color_swap color hl,color_swap color hr,hc]

theorem planar_rePair_allow {C : Type*} (r f : Perm A)
    (hi : Function.Involutive r) (hn : ∀ z, r z ≠ z)
    (color : A → C) (hc : ∀ z, color ((r*f) z) = color z)
    {a b : A} (hab : color a ≠ color b)
    (hl : color (r a) = color b) (hr : color a = color (r b))
    (hcy : (r*f).SameCycle (r a) b) (hp : PlanarMap r f) :
    PlanarMap (rePair r a b) f := by
  by_cases h : r a = b
  · have hr : rePair r a b = r := by
      unfold rePair
      rw [h,Equiv.swap_self]
      change 1 * r * 1 = r
      simp
    rwa [hr]
  · exact planar_rePair r f hi hn color hc hab hl hr h hcy hp

omit [Fintype A] in
theorem rePair_other_edge (r : Perm A) (hi : Function.Involutive r) {a b z : A}
    (hza : z ≠ a) (hzb : z ≠ b) (hra : r z ≠ a) (hrb : r z ≠ b) :
    rePair r a b z = r z := by
  have hzra : z ≠ r a := by intro h; apply hra; rw [h,hi]
  simp only [rePair,Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hzra hzb,
    Equiv.swap_apply_of_ne_of_ne (r.injective.ne hza) hrb]

/-- Two oppositely oriented triangular faces. -/
noncomputable def dipoleFace : Perm (Fin 6) :=
  Equiv.swap 0 2 * Equiv.swap 0 1 * Equiv.swap 3 5 * Equiv.swap 3 4

@[simp] theorem dipoleFace_zero : dipoleFace 0 = 1 := by norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleFace_one : dipoleFace 1 = 2 := by norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleFace_two : dipoleFace 2 = 0 := by norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleFace_three : dipoleFace 3 = 4 := by norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleFace_four : dipoleFace 4 = 5 := by norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleFace_five : dipoleFace 5 = 3 := by norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]

noncomputable def dipoleReverse : Perm (Fin 6) :=
  Equiv.swap 0 3 * Equiv.swap 1 5 * Equiv.swap 2 4

@[simp] theorem dipoleReverse_zero : dipoleReverse 0 = 3 := by norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleReverse_one : dipoleReverse 1 = 5 := by norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleReverse_two : dipoleReverse 2 = 4 := by norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleReverse_three : dipoleReverse 3 = 0 := by norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleReverse_four : dipoleReverse 4 = 2 := by norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
@[simp] theorem dipoleReverse_five : dipoleReverse 5 = 1 := by norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]

theorem dipoleFace_count : cycleCount dipoleFace = 2 := by
  have h := card_eq_mul_cycles dipoleFace 3 (fun a => orbit_card_three dipoleFace a
    (by fin_cases a <;> norm_num [pow_succ',Perm.mul_apply,dipoleFace,Equiv.swap_apply_def,Fin.ext_iff])
    (by fin_cases a <;> norm_num [dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]))
  have hh : (6:ℕ) = 3 * cycleCount dipoleFace := by
    simpa only [Fintype.card_fin,cycleCount,Nat.card_eq_fintype_card] using h
  omega

omit [Fintype A] in
theorem range_invariant {B : Type*} (r : Perm A) (t : Perm B) (e : B → A)
    (he : ∀ b, r (e b) = e (t b)) (a : A) : r a ∈ Set.range e ↔ a ∈ Set.range e := by
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨t⁻¹ b,r.injective ?_⟩
    rw [he]
    change e (t (t.symm b)) = r a
    rwa [t.apply_symm_apply]
  · rintro ⟨b,rfl⟩
    exact ⟨t b,(he b).symm⟩

theorem components_rePair_le (r f : Perm A) {a b : A}
    (h : components r f (r a) b) : components (rePair r a b) f ≤ components r f := by
  rw [components_conjugate_swap r f h]
  exact le_joinPair _ _ _

/-- The actual two re-pairings isolate the cancellable six darts. This lemma
retains arbitrary outside reconnections; it does not postulate an empty outside
neighborhood. All unaffected face orbits, including the exterior, are unchanged. -/
theorem isolate_dipole {C : Type*} (r f : Perm A)
    (hi : Function.Involutive r) (hn : ∀ z, r z ≠ z)
    (color : A → C) (hc : ∀ z, color ((r*f) z) = color z)
    (e : Fin 6 ↪ A) (hf : ∀ j, f (e j) = e (dipoleFace j))
    (he : r (e 0) = e 3)
    (h10 : color (e 1) ≠ color (e 0)) (h21 : color (e 2) ≠ color (e 1))
    (h14 : color (e 1) = color (e 4)) (hp : PlanarMap r f) :
    ∃ r' : Perm A, Function.Involutive r' ∧ (∀ z, r' z ≠ z) ∧
      PlanarMap r' f ∧ (∀ z, color ((r'*f) z) = color z) ∧
      (∀ j, r' (e j) = e (dipoleReverse j)) ∧
      r' = rePair (rePair r (e 1) (e 5)) (e 2) (e 4) ∧
      components r' f ≤ components r f := by
  have h3 : r (e 3) = e 0 := by rw [← he,hi]
  have hne {i j : Fin 6} (h : i ≠ j) : e i ≠ e j := e.injective.ne h
  have hF0 : f (e 0) = e 1 := by simpa using hf 0
  have hF1 : f (e 1) = e 2 := by simpa using hf 1
  have hF2 : f (e 2) = e 0 := by simpa using hf 2
  have hF3 : f (e 3) = e 4 := by simpa using hf 3
  have hF4 : f (e 4) = e 5 := by simpa using hf 4
  have hF5 : f (e 5) = e 3 := by simpa using hf 5
  have h50 : color (e 5) = color (e 0) := by
    simpa only [Perm.mul_apply,hF5,h3] using (hc (e 5)).symm
  have h23 : color (e 2) = color (e 3) := by
    simpa only [Perm.mul_apply,hF2,he] using (hc (e 2)).symm
  have hl₁ : color (r (e 1)) = color (e 5) := by
    rw [h50]
    simpa only [Perm.mul_apply,hF0] using hc (e 0)
  have hr₁ : color (e 1) = color (r (e 5)) := by
    rw [h14]
    simpa only [Perm.mul_apply,hF4] using (hc (e 4)).symm
  have hcy₁ : (r*f).SameCycle (r (e 1)) (e 5) := by
    have hA : (r*f).SameCycle (e 0) (r (e 1)) := by
      simpa only [Perm.mul_apply,hF0] using
        (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl (r*f) (e 0)))
    have hB : (r*f).SameCycle (e 5) (e 0) := by
      simpa only [Perm.mul_apply,hF5,h3] using
        (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl (r*f) (e 5)))
    exact (hB.trans hA).symm
  let r₁ := rePair r (e 1) (e 5)
  have hi₁ : Function.Involutive r₁ := rePair_involutive r hi _ _
  have hn₁ : ∀ z, r₁ z ≠ z := rePair_ne r hn _ _
  have hp₁ : PlanarMap r₁ f := planar_rePair_allow r f hi hn color hc
    (by rwa [h50]) hl₁ hr₁ hcy₁ hp
  have hc₁ : ∀ z, color ((r₁*f) z) = color z := rePair_color r f hi color hc hl₁ hr₁
  have h01 : r₁ (e 0) = e 3 := by
    rw [rePair_other_edge r hi (hne (by decide)) (hne (by decide))
      (by rw [he]; exact hne (by decide)) (by rw [he]; exact hne (by decide)),he]
  have h31 : r₁ (e 3) = e 0 := by rw [← h01,hi₁]
  have h15 : r₁ (e 1) = e 5 := rePair_apply_a r hn (hne (by decide))
  have h51 : r₁ (e 5) = e 1 := by rw [← h15,hi₁]
  have hl₂ : color (r₁ (e 2)) = color (e 4) := by
    rw [← h14]
    simpa only [Perm.mul_apply,hF1] using hc₁ (e 1)
  have hr₂ : color (e 2) = color (r₁ (e 4)) := by
    rw [h23]
    simpa only [Perm.mul_apply,hF3] using (hc₁ (e 3)).symm
  have hcy₂ : (r₁*f).SameCycle (r₁ (e 2)) (e 4) := by
    have hA : (r₁*f).SameCycle (e 1) (r₁ (e 2)) := by
      simpa only [Perm.mul_apply,hF1] using
        (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl (r₁*f) (e 1)))
    have hB : (r₁*f).SameCycle (e 4) (e 1) := by
      simpa only [Perm.mul_apply,hF4,h51] using
        (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl (r₁*f) (e 4)))
    exact (hB.trans hA).symm
  let r₂ := rePair r₁ (e 2) (e 4)
  have hi₂ : Function.Involutive r₂ := rePair_involutive r₁ hi₁ _ _
  have hn₂ : ∀ z, r₂ z ≠ z := rePair_ne r₁ hn₁ _ _
  have hp₂ : PlanarMap r₂ f := planar_rePair_allow r₁ f hi₁ hn₁ color hc₁
    (by rwa [← h14]) hl₂ hr₂ hcy₂ hp₁
  have hc₂ : ∀ z, color ((r₂*f) z) = color z := rePair_color r₁ f hi₁ color hc₁ hl₂ hr₂
  have h02 : r₂ (e 0) = e 3 := by
    rw [rePair_other_edge r₁ hi₁ (hne (by decide)) (hne (by decide))
      (by rw [h01]; exact hne (by decide)) (by rw [h01]; exact hne (by decide)),h01]
  have h12 : r₂ (e 1) = e 5 := by
    rw [rePair_other_edge r₁ hi₁ (hne (by decide)) (hne (by decide))
      (by rw [h15]; exact hne (by decide)) (by rw [h15]; exact hne (by decide)),h15]
  have h24 : r₂ (e 2) = e 4 := rePair_apply_a r₁ hn₁ (hne (by decide))
  refine ⟨r₂,hi₂,hn₂,hp₂,hc₂,?_,rfl,?_⟩
  · intro j
    fin_cases j
    · simpa using h02
    · simpa using h12
    · simpa using h24
    · change r₂ (e 3) = e (dipoleReverse 3)
      simp only [dipoleReverse_three]; rw [← h02,hi₂]
    · change r₂ (e 4) = e (dipoleReverse 4)
      simp only [dipoleReverse_four]; rw [← h24,hi₂]
    · change r₂ (e 5) = e (dipoleReverse 5)
      simp only [dipoleReverse_five]; rw [← h12,hi₂]
  · exact (components_rePair_le r₁ f (sameCycle_mul_le_components r₁ f hcy₂)).trans
      (components_rePair_le r f (sameCycle_mul_le_components r f hcy₁))

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A B : Type*} [Fintype A] [Fintype B]

/-- Deleting an invariant finite family of face cycles has its exact effect on
area; no ambient topological disk is presumed in the count. -/
theorem cycleCount_delete_range (f : Perm A) (t : Perm B) (e : B ↪ A)
    (he : ∀ b, f (e b) = e (t b)) :
    cycleCount f = cycleCount t + cycleCount
      (f.subtypePerm (p := fun a => a ∉ Set.range e)
        (fun a => not_congr (range_invariant f t e he a))) := by
  have h := cycleCount_partition f (fun a => a ∈ Set.range e) (range_invariant f t e he)
  have hh : cycleCount t = cycleCount (f.subtypePerm (range_invariant f t e he)) := by
    apply cycleCount_intertwine t _ (Equiv.ofInjective e e.injective)
    intro b
    apply Subtype.ext
    exact (he b).symm
  rw [← hh] at h
  exact h

omit [Fintype A] [Fintype B] in
theorem rePair_labels {E : Type*} (r : Perm A) (label : A → E) (flip : E → E)
    (hr : ∀ a, label (r a) = flip (label a)) {a b : A}
    (hl : label (r a) = label b) :
    ∀ z, label (rePair r a b z) = flip (label z) := by
  intro z
  simp only [rePair,Perm.mul_apply,color_swap label hl,hr]

omit [Fintype B] in
theorem cancel_dipole {C : Type*} (r f : Perm A)
    (hi : Function.Involutive r) (hn : ∀ z, r z ≠ z)
    (color : A → C) (hc : ∀ z, color ((r*f) z) = color z)
    (e : Fin 6 ↪ A) (hf : ∀ j, f (e j) = e (dipoleFace j))
    (he : r (e 0) = e 3)
    (h10 : color (e 1) ≠ color (e 0)) (h21 : color (e 2) ≠ color (e 1))
    (h14 : color (e 1) = color (e 4)) (hp : PlanarMap r f) :
    ∃ (r' : Perm A) (hr : ∀ a, (r' a ∉ Set.range e) ↔ (a ∉ Set.range e)),
      Function.Involutive (r'.subtypePerm (p := fun a => a ∉ Set.range e) hr) ∧
      (∀ z, r'.subtypePerm (p := fun a => a ∉ Set.range e) hr z ≠ z) ∧
      PlanarMap (r'.subtypePerm (p := fun a => a ∉ Set.range e) hr)
        (f.subtypePerm (p := fun a => a ∉ Set.range e)
          (fun a => not_congr (range_invariant f dipoleFace e hf a))) ∧
      cycleCount (f.subtypePerm (p := fun a => a ∉ Set.range e)
        (fun a => not_congr (range_invariant f dipoleFace e hf a))) + 2 = cycleCount f := by
  obtain ⟨r',hi',hn',hp',hc',he',_,_⟩ := isolate_dipole r f hi hn color hc e hf he h10 h21 h14 hp
  let hr : ∀ a, (r' a ∉ Set.range e) ↔ (a ∉ Set.range e) :=
    fun a => not_congr (range_invariant r' dipoleReverse e he' a)
  refine ⟨r',hr,?_,?_,?_,?_⟩
  · intro a
    apply Subtype.ext
    exact hi' a.val
  · intro a h
    exact hn' a.val (congrArg Subtype.val h)
  · simpa only [PlanarMap, ← Nat.card_eq_fintype_card] using
      hp'.restrict (fun a => a ∉ Set.range e) hr
        (fun a => not_congr (range_invariant f dipoleFace e hf a))
  · have h := cycleCount_delete_range f dipoleFace e hf
    rw [dipoleFace_count] at h
    omega

end Release075.PermCycles

namespace Release075
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

theorem formPerm_append_cons (x y : A) (xs ys : List A) :
    (x :: xs ++ y :: ys).formPerm = (x :: xs).formPerm *
      Equiv.swap ((x::xs).getLast (by simp)) y * (y::ys).formPerm := by
  induction xs generalizing x with
  | nil => simp only [List.cons_append,List.nil_append,List.formPerm_cons_cons,List.formPerm_singleton,
      List.getLast_singleton,one_mul]
  | cons z xs ih =>
    simpa only [List.cons_append,List.formPerm_cons_cons,List.getLast_cons_cons,mul_assoc] using
      congrArg (fun p : Perm A => Equiv.swap x z * p) (ih z)

theorem formPerm_concat (x y : A) (xs ys : List A) (hy : y ∉ x::xs) :
    (x :: xs ++ y :: ys).formPerm =
      Equiv.swap x y * ((x::xs).formPerm * (y::ys).formPerm) := by
  rw [formPerm_append_cons,Equiv.mul_swap_eq_swap_mul,
    List.formPerm_apply_getLast,List.formPerm_apply_of_notMem hy,mul_assoc]

/-- A specified exterior cycle, including the empty boundary. Its entries are
incidences (darts), not necessarily distinct vertices or geometric edges. -/
def IsBoundary (f : Perm A) (l : List A) : Prop :=
  l.Nodup ∧ ∀ a ∈ l, f a = l.formPerm a

theorem IsBoundary.mem_iff {f : Perm A} {l : List A} (h : IsBoundary f l) (a : A) :
    f a ∈ l ↔ a ∈ l := by
  constructor
  · intro ha
    let b := l.formPerm.symm (f a)
    have hb : b ∈ l := by
      apply List.mem_of_formPerm_apply_mem (l := l)
      simpa only [b,Equiv.apply_symm_apply] using ha
    have he : f b = f a := by rw [h.2 b hb]; exact l.formPerm.apply_symm_apply _
    rwa [f.injective he] at hb
  · intro ha
    rw [h.2 a ha]
    exact List.formPerm_apply_mem_of_mem ha

theorem IsBoundary.not_mem_iff {f : Perm A} {l : List A} (h : IsBoundary f l) (a : A) :
    f a ∉ l ↔ a ∉ l := not_congr (h.mem_iff a)

theorem formPerm_embedding {B : Type*} (e : A ↪ B) (l : List A) (a : A) :
    (l.map e).formPerm (e a) = e (l.formPerm a) := by
  induction l using List.twoStepInduction with
  | nil => rfl
  | singleton x => rfl
  | cons_cons x y xs _ ih =>
    change Equiv.swap (e x) (e y) (((y::xs).map e).formPerm (e a)) =
      e (Equiv.swap x y ((y::xs).formPerm a))
    rw [ih y,e.injective.swap_apply]

theorem IsBoundary.conjugate {B : Type*} {f : Perm A} {g : Perm B} {l : List A}
    (h : IsBoundary f l) (e : A ↪ B) (he : ∀ a, g (e a) = e (f a)) :
    IsBoundary g (l.map e) := by
  refine ⟨h.1.map e.injective,?_⟩
  intro b hb
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
  rw [he,h.2 a ha]
  exact (formPerm_embedding e l a).symm

theorem IsBoundary.rotate {f : Perm A} {l : List A} (h : IsBoundary f l) (n : ℕ) :
    IsBoundary f (l.rotate n) := by
  refine ⟨List.nodup_rotate.mpr h.1,?_⟩
  intro a ha
  rw [List.formPerm_rotate l h.1 n]
  exact h.2 a (List.mem_rotate.mp ha)

end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem components_split_right_le (r f : Perm A) {a b : A}
    (h : f.SameCycle a b) : components r (Equiv.swap a b*f) ≤ components r f := by
  by_cases he : a = b
  · subst b
    simp only [Equiv.swap_self]
    change components r (1*f) ≤ components r f
    rw [one_mul]
  have hn := swap_splits f he h
  have hj := components_swap_of_not_same (Equiv.swap a b*f) r hn
  have hr : Equiv.swap a b * (Equiv.swap a b*f) = f := by
    rw [←mul_assoc,Equiv.swap_mul_self,one_mul]
  rw [hr,components_comm f r,components_comm (Equiv.swap a b*f) r] at hj
  rw [hj]
  exact le_joinPair _ a b

/-- Fold two consecutive inverse boundary incidences. Darts are first paired,
then split off as their own isolated tree component. The surviving outside word
is unchanged; no disjointness of the former outside partners is assumed. -/
theorem fold_pair {C E : Type*} (r f : Perm A)
    (hi : Function.Involutive r) (hn : ∀ a, r a ≠ a)
    (label : A → E) (flip : E → E) (hflip : Function.Involutive flip)
    (color : E → C) (hedge : ∀ e, color e ≠ color (flip e))
    (hl : ∀ a, label (r a) = flip (label a))
    (hc : ∀ a, color (label ((r*f) a)) = color (label a))
    (hp : PlanarMap r f) {a b : A} (hab : a ≠ b)
    (hf : f b = a) (he : label a = flip (label b)) :
    ∃ r' f' : Perm A,
      Function.Involutive r' ∧ (∀ z, r' z ≠ z) ∧ PlanarMap r' f' ∧
      (∀ z, label (r' z) = flip (label z)) ∧
      (∀ z, color (label ((r'*f') z)) = color (label z)) ∧
      r' a = b ∧ r' b = a ∧ f' a = b ∧ f' b = a ∧
      components r' f' ≤ components r f ∧
      (∀ z, f z ≠ b → f z ≠ f a → f' z = f z) ∧
      f' = Equiv.swap b (f a) * f := by
  have hleft : (color ∘ label) (r a) = (color ∘ label) b := by
    dsimp; rw [hl,he,hflip]
  have hright : (color ∘ label) a = (color ∘ label) (r b) := by
    dsimp; rw [hl,he]
  have hcol : (color ∘ label) a ≠ (color ∘ label) b := by
    dsimp; rw [he]; exact (hedge (label b)).symm
  have hcy : (r*f).SameCycle (r a) b := by
    have h := Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl (r*f) b)
    simpa only [Perm.mul_apply,hf] using h.symm
  let r' := rePair r a b
  have hi' := rePair_involutive r hi a b
  have hn' := rePair_ne r hn a b
  have hp' : PlanarMap r' f := planar_rePair_allow r f hi hn (color ∘ label) hc
    hcol hleft hright hcy hp
  have hc' : ∀ z, color (label ((r'*f) z)) = color (label z) :=
    rePair_color r f hi (color ∘ label) hc hleft hright
  have ha : r' a = b := rePair_apply_a r hn hab
  have hb : r' b = a := by rw [←ha,hi']
  have hlabel : ∀ z, label (r' z) = flip (label z) := rePair_labels r label flip hl
    (by rw [hl,he,hflip])
  let f' := Equiv.swap b (f a) * f
  have hcyf : f.SameCycle b (f a) := by
    have hh : f.SameCycle b a := by
      simpa only [hf] using (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl f b))
    exact Perm.sameCycle_apply_right.mpr hh
  have hp'' : PlanarMap r' f' := hp'.swap_right hcyf
  have ha' : f' a = b := Equiv.swap_apply_right b (f a)
  have hb' : f' b = a := by
    change Equiv.swap b (f a) (f b) = a
    rw [hf,Equiv.swap_apply_of_ne_of_ne hab]
    intro h
    have := f.injective (h.symm.trans hf.symm)
    exact hab this
  have hswap : color (label (r' b)) = color (label (r' (f a))) := by
    rw [hb]
    exact (hc' a).symm
  have hmono : components r' f' ≤ components r f :=
    (components_split_right_le r' f hcyf).trans
      (components_rePair_le r f (sameCycle_mul_le_components r f hcy))
  refine ⟨r',f',hi',hn',hp'',hlabel,
    swap_color_preserving r' f (color ∘ label) hc' hswap,ha,hb,ha',hb',hmono,?_,rfl⟩
  intro z hz₁ hz₂
  exact Equiv.swap_apply_of_ne_of_ne hz₁ hz₂

end Release075.PermCycles

end OAI
