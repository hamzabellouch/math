import OAI.GroupTheory.Hyperbolic.PermutationCycles

namespace OAI

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

/-- A swap supported in other colors leaves this entire orbit unchanged. -/
theorem swap_sameCycle_away {C : Type*} (f : Perm A) (color : A → C)
    (hcolor : ∀ z, color (f z) = color z) (a b x y : A)
    (ha : color x ≠ color a) (hb : color x ≠ color b) :
    (Equiv.swap a b * f).SameCycle x y ↔ f.SameCycle x y := by
  have hp (n : ℕ) : color ((f^n) x) = color x := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [pow_succ',Perm.mul_apply,hcolor] using ih
  have he (n : ℕ) : ((Equiv.swap a b * f)^n) x = (f^n) x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ',Perm.mul_apply,ih,pow_succ',Perm.mul_apply]
      change Equiv.swap a b (f ((f^n) x)) = f ((f^n) x)
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h
        exact ha (((hcolor _).trans (hp n)).symm.trans (congrArg color h))
      · intro h
        exact hb (((hcolor _).trans (hp n)).symm.trans (congrArg color h))
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : ℤ),by simpa only [zpow_natCast,he] using hn⟩
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : ℤ),by simpa only [zpow_natCast,he] using hn⟩

omit [Fintype A] in
theorem swap_rel (s : Setoid A) {a b : A} (hab : s a b) (z : A) :
    s z (Equiv.swap a b z) := by
  by_cases ha : z = a
  · subst z
    simpa only [Equiv.swap_apply_left] using hab
  by_cases hb : z = b
  · subst z
    simpa only [Equiv.swap_apply_right] using s.symm hab
  · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

theorem sameCycle_conjugate_swap_le (f : Perm A) (s : Setoid A) {a b : A}
    (hf : Perm.SameCycle.setoid f ≤ s) (hab : s a b) :
    Perm.SameCycle.setoid (Equiv.swap a b * f * Equiv.swap a b) ≤ s := by
  apply sameCycle_le_of_step
  intro z
  exact s.trans (swap_rel s hab z) (s.trans
    (hf (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl f _)))
    (swap_rel s hab _))

/-- A local re-pairing can only split off one further component, provided its
slots belonged to the same old component. This includes reconnected slots. -/
theorem components_conjugate_swap (f g : Perm A) {a b : A}
    (hab : components f g a b) :
    components f g = joinPair (components (Equiv.swap a b * f * Equiv.swap a b) g) a b := by
  let f' := Equiv.swap a b * f * Equiv.swap a b
  have hret : Equiv.swap a b * f' * Equiv.swap a b = f := by
    dsimp [f']
    simp only [mul_assoc,Equiv.swap_mul_self,mul_one]
    rw [← mul_assoc,Equiv.swap_mul_self,one_mul]
  have hnew : components f' g ≤ components f g := by
    apply sup_le
    · exact sameCycle_conjugate_swap_le f _ le_sup_left hab
    · exact le_sup_right
  apply le_antisymm
  · let s := joinPair (components f' g) a b
    have hs : components f' g ≤ s := le_joinPair _ a b
    apply sup_le
    · have hh := sameCycle_conjugate_swap_le f' s (le_trans le_sup_left hs) (joinPair_rel _ a b)
      rwa [hret] at hh
    · exact le_trans le_sup_right hs
  · exact joinPair_le hnew hab

/-- Change the pairing on two edges, creating pairs `(a,b)` and `(reverse a,
reverse b)`. Formulated by conjugation, so involutivity and absence of fixed
points are inherited rather than assumed for the result. -/
noncomputable def rePair (reverse : Perm A) (a b : A) : Perm A :=
  Equiv.swap (reverse a) b * reverse * Equiv.swap (reverse a) b

omit [Fintype A] in
theorem rePair_vertex (reverse face : Perm A) (hi : Function.Involutive reverse) (a b : A) :
    rePair reverse a b * face =
      Equiv.swap (reverse a) b * Equiv.swap a (reverse b) * (reverse * face) := by
  unfold rePair
  rw [mul_assoc (Equiv.swap (reverse a) b) reverse (Equiv.swap (reverse a) b),
    Equiv.mul_swap_eq_swap_mul reverse (reverse a) b,hi a]
  simp only [mul_assoc]

omit [Fintype A] in
theorem cycleCount_conj (f t : Perm A) : cycleCount (t*f*t⁻¹) = cycleCount f := by
  let e : Cycles f ≃ Cycles (t*f*t⁻¹) := Quotient.congr t (by
    intro x y
    change f.SameCycle x y ↔ (t*f*t⁻¹).SameCycle (t x) (t y)
    simp [Perm.sameCycle_conj])
  exact (Nat.card_congr e).symm

omit [Fintype A] in
theorem cycleCount_rePair (reverse : Perm A) (a b : A) :
    cycleCount (rePair reverse a b) = cycleCount reverse := by
  simpa only [rePair,Equiv.swap_inv] using cycleCount_conj reverse (Equiv.swap (reverse a) b)

omit [Fintype A] in
theorem rePair_involutive (reverse : Perm A) (hi : Function.Involutive reverse) (a b : A) :
    Function.Involutive (rePair reverse a b) := by
  intro z
  simp only [rePair,Perm.mul_apply,Equiv.swap_apply_self]
  rw [hi,Equiv.swap_apply_self]

omit [Fintype A] in
theorem rePair_ne (reverse : Perm A) (hn : ∀ z, reverse z ≠ z) (a b z : A) :
    rePair reverse a b z ≠ z := by
  intro h
  have hh := congrArg (Equiv.swap (reverse a) b) h
  simp only [rePair,Perm.mul_apply,Equiv.swap_apply_self] at hh
  exact hn _ hh

omit [Fintype A] in
theorem color_swap {C : Type*} (color : A → C) {a b : A}
    (hab : color a = color b) (z : A) : color (Equiv.swap a b z) = color z := by
  by_cases ha : z = a
  · subst z
    simpa only [Equiv.swap_apply_left] using hab.symm
  by_cases hb : z = b
  · subst z
    simpa only [Equiv.swap_apply_right] using hab
  · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

omit [Fintype A] in
theorem rePair_apply_a (reverse : Perm A) (hn : ∀ z, reverse z ≠ z) {a b : A}
    (hab : a ≠ b) : rePair reverse a b a = b := by
  simp only [rePair,Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne (hn a).symm hab,Equiv.swap_apply_left]

omit [Fintype A] in
theorem rePair_apply_reverse_a (reverse : Perm A) (hn : ∀ z, reverse z ≠ z) {a b : A}
    (hab : a ≠ b) : rePair reverse a b (reverse a) = reverse b := by
  simp only [rePair,Perm.mul_apply,Equiv.swap_apply_left]
  exact Equiv.swap_apply_of_ne_of_ne (reverse.injective.ne hab.symm) (hn b)

/-- Genus zero for every connected component, expressed without an embedding or
an unproved Jordan-curve theorem. This uses the universal Euler upper bound. -/
def PlanarMap (reverse face : Perm A) : Prop :=
  cycleCount reverse + cycleCount face + cycleCount (reverse*face) =
    Fintype.card A + 2*componentCount reverse face

theorem planar_rePair {C : Type*} (reverse face : Perm A)
    (hi : Function.Involutive reverse) (hn : ∀ z, reverse z ≠ z)
    (color : A → C) (hcolor : ∀ z, color ((reverse*face) z) = color z)
    {a b : A} (hab : color a ≠ color b)
    (hleft : color (reverse a) = color b) (hright : color a = color (reverse b))
    (hpair : reverse a ≠ b) (hcycle : (reverse*face).SameCycle (reverse a) b)
    (hplanar : PlanarMap reverse face) : PlanarMap (rePair reverse a b) face := by
  let v := reverse * face
  let r' := rePair reverse a b
  let v' := r' * face
  let u := Equiv.swap a (reverse b) * v
  have hab' : a ≠ b := fun h => hab (congrArg color h)
  have hcountR : cycleCount r' = cycleCount reverse := cycleCount_rePair reverse a b
  have hv' : v' = Equiv.swap (reverse a) b * u := rePair_vertex reverse face hi a b
  have haway1 : color (reverse a) ≠ color a := by rw [hleft]; exact hab.symm
  have haway2 : color (reverse a) ≠ color (reverse b) := by rw [← hright]; exact haway1
  have hucycle : u.SameCycle (reverse a) b :=
    (swap_sameCycle_away v color hcolor a (reverse b) (reverse a) b haway1 haway2).mpr hcycle
  have hsplit : cycleCount v' = cycleCount u + 1 := by
    have h := cycles_card_swap_of_same u hpair hucycle
    simpa only [← hv',cycleCount,Nat.card_eq_fintype_card] using h
  have hnab : a ≠ reverse b := by
    intro h
    apply hpair
    rw [h,hi b]
  have hge : cycleCount v ≤ cycleCount v' := by
    by_cases hc : v.SameCycle a (reverse b)
    · have hh := cycles_card_swap_of_same v hnab hc
      have hh' : cycleCount u = cycleCount v + 1 := by
        simpa only [cycleCount,Nat.card_eq_fintype_card] using hh
      omega
    · have hh : cycleCount u + 1 = cycleCount v := cycleCount_swap_of_not_same v hc
      omega
  have hj : components reverse face = joinPair (components r' face) (reverse a) b :=
    components_conjugate_swap reverse face (sameCycle_mul_le_components reverse face hcycle)
  have hvcolor : ∀ z, color (v' z) = color z := by
    intro z
    rw [hv']
    change color (Equiv.swap (reverse a) b (Equiv.swap a (reverse b) (v z))) = color z
    rw [color_swap color hleft,color_swap color hright,hcolor]
  by_cases hc : components r' face (reverse a) b
  · have hcomp : componentCount reverse face = componentCount r' face := by
      simp only [componentCount,hj,joinPair_eq_of_rel _ hc]
    have hbound := euler_bound r' face
    dsimp [PlanarMap] at hplanar ⊢
    change cycleCount reverse + cycleCount face + cycleCount v =
      Fintype.card A + 2*componentCount reverse face at hplanar
    change cycleCount r' + cycleCount face + cycleCount v' ≤
      Fintype.card A + 2*componentCount r' face at hbound
    change cycleCount r' + cycleCount face + cycleCount v' =
      Fintype.card A + 2*componentCount r' face
    omega
  · have hcomp : componentCount reverse face + 1 = componentCount r' face := by
      simpa only [componentCount,hj] using card_joinPair (components r' face) hc
    have hrab : components r' face a b := by
      have hh : r'.SameCycle a (r' a) :=
        Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl r' a)
      rw [rePair_apply_a reverse hn hab'] at hh
      exact (show Perm.SameCycle.setoid r' ≤ components r' face from le_sup_left) hh
    have hrAB : components r' face (reverse a) (reverse b) := by
      have hh : r'.SameCycle (reverse a) (r' (reverse a)) :=
        Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl r' (reverse a))
      rw [rePair_apply_reverse_a reverse hn hab'] at hh
      exact (show Perm.SameCycle.setoid r' ≤ components r' face from le_sup_left) hh
    have hsep : ¬ v'.SameCycle a (reverse b) := by
      intro h
      have hh := sameCycle_mul_le_components r' face h
      exact hc ((components r' face).trans hrAB ((components r' face).trans
        ((components r' face).symm hh) hrab))
    have hawayA : color a ≠ color (reverse a) := by rw [hleft]; exact hab
    have hret1 : Equiv.swap (reverse a) b * v' = u := by
      rw [hv',← mul_assoc,Equiv.swap_mul_self,one_mul]
    have hns : ¬ u.SameCycle a (reverse b) := by
      rw [← hret1]
      exact fun h => hsep ((swap_sameCycle_away v' color hvcolor (reverse a) b a
        (reverse b) hawayA hab).mp h)
    have hret2 : Equiv.swap a (reverse b) * u = v := by
      dsimp [u]
      rw [← mul_assoc,Equiv.swap_mul_self,one_mul]
    have hmerge := cycleCount_swap_of_not_same u hns
    rw [hret2] at hmerge
    dsimp [PlanarMap] at hplanar ⊢
    change cycleCount reverse + cycleCount face + cycleCount v =
      Fintype.card A + 2*componentCount reverse face at hplanar
    change cycleCount r' + cycleCount face + cycleCount v' =
      Fintype.card A + 2*componentCount r' face
    omega

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem invariant_pred_sameCycle (f : Perm A) (p : A → Prop)
    (hp : ∀ a, p (f a) ↔ p a) {a b : A} (h : f.SameCycle a b) : p a ↔ p b := by
  obtain ⟨n,rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pow_succ',Perm.mul_apply,hp] using ih

/-- Decompose the number of classes along a union of equivalence classes. -/
theorem card_quotient_partition (s : Setoid A) (p : A → Prop)
    (hp : ∀ a b, s a b → (p a ↔ p b)) :
    Nat.card (Quotient s) = Nat.card (Quotient (s.comap (Subtype.val : {a // p a} → A))) +
      Nat.card (Quotient (s.comap (Subtype.val : {a // ¬p a} → A))) := by
  let q : Quotient s → Prop := Quotient.lift p (fun a b h => propext (hp a b h))
  let e₁ := Equiv.subtypeQuotientEquivQuotientSubtype p (s₁ := s)
    (s₂ := s.comap Subtype.val) q (fun _ => Iff.rfl) (fun _ _ => Iff.rfl)
  let e₂ := Equiv.subtypeQuotientEquivQuotientSubtype (fun a => ¬p a) (s₁ := s)
    (s₂ := s.comap Subtype.val) (fun a => ¬ q a) (fun _ => Iff.rfl) (fun _ _ => Iff.rfl)
  rw [← Nat.card_congr e₁,← Nat.card_congr e₂,← Nat.card_sum]
  exact (Nat.card_congr (Equiv.sumCompl q)).symm

theorem cycleCount_partition (f : Perm A) (p : A → Prop) (hp : ∀ a, p (f a) ↔ p a) :
    cycleCount f = cycleCount (f.subtypePerm hp) +
      cycleCount (f.subtypePerm (p := fun a => ¬p a) (fun a => not_congr (hp a))) := by
  have h := card_quotient_partition (Perm.SameCycle.setoid f) p
    (fun _ _ h => invariant_pred_sameCycle f p hp h)
  have hs : Perm.SameCycle.setoid (f.subtypePerm hp) =
      (Perm.SameCycle.setoid f).comap Subtype.val := by
    ext; exact Perm.sameCycle_subtypePerm
  have ht : Perm.SameCycle.setoid (f.subtypePerm (p := fun a => ¬p a) (fun a => not_congr (hp a))) =
      (Perm.SameCycle.setoid f).comap Subtype.val := by
    ext; exact Perm.sameCycle_subtypePerm
  simpa only [cycleCount,Cycles,hs,ht] using h

/-- Restriction to an invariant set commutes with connected components. -/
theorem components_subtype (f g : Perm A) (p : A → Prop)
    (hf : ∀ a, p (f a) ↔ p a) (hg : ∀ a, p (g a) ↔ p a) :
    components (f.subtypePerm hf) (g.subtypePerm hg) = (components f g).comap Subtype.val := by
  have hinv : ∀ a b, components f g a b → (p a ↔ p b) := by
    intro a b h
    have hh : components f g ≤ Setoid.ker p := by
      apply sup_le
      · intro a b h; exact propext (invariant_pred_sameCycle f p hf h)
      · intro a b h; exact propext (invariant_pred_sameCycle g p hg h)
    exact propext_iff.mp (hh h)
  apply le_antisymm
  · apply sup_le
    · intro x y h
      exact (show Perm.SameCycle.setoid f ≤ components f g from le_sup_left)
        (Perm.sameCycle_subtypePerm.mp h)
    · intro x y h
      exact (show Perm.SameCycle.setoid g ≤ components f g from le_sup_right)
        (Perm.sameCycle_subtypePerm.mp h)
  · intro x y h
    change components f g x.val y.val at h
    rw [components,Setoid.sup_def] at h
    have hh (a b : A) (h : Relation.EqvGen (⇑(Perm.SameCycle.setoid f) ⊔
        ⇑(Perm.SameCycle.setoid g)) a b) :
        ∀ ha : p a, ∀ hb : p b,
          components (f.subtypePerm hf) (g.subtypePerm hg) ⟨a,ha⟩ ⟨b,hb⟩ := by
      induction h with
      | rel a b h =>
        intro ha hb
        rcases h with h | h
        · exact (show Perm.SameCycle.setoid (f.subtypePerm hf) ≤ _ from le_sup_left)
            (Perm.sameCycle_subtypePerm.mpr h)
        · exact (show Perm.SameCycle.setoid (g.subtypePerm hg) ≤ _ from le_sup_right)
            (Perm.sameCycle_subtypePerm.mpr h)
      | refl a => intros; exact (components (f.subtypePerm hf) (g.subtypePerm hg)).refl _
      | symm a b h ih => intros; exact (components (f.subtypePerm hf) (g.subtypePerm hg)).symm (ih _ _)
      | trans a b c hab hbc ih₁ ih₂ =>
        intro ha hc
        have hab' : components f g a b := by rwa [components,Setoid.sup_def]
        have hb : p b := (hinv a b hab').mp ha
        exact (components (f.subtypePerm hf) (g.subtypePerm hg)).trans (ih₁ ha hb) (ih₂ hb hc)
    exact hh _ _ h x.property y.property

theorem componentCount_partition (f g : Perm A) (p : A → Prop)
    (hf : ∀ a, p (f a) ↔ p a) (hg : ∀ a, p (g a) ↔ p a) :
    componentCount f g = componentCount (f.subtypePerm hf) (g.subtypePerm hg) +
      componentCount (f.subtypePerm (p := fun a => ¬p a) (fun a => not_congr (hf a)))
        (g.subtypePerm (p := fun a => ¬p a) (fun a => not_congr (hg a))) := by
  have hh : components f g ≤ Setoid.ker p := by
    apply sup_le
    · intro a b h; exact propext (invariant_pred_sameCycle f p hf h)
    · intro a b h; exact propext (invariant_pred_sameCycle g p hg h)
  simpa only [componentCount,components_subtype] using
    card_quotient_partition (components f g) p (fun _ _ h => propext_iff.mp (hh h))

/-- Genus-zero is inherited by every union of connected components. -/
theorem PlanarMap.restrict {f g : Perm A} (h : PlanarMap f g) (p : A → Prop)
    (hf : ∀ a, p (f a) ↔ p a) (hg : ∀ a, p (g a) ↔ p a) :
    PlanarMap (f.subtypePerm hf) (g.subtypePerm hg) := by
  have hfg : ∀ a, p ((f*g) a) ↔ p a := fun a => (hf (g a)).trans (hg a)
  have hF := cycleCount_partition f p hf
  have hG := cycleCount_partition g p hg
  have hFG := cycleCount_partition (f*g) p hfg
  rw [← Perm.subtypePerm_mul f g hf hg,
    ← Perm.subtypePerm_mul (p := fun a => ¬p a) f g (fun a => not_congr (hf a))
      (fun a => not_congr (hg a))] at hFG
  have hC := componentCount_partition f g p hf hg
  have hA : Fintype.card A = Fintype.card {a // p a} + Fintype.card {a // ¬p a} := by
    simpa only [Fintype.card_sum] using (Fintype.card_congr (Equiv.sumCompl p)).symm
  have hB := euler_bound (f.subtypePerm (p := fun a => ¬p a) (fun a => not_congr (hf a)))
    (g.subtypePerm (p := fun a => ¬p a) (fun a => not_congr (hg a)))
  have hB' := euler_bound (f.subtypePerm hf) (g.subtypePerm hg)
  unfold PlanarMap at h ⊢
  omega

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A B : Type*} [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
theorem pow_intertwine (f : Perm A) (g : Perm B) (e : A → B)
    (he : ∀ a, e (f a) = g (e a)) (n : ℕ) (a : A) :
    e ((f^n) a) = (g^n) (e a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',Perm.mul_apply,he,ih,pow_succ',Perm.mul_apply]

theorem sameCycle_intertwine (f : Perm A) (g : Perm B) (e : A ≃ B)
    (he : ∀ a, e (f a) = g (e a)) (a b : A) : f.SameCycle a b ↔ g.SameCycle (e a) (e b) := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n:ℤ),by rw [zpow_natCast,← pow_intertwine f g e he,hn]⟩
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n:ℤ),e.injective ?_⟩
    rwa [zpow_natCast,pow_intertwine f g e he]

theorem cycleCount_intertwine (f : Perm A) (g : Perm B) (e : A ≃ B)
    (he : ∀ a, e (f a) = g (e a)) : cycleCount f = cycleCount g :=
  Nat.card_congr (Quotient.congr e (sameCycle_intertwine f g e he))

omit [Fintype B] in
theorem components_map (f g : Perm A) (f' g' : Perm B) (e : A → B)
    (hf : ∀ a, e (f a) = f' (e a)) (hg : ∀ a, e (g a) = g' (e a)) :
    components f g ≤ (components f' g').comap e := by
  apply sup_le
  · apply sameCycle_le_of_step
    intro a
    change components f' g' (e a) (e (f a))
    rw [hf]
    exact (show Perm.SameCycle.setoid f' ≤ components f' g' from le_sup_left)
      (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl f' _))
  · apply sameCycle_le_of_step
    intro a
    change components f' g' (e a) (e (g a))
    rw [hg]
    exact (show Perm.SameCycle.setoid g' ≤ components f' g' from le_sup_right)
      (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl g' _))

theorem components_intertwine (f g : Perm A) (f' g' : Perm B) (e : A ≃ B)
    (hf : ∀ a, e (f a) = f' (e a)) (hg : ∀ a, e (g a) = g' (e a)) (a b : A) :
    components f g a b ↔ components f' g' (e a) (e b) := by
  constructor
  · exact fun h => components_map f g f' g' e hf hg h
  · intro h
    have hf' (b : B) : e.symm (f' b) = f (e.symm b) := by
      apply e.injective
      simp only [e.apply_symm_apply,hf]
    have hg' (b : B) : e.symm (g' b) = g (e.symm b) := by
      apply e.injective
      simp only [e.apply_symm_apply,hg]
    have hh := components_map f' g' f g e.symm hf' hg' h
    simpa only [Setoid.comap_rel,e.symm_apply_apply] using hh

theorem componentCount_intertwine (f g : Perm A) (f' g' : Perm B) (e : A ≃ B)
    (hf : ∀ a, e (f a) = f' (e a)) (hg : ∀ a, e (g a) = g' (e a)) :
    componentCount f g = componentCount f' g' :=
  Nat.card_congr (Quotient.congr e (components_intertwine f g f' g' e hf hg))

def leftPred : A ⊕ B → Prop := Sum.elim (fun _ => True) (fun _ => False)

def leftEquiv : {z : A ⊕ B // leftPred z} ≃ A where
  toFun z := match z with
    | ⟨.inl a,_⟩ => a
    | ⟨.inr _,h⟩ => False.elim h
  invFun a := ⟨.inl a,True.intro⟩
  left_inv z := by rcases z with ⟨a|b,h⟩; rfl; exact h.elim
  right_inv _ := rfl

def rightEquiv : {z : A ⊕ B // ¬leftPred z} ≃ B where
  toFun z := match z with
    | ⟨.inl _,h⟩ => False.elim (h True.intro)
    | ⟨.inr b,_⟩ => b
  invFun b := ⟨.inr b,not_false⟩
  left_inv z := by rcases z with ⟨a|b,h⟩; exact (h True.intro).elim; rfl
  right_inv _ := rfl

omit [Fintype A] [Fintype B] in
theorem leftPred_sumCongr (f : Perm A) (g : Perm B) (z : A ⊕ B) :
    leftPred ((f.sumCongr g) z) ↔ leftPred z := by cases z <;> rfl

omit [Fintype A] [Fintype B] in
theorem leftEquiv_intertwine (f : Perm A) (g : Perm B)
    (z : {z : A ⊕ B // leftPred z}) :
    leftEquiv ((f.sumCongr g).subtypePerm (leftPred_sumCongr f g) z) = f (leftEquiv z) := by
  rcases z with ⟨a|b,h⟩; rfl; exact h.elim

omit [Fintype A] [Fintype B] in
theorem rightEquiv_intertwine (f : Perm A) (g : Perm B)
    (z : {z : A ⊕ B // ¬ leftPred z}) :
    rightEquiv ((f.sumCongr g).subtypePerm (p := fun z => ¬leftPred z)
      (fun z => not_congr (leftPred_sumCongr f g z)) z) = g (rightEquiv z) := by
  rcases z with ⟨a|b,h⟩; exact (h True.intro).elim; rfl

theorem cycleCount_sum (f : Perm A) (g : Perm B) :
    cycleCount (f.sumCongr g) = cycleCount f + cycleCount g := by
  rw [cycleCount_partition (f.sumCongr g) leftPred (leftPred_sumCongr f g),
    cycleCount_intertwine _ f leftEquiv (leftEquiv_intertwine f g),
    cycleCount_intertwine _ g rightEquiv (rightEquiv_intertwine f g)]

theorem componentCount_sum (f g : Perm A) (f' g' : Perm B) :
    componentCount (f.sumCongr f') (g.sumCongr g') = componentCount f g + componentCount f' g' := by
  rw [componentCount_partition (f.sumCongr f') (g.sumCongr g') leftPred
    (leftPred_sumCongr f f') (leftPred_sumCongr g g'),
    componentCount_intertwine _ _ f g leftEquiv (leftEquiv_intertwine f f')
      (leftEquiv_intertwine g g'),
    componentCount_intertwine _ _ f' g' rightEquiv (rightEquiv_intertwine f f')
      (rightEquiv_intertwine g g')]

omit [Fintype A] [Fintype B] in
theorem sum_mul (f g : Perm A) (f' g' : Perm B) :
    (f.sumCongr f') * (g.sumCongr g') = (f*g).sumCongr (f'*g') := by
  ext z; cases z <;> rfl

theorem PlanarMap.sum {f g : Perm A} {f' g' : Perm B}
    (h : PlanarMap f g) (h' : PlanarMap f' g') :
    PlanarMap (f.sumCongr f') (g.sumCongr g') := by
  unfold PlanarMap at *
  rw [sum_mul,cycleCount_sum,cycleCount_sum,cycleCount_sum,componentCount_sum,Fintype.card_sum]
  omega

end Release075.PermCycles

end OAI
