import Mathlib

namespace OAI


/-!
Sequential limits, injective induced maps, and finite presentation of mapping tori.
-/


namespace FiniteAlgebraicEnvelopes.SequentialLimit

variable {Q : Type*} [Group Q] (f : Monoid.End Q)

def transition (i j : ℕ) (_ : i ≤ j) : Q →* Q := f ^ (j - i)

instance : DirectedSystem (fun _ : ℕ => Q) (transition f · · ·) where
  map_self {i} x := by
    change (f ^ (i-i)) x = x
    rw [Nat.sub_self, pow_zero]
    rfl
  map_map {k j i} hij hjk x := by
    change ((f ^ (k-j)) * (f ^ (j-i))) x = (f ^ (k-i)) x
    rw [← pow_add]
    congr 2
    omega

abbrev Limit := DirectLimit (fun _ : ℕ => Q) (transition f)

noncomputable def of (i : ℕ) : Q →* Limit f where
  toFun x := ⟦⟨i,x⟩⟧
  map_one' := (DirectLimit.one_def i).symm
  map_mul' _ _ := (DirectLimit.mul_def _ _ _).symm

theorem of_transition (i j : ℕ) (h : i ≤ j) (x : Q) :
    of f j (transition f i j h x) = of f i x := DirectLimit.mk_apply ..

@[simp] theorem of_succ (i : ℕ) (x : Q) : of f (i+1) (f x) = of f i x := by
  have he : transition f i (i+1) (Nat.le_succ i) = f := by
    change (f ^ (i+1-i) : Monoid.End Q) = f
    rw [show i+1-i = 1 by omega, pow_one]
  have hh := of_transition f i (i+1) (Nat.le_succ i) x
  rw [he] at hh
  exact hh

noncomputable def lift {H : Type*} [Group H] (g : ℕ → Q →* H)
    (h : ∀ i j hij x, g i x = g j (transition f i j hij x)) : Limit f →* H where
  toFun := DirectLimit.lift (transition f) (g ·) h
  map_one' := DirectLimit.lift_one g h
  map_mul' := DirectLimit.lift_mul g h

@[simp] theorem lift_of {H : Type*} [Group H] (g : ℕ → Q →* H) (h) (i) (x) :
    lift f g h (of f i x) = g i x := rfl

theorem hom_ext {H : Type*} [Group H] {a b : Limit f →* H}
    (h : ∀ i x, a (of f i x) = b (of f i x)) : a = b := by
  ext z
  exact DirectLimit.induction (transition f) h z

noncomputable def shiftHom : Limit f →* Limit f :=
  lift f (fun i => of f (i+1)) (by
    intro i j hij x
    simpa [transition] using
      (of_transition f (i+1) (j+1) (Nat.add_le_add_right hij 1) x).symm)

noncomputable def forwardHom : Limit f →* Limit f :=
  lift f (fun i => (of f i).comp f) (by
    intro i j hij x
    change of f i (f x) = of f j (f ((f ^ (j-i)) x))
    have hc : f ((f ^ (j-i)) x) = (f ^ (j-i)) (f x) := by
      exact DFunLike.congr_fun (Commute.self_pow f (j-i)).eq x
    rw [hc]
    exact (of_transition f i j hij (f x)).symm)

@[simp] theorem shift_of (i) (x) : shiftHom f (of f i x) = of f (i+1) x := rfl
@[simp] theorem forward_of (i) (x) : forwardHom f (of f i x) = of f i (f x) := rfl

noncomputable def shift : MulAut (Limit f) where
  toFun := shiftHom f
  invFun := forwardHom f
  left_inv := by
    intro z
    induction z using DirectLimit.induction with | ih i x =>
      exact of_succ f i x
  right_inv := by
    intro z
    induction z using DirectLimit.induction with | ih i x =>
      exact of_succ f i x
  map_mul' := map_mul (shiftHom f)

@[simp] theorem shift_apply_of (i) (x) : shift f (of f i x) = of f (i+1) x := rfl
@[simp] theorem shift_symm_of (i) (x) : (shift f).symm (of f i x) = of f i (f x) := rfl

theorem compatible_of_succ {H : Type*} [Group H] (g : ℕ → Q →* H)
    (h : ∀ i x, g (i+1) (f x) = g i x) :
    ∀ i j hij x, g i x = g j (transition f i j hij x) := by
  intro i j hij x
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  simp only [transition, Nat.add_sub_cancel_left]
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ']
    change g i x = g (i + (k+1)) (f ((f ^ k) x))
    rw [show i+(k+1) = (i+k)+1 by omega, h]
    exact ih x (Nat.le_add_right _ _)

noncomputable def action : Multiplicative ℤ →* MulAut (Limit f) :=
  zpowersHom _ (shift f)

abbrev Torus := (Limit f) ⋊[action f] Multiplicative ℤ

noncomputable def base : Q →* Torus f := SemidirectProduct.inl.comp (of f 0)
noncomputable def stable : Torus f := SemidirectProduct.inr (Multiplicative.ofAdd 1)

@[simp] theorem action_one : action f (Multiplicative.ofAdd 1) = shift f := by
  simp [action, zpowersHom]

@[simp] theorem action_neg_one : action f (Multiplicative.ofAdd (-1)) = (shift f).symm := by
  change (shift f) ^ (-1 : ℤ) = (shift f).symm
  rw [zpow_neg_one]
  rfl

theorem relation (x : Q) : (stable f)⁻¹ * base f x * stable f = base f (f x) := by
  change (SemidirectProduct.inr (Multiplicative.ofAdd 1))⁻¹ *
    SemidirectProduct.inl (of f 0 x) * SemidirectProduct.inr (Multiplicative.ofAdd 1) = _
  rw [← map_inv, ← SemidirectProduct.inl_aut_inv]
  change SemidirectProduct.inl ((shift f).symm (of f 0 x)) = _
  rfl

section Universal
variable {H : Type*} [Group H] (h : Q →* H) (t : H)
    (ht : ∀ x, t⁻¹ * h x * t = h (f x))

noncomputable def stageMap (i : ℕ) : Q →* H :=
  (MulAut.conj (t ^ i)).toMonoidHom.comp h

@[simp] theorem stageMap_apply (i) (x) : stageMap h t i x = t^i * h x * (t^i)⁻¹ := rfl

include ht in
theorem stageMap_succ (i : ℕ) (x : Q) : stageMap h t (i+1) (f x) = stageMap h t i x := by
  simp only [stageMap_apply, ← ht, pow_succ, mul_inv_rev]
  group

noncomputable def limitMap : Limit f →* H :=
  lift f (stageMap h t) (compatible_of_succ f (stageMap h t) (stageMap_succ f h t ht))

@[simp] theorem limitMap_of (i) (x) : limitMap f h t ht (of f i x) = t^i * h x * (t^i)⁻¹ := rfl

theorem limitMap_shift (x : Limit f) :
    limitMap f h t ht (shift f x) = t * limitMap f h t ht x * t⁻¹ := by
  induction x using DirectLimit.induction (transition f) with | ih i x =>
    change limitMap f h t ht (shift f (of f i x)) =
      t * limitMap f h t ht (of f i x) * t⁻¹
    simp only [shift_apply_of, limitMap_of, pow_succ', mul_inv_rev]
    group

theorem limitMap_shift_inv (x : Limit f) :
    limitMap f h t ht ((shift f)⁻¹ x) = t⁻¹ * limitMap f h t ht x * t := by
  have hh := limitMap_shift f h t ht ((shift f)⁻¹ x)
  simp only [MulAut.apply_inv_self] at hh
  rw [hh]
  group

theorem limitMap_shift_zpow (n : ℤ) (x : Limit f) :
    limitMap f h t ht (((shift f)^n) x) = t^n * limitMap f h t ht x * (t^n)⁻¹ := by
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    rw [zpow_add, zpow_add, zpow_one, zpow_one, mul_inv_rev]
    change limitMap f h t ht (((shift f)^(n:ℤ)) (shift f x)) = _
    rw [ih, limitMap_shift]
    group
  | pred n ih =>
    rw [sub_eq_add_neg, zpow_add, zpow_add, zpow_neg_one, zpow_neg_one, mul_inv_rev]
    change limitMap f h t ht (((shift f)^(-(n:ℤ))) ((shift f)⁻¹ x)) = _
    rw [ih, limitMap_shift_inv]
    group

noncomputable def torusLift : Torus f →* H :=
  SemidirectProduct.lift (limitMap f h t ht) (zpowersHom H t) (by
    intro n
    ext x
    exact limitMap_shift_zpow f h t ht n.toAdd x)

@[simp] theorem torusLift_base (x : Q) : torusLift f h t ht (base f x) = h x := by
  simp [base, torusLift]

@[simp] theorem torusLift_stable : torusLift f h t ht (stable f) = t := by
  simp [stable, torusLift, zpowersHom]

end Universal

theorem inl_of (i : ℕ) (x : Q) :
    (SemidirectProduct.inl (of f i x) : Torus f) =
      stable f ^ i * base f x * (stable f ^ i)⁻¹ := by
  induction i with
  | zero => simp [base]
  | succ i ih =>
    have hh := SemidirectProduct.inl_aut (φ := action f) (Multiplicative.ofAdd 1) (of f i x)
    rw [action_one, shift_apply_of, map_inv] at hh
    rw [hh, ih]
    change stable f * (stable f ^ i * base f x * (stable f ^ i)⁻¹) * (stable f)⁻¹ = _
    rw [pow_succ', mul_inv_rev]
    simp only [mul_assoc]

theorem torus_hom_ext {H : Type*} [Group H] {a b : Torus f →* H}
    (hq : a.comp (base f) = b.comp (base f)) (ht : a (stable f) = b (stable f)) : a = b := by
  apply SemidirectProduct.hom_ext
  · apply hom_ext f
    intro i x
    simp only [MonoidHom.comp_apply, inl_of, map_mul, map_inv, map_pow, ht]
    have hx : a (base f x) = b (base f x) := DFunLike.congr_fun hq x
    rw [hx]
  · apply MonoidHom.ext
    intro n
    have hn : n = (Multiplicative.ofAdd 1) ^ n.toAdd := by
      apply Multiplicative.toAdd.injective
      simp
    rw [hn]
    simp only [MonoidHom.comp_apply, map_zpow]
    exact congrArg (fun z => z ^ n.toAdd) ht

end FiniteAlgebraicEnvelopes.SequentialLimit

namespace FiniteAlgebraicEnvelopes.MappingTorus
variable {Q : Type*} [Group Q] (f : Monoid.End Q)

abbrev Free := Monoid.Coprod Q (Multiplicative ℤ)
def letter : Free (Q := Q) := Monoid.Coprod.inr (Multiplicative.ofAdd 1)
def relator (x : Q) : Free (Q := Q) :=
  (letter (Q := Q))⁻¹ * Monoid.Coprod.inl x * letter * (Monoid.Coprod.inl (f x))⁻¹

def relations : Subgroup (Free (Q := Q)) := Subgroup.normalClosure (Set.range (relator f))
instance : (relations f).Normal := inferInstanceAs (Subgroup.normalClosure _).Normal
abbrev Presentation := Free (Q := Q) ⧸ relations f
noncomputable def base : Q →* Presentation f := (QuotientGroup.mk' (relations f)).comp Monoid.Coprod.inl
noncomputable def stable : Presentation f := QuotientGroup.mk' (relations f) letter

theorem relation (x : Q) : (stable f)⁻¹ * base f x * stable f = base f (f x) := by
  have h : QuotientGroup.mk' (relations f) (relator f x) = 1 := by
    change relator f x ∈ (QuotientGroup.mk' (relations f)).ker
    rw [QuotientGroup.ker_mk']
    exact Subgroup.subset_normalClosure (Set.mem_range_self x)
  apply mul_inv_eq_one.mp
  exact h

section Universal
variable {H : Type*} [Group H] (h : Q →* H) (t : H)
    (ht : ∀ x, t⁻¹ * h x * t = h (f x))

noncomputable def lift : Presentation f →* H :=
  QuotientGroup.lift (relations f) (Monoid.Coprod.lift h (zpowersHom H t)) (by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨x, rfl⟩
    change Monoid.Coprod.lift h (zpowersHom H t) (relator f x) = 1
    simpa [relator, letter, zpowersHom] using mul_inv_eq_one.mpr (ht x))

@[simp] theorem lift_base (x : Q) : lift f h t ht (base f x) = h x := by
  change (Monoid.Coprod.lift h (zpowersHom H t)) (Monoid.Coprod.inl x) = h x
  simp
@[simp] theorem lift_stable : lift f h t ht (stable f) = t := by
  simp [lift, stable, letter, zpowersHom]
end Universal

theorem hom_ext {H : Type*} [Group H] {a b : Presentation f →* H}
    (hq : a.comp (base f) = b.comp (base f)) (ht : a (stable f) = b (stable f)) : a = b := by
  apply MonoidHom.cancel_right (QuotientGroup.mk'_surjective (relations f)) |>.mp
  apply Monoid.Coprod.hom_ext
  · exact hq
  · apply MonoidHom.ext
    intro n
    have hn : n = (Multiplicative.ofAdd 1) ^ n.toAdd := by
      apply Multiplicative.toAdd.injective
      simp
    rw [hn]
    simp only [MonoidHom.comp_apply, map_zpow]
    exact congrArg (fun z => z ^ n.toAdd) ht

noncomputable def equivalence : Presentation f ≃* SequentialLimit.Torus f := by
  let a := lift f (SequentialLimit.base f) (SequentialLimit.stable f) (SequentialLimit.relation f)
  let b := SequentialLimit.torusLift f (base f) (stable f) (relation f)
  have ha : b.comp a = MonoidHom.id _ := by
    apply hom_ext f
    · ext x : 1
      simp [a,b]
    · simp [a,b]
  have hb : a.comp b = MonoidHom.id _ := by
    apply SequentialLimit.torus_hom_ext f
    · ext x : 1
      simp [a,b]
    · simp [a,b]
  exact { a with
    invFun := b
    left_inv := DFunLike.congr_fun ha
    right_inv := DFunLike.congr_fun hb }

theorem finite_relations [Group.FG Q] : (relations f).IsFinitelyNormallyGenerated := by
  obtain ⟨s, hs⟩ := Group.FG.out (G := Q)
  let N := Subgroup.normalClosure (relator f '' (s : Set Q))
  refine ⟨relator f '' (s : Set Q), s.finite_toSet.image _, ?_⟩
  apply le_antisymm
  · apply Subgroup.normalClosure_mono
    exact Set.image_subset_range _ _
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨x, rfl⟩
    have hh : (MulAut.conj ((QuotientGroup.mk' N) letter)⁻¹).toMonoidHom.comp
        ((QuotientGroup.mk' N).comp Monoid.Coprod.inl) =
        ((QuotientGroup.mk' N).comp Monoid.Coprod.inl).comp f := by
      apply MonoidHom.eq_of_eqOn_dense hs
      intro y hy
      have hy' : (QuotientGroup.mk' N) (relator f y) = 1 := by
        apply (QuotientGroup.eq_one_iff _).mpr
        exact Subgroup.subset_normalClosure (Set.mem_image_of_mem _ hy)
      change ((QuotientGroup.mk' N) letter)⁻¹ *
        (QuotientGroup.mk' N) (Monoid.Coprod.inl y) * (QuotientGroup.mk' N) letter =
        (QuotientGroup.mk' N) (Monoid.Coprod.inl (f y))
      apply mul_inv_eq_one.mp
      simpa only [relator, map_mul, map_inv] using hy'
    apply (QuotientGroup.eq_one_iff _).mp
    have hx := DFunLike.congr_fun hh x
    change ((QuotientGroup.mk' N) letter)⁻¹ *
      (QuotientGroup.mk' N) (Monoid.Coprod.inl x) * (QuotientGroup.mk' N) letter =
      (QuotientGroup.mk' N) (Monoid.Coprod.inl (f x)) at hx
    change (QuotientGroup.mk' N) (relator f x) = 1
    simpa only [relator, map_mul, map_inv] using mul_inv_eq_one.mpr hx

theorem finitelyPresented [Group.IsFinitelyPresented Q] : Group.IsFinitelyPresented (Presentation f) := by
  have : Group.FG Q := by
    obtain ⟨n, q, hq, _⟩ := Group.IsFinitelyPresented.out (G := Q)
    exact Group.fg_of_surjective hq
  exact Group.IsFinitelyPresented.quotient (relations f) (finite_relations f)

theorem torus_finitelyPresented [Group.IsFinitelyPresented Q] :
    Group.IsFinitelyPresented (SequentialLimit.Torus f) := by
  let := finitelyPresented f
  exact Group.IsFinitelyPresented.equiv (equivalence f)

end FiniteAlgebraicEnvelopes.MappingTorus

namespace FiniteAlgebraicEnvelopes.SequentialLimit
variable {Q E : Type*} [Group Q] [Group E] (f : Monoid.End Q) (g : Monoid.End E)
    (q : Q →* E) (hq : ∀ x, q (f x) = g (q x))

include hq in
theorem transition_natural (i j : ℕ) (hij : i ≤ j) (x : Q) :
    q (transition f i j hij x) = transition g i j hij (q x) := by
  change q ((f ^ (j-i)) x) = (g ^ (j-i)) (q x)
  generalize j-i = n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ']
    change q ((f * f^n) x) = (g * g^n) (q x)
    change q (f ((f^n) x)) = g ((g^n) (q x))
    rw [hq, ih]

noncomputable def map : Limit f →* Limit g :=
  lift f (fun i => (of g i).comp q) (by
    intro i j hij x
    change of g i (q x) = of g j (q (transition f i j hij x))
    rw [transition_natural f g q hq]
    exact (of_transition g i j hij (q x)).symm)

@[simp] theorem map_of (i) (x) : map f g q hq (of f i x) = of g i (q x) := rfl

theorem map_shift (x : Limit f) : map f g q hq (shift f x) = shift g (map f g q hq x) := by
  induction x using DirectLimit.induction (transition f) with | ih i x => rfl

theorem map_surjective (hs : Function.Surjective q) : Function.Surjective (map f g q hq) := by
  intro z
  induction z using DirectLimit.induction (transition g) with | ih i x =>
    obtain ⟨y, rfl⟩ := hs x
    exact ⟨of f i y, rfl⟩

/-- Killing the coefficient kernel in one step makes the induced map injective.
No injectivity assumption on either transition is needed. -/
theorem map_injective (hk : ∀ x, q x = 1 → f x = 1) : Function.Injective (map f g q hq) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro z hz
  change z = 1
  induction z using DirectLimit.induction (transition f) with | ih i x =>
    change of g i (q x) = 1 at hz
    obtain ⟨j, hij, he⟩ := (DirectLimit.exists_eq_one (G := fun _ : ℕ => E) (f := transition g) ⟨i, q x⟩).mp hz
    have he' : q (transition f i j hij x) = 1 := by
      rw [transition_natural f g q hq, he]
    have hf' := hk _ he'
    change of f i x = 1
    rw [← of_transition f i j hij x, ← of_succ f j (transition f i j hij x), hf', map_one]

noncomputable def equivalence (hs : Function.Surjective q)
    (hk : ∀ x, q x = 1 → f x = 1) : Limit f ≃* Limit g :=
  MulEquiv.ofBijective (map f g q hq) ⟨map_injective f g q hq hk, map_surjective f g q hq hs⟩

end FiniteAlgebraicEnvelopes.SequentialLimit

end OAI
