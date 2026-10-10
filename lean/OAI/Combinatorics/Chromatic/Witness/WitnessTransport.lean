import Mathlib

namespace OAI

section
namespace ElementaryPositivity
namespace FiniteMatching

variable {A B : Type*} [DecidableEq B]
variable {P : A → Prop} {Q : B → Prop}

def align (e : A ≃ B) (f : {a // P a} ≃ {b // Q b}) (a : {a // P a}) : A ≃ B :=
  e.trans (Equiv.swap (e a.val) (f a).val)

@[simp] theorem align_at (e : A ≃ B) (f : {a // P a} ≃ {b // Q b})
    (a : {a // P a}) : align e f a a.val = (f a).val := by
  simp [align]

theorem align_preserves (e : A ≃ B) (f : {a // P a} ≃ {b // Q b})
    (a b : {a // P a}) (hb : e b.val = (f b).val) :
    align e f a b.val = (f b).val := by
  by_cases hab : a = b
  · subst b
    exact align_at _ _ _
  · have habval : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    have he : (f b).val ≠ e a.val := by
      rw [← hb]
      exact fun h => habval (e.injective h.symm)
    have hf : (f b).val ≠ (f a).val :=
      fun h => hab (f.injective (Subtype.ext h.symm))
    simp [align, hb, Equiv.swap_apply_of_ne_of_ne he hf]

def compress (e : A ≃ B) (f : {a // P a} ≃ {b // Q b}) :
    List {a // P a} → A ≃ B
  | [] => e
  | a :: as => compress (align e f a) f as

 theorem compress_preserves (e : A ≃ B) (f : {a // P a} ≃ {b // Q b})
    (as : List {a // P a}) (b : {a // P a}) (hb : e b.val = (f b).val) :
    compress e f as b.val = (f b).val := by
  induction as generalizing e with
  | nil => exact hb
  | cons a as ih =>
    exact ih _ (align_preserves e f a b hb)

 theorem compress_at (e : A ≃ B) (f : {a // P a} ≃ {b // Q b})
    (as : List {a // P a}) (b : {a // P a}) (hb : b ∈ as) :
    compress e f as b.val = (f b).val := by
  induction as generalizing e with
  | nil => simp at hb
  | cons a as ih =>
    rcases List.mem_cons.mp hb with h | h
    · subst b
      exact compress_preserves (align e f a) f as a (align_at e f a)
    · exact ih (align e f a) h

omit [DecidableEq B] in
 theorem membership_iff (e : A ≃ B) (f : {a // P a} ≃ {b // Q b})
    (he : ∀ a : {a // P a}, e a.val = (f a).val) (a : A) :
    P a ↔ Q (e a) := by
  constructor
  · intro ha
    rw [he ⟨a, ha⟩]
    exact (f ⟨a, ha⟩).property
  · intro hq
    let a' := f.symm ⟨e a, hq⟩
    have haa : a'.val = a := by
      apply e.injective
      rw [he a']
      exact congrArg Subtype.val (f.apply_symm_apply ⟨e a, hq⟩)
    exact haa ▸ a'.property

def cancel (e : A ≃ B) (f : {a // P a} ≃ {b // Q b})
    (as : List {a // P a}) (complete : ∀ a, a ∈ as) :
    {a // ¬P a} ≃ {b // ¬Q b} :=
  (compress e f as).subtypeEquiv fun a =>
    not_congr (membership_iff (compress e f as) f
      (fun b => compress_at e f as b (complete b)) a)

variable {W : Type*}

 theorem swap_preserves (energy : B → W) (x y : B) (h : energy x = energy y)
    (b : B) : energy (Equiv.swap x y b) = energy b := by
  by_cases hx : b = x
  · subst b
    simpa using h.symm
  · by_cases hy : b = y
    · subst b
      simpa using h
    · rw [Equiv.swap_apply_of_ne_of_ne hx hy]

 theorem align_energy (energyA : A → W) (energyB : B → W)
    (e : A ≃ B) (f : {a // P a} ≃ {b // Q b})
    (he : ∀ a, energyB (e a) = energyA a)
    (hf : ∀ a, energyB (f a).val = energyA a.val)
    (a : {a // P a}) (x : A) : energyB (align e f a x) = energyA x := by
  change energyB (Equiv.swap (e a.val) (f a).val (e x)) = _
  rw [swap_preserves energyB _ _ ((he a.val).trans (hf a).symm)]
  exact he x

 theorem compress_energy (energyA : A → W) (energyB : B → W)
    (e : A ≃ B) (f : {a // P a} ≃ {b // Q b})
    (he : ∀ a, energyB (e a) = energyA a)
    (hf : ∀ a, energyB (f a).val = energyA a.val)
    (as : List {a // P a}) (x : A) : energyB (compress e f as x) = energyA x := by
  induction as generalizing e with
  | nil => exact he x
  | cons a as ih => exact ih _ (align_energy energyA energyB e f he hf a)

 theorem cancel_energy (energyA : A → W) (energyB : B → W)
    (e : A ≃ B) (f : {a // P a} ≃ {b // Q b})
    (he : ∀ a, energyB (e a) = energyA a)
    (hf : ∀ a, energyB (f a).val = energyA a.val)
    (as : List {a // P a}) (complete : ∀ a, a ∈ as) (x : {a // ¬P a}) :
    energyB (cancel e f as complete x).val = energyA x.val :=
  compress_energy energyA energyB e f he hf as x.val

end FiniteMatching
end ElementaryPositivity

namespace ElementaryPositivity
namespace ExactMasks

variable {A B I W : Type*} [DecidableEq I]

def Exact (mask : A → Finset I) (J : Finset I) := {a // mask a = J}
def Required (mask : A → Finset I) (J : Finset I) := {a // J ⊆ mask a}
def Strict (mask : A → Finset I) (J : Finset I) := {a // J ⊂ mask a}

def GradedEquiv (energyA : A → W) (energyB : B → W) :=
  {e : A ≃ B // ∀ a, energyB (e a) = energyA a}

def strictFibers (mask : A → Finset I) (J : Finset I) :
    Strict mask J ≃ Σ K : {K : Finset I // J ⊂ K}, Exact mask K.val where
  toFun a := ⟨⟨mask a.val, a.property⟩, ⟨a.val, rfl⟩⟩
  invFun a := ⟨a.2.val, by simpa only [a.2.property] using a.1.property⟩
  left_inv _ := rfl
  right_inv a := by
    rcases a with ⟨⟨K, hk⟩, ⟨a, ha⟩⟩
    dsimp only at ha
    subst K
    rfl

def internalStrict (mask : A → Finset I) (J : Finset I) :
    {a : Required mask J // mask a.val ≠ J} ≃ Strict mask J where
  toFun a := ⟨a.val.val, Finset.ssubset_iff_subset_ne.mpr
    ⟨a.val.property, Ne.symm a.property⟩⟩
  invFun a := ⟨⟨a.val, (Finset.ssubset_iff_subset_ne.mp a.property).1⟩,
    Ne.symm ((Finset.ssubset_iff_subset_ne.mp a.property).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def exactCompl (mask : A → Finset I) (J : Finset I) :
    Exact mask J ≃ {a : Required mask J // ¬mask a.val ≠ J} where
  toFun a := ⟨⟨a.val, by rw [a.property]⟩, not_not.mpr a.property⟩
  invFun a := ⟨a.val.val, not_not.mp a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def strictEquiv (maskA : A → Finset I) (maskB : B → Finset I) (J : Finset I)
    (ih : ∀ K, J ⊂ K → Exact maskA K ≃ Exact maskB K) :
    Strict maskA J ≃ Strict maskB J :=
  (strictFibers maskA J).trans
    ((Equiv.sigmaCongrRight fun K : {K : Finset I // J ⊂ K} => ih K.val K.property).trans
      (strictFibers maskB J).symm)

omit [DecidableEq I] in
 theorem strictEquiv_energy (maskA : A → Finset I) (maskB : B → Finset I)
    (energyA : A → W) (energyB : B → W) (J : Finset I)
    (ih : ∀ K, J ⊂ K → Exact maskA K ≃ Exact maskB K)
    (hh : ∀ K h a, energyB (ih K h a).val = energyA a.val)
    (a : Strict maskA J) :
    energyB (strictEquiv maskA maskB J ih a).val = energyA a.val := by
  exact hh (maskA a.val) a.property ⟨a.val, rfl⟩

variable [Fintype A] [Encodable A] [DecidableEq B]

def step (maskA : A → Finset I) (maskB : B → Finset I)
    (energyA : A → W) (energyB : B → W) (J : Finset I)
    (required : GradedEquiv
      (fun a : Required maskA J => energyA a.val)
      (fun b : Required maskB J => energyB b.val))
    (ih : ∀ K, J ⊂ K → GradedEquiv
      (fun a : Exact maskA K => energyA a.val)
      (fun b : Exact maskB K => energyB b.val)) :
    GradedEquiv (fun a : Exact maskA J => energyA a.val)
      (fun b : Exact maskB J => energyB b.val) := by
  letI : DecidableEq (Required maskB J) :=
    inferInstanceAs (DecidableEq {b : B // J ⊆ maskB b})
  letI : Fintype (Required maskA J) :=
    inferInstanceAs (Fintype {a : A // J ⊆ maskA a})
  letI : Encodable (Required maskA J) :=
    inferInstanceAs (Encodable {a : A // J ⊆ maskA a})
  let ilarge := strictEquiv maskA maskB J (fun K h => (ih K h).val)
  let internal := (internalStrict maskA J).trans
    (ilarge.trans (internalStrict maskB J).symm)
  let enumeration := Encodable.sortedUniv {a : Required maskA J // maskA a.val ≠ J}
  have complete : ∀ a, a ∈ enumeration := fun a => Encodable.mem_sortedUniv a
  let cancelled := FiniteMatching.cancel required.val internal enumeration complete
  refine ⟨(exactCompl maskA J).trans (cancelled.trans (exactCompl maskB J).symm), ?_⟩
  intro a
  apply FiniteMatching.cancel_energy
    (fun a : Required maskA J => energyA a.val)
    (fun b : Required maskB J => energyB b.val)
    required.val internal required.property
  intro x
  exact strictEquiv_energy maskA maskB energyA energyB J
    (fun K h => (ih K h).val) (fun K h => (ih K h).property)
    (internalStrict maskA J x)

def refine [Fintype I] (maskA : A → Finset I) (maskB : B → Finset I)
    (energyA : A → W) (energyB : B → W)
    (required : ∀ J, GradedEquiv
      (fun a : Required maskA J => energyA a.val)
      (fun b : Required maskB J => energyB b.val)) (J : Finset I) :
    GradedEquiv (fun a : Exact maskA J => energyA a.val)
      (fun b : Exact maskB J => energyB b.val) :=
  step maskA maskB energyA energyB J (required J)
    (fun K _ => refine maskA maskB energyA energyB required K)
termination_by Fintype.card I - J.card
decreasing_by
  rename_i strictSubset
  have hjk := Finset.card_lt_card strictSubset
  have hk := Finset.card_le_univ K
  omega

end ExactMasks
end ElementaryPositivity

end

end OAI
