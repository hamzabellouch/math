import OAI.GroupTheory.Kervaire.Inversion

namespace OAI

section
noncomputable section

namespace KervaireRibbon
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {I : Type} {A : Type*} [Group A]

def OuterRibbon.one (ρ : Perm I) (a : I → A) (s : I → ℤ) :
    OuterRibbon (V := (PEmpty : Type)) ρ a s (PUnit.unit : (PUnit : Type)) [] := by
  let b : DiskAtlas (V := (PEmpty : Type)) ρ a s (1 : Perm (PUnit : Type)) (fun _ ↦ 0) := {
    disk := ⟨fun vi ↦ vi.1.elim,by rintro ⟨v,i⟩; exact v.elim⟩
    ε := fun v ↦ v.elim
    polarity := fun v ↦ v.elim
    next := fun v ↦ v.elim
    sign := fun v ↦ v.elim }
  exact {
    σ := 1, θ := 1, t := fun _ ↦ 0, u := fun _ ↦ 1, atlas := b
    involutive := fun _ ↦ rfl, planar' := planar_one_right 1
    opposite := fun _ ↦ (neg_zero : -(0:ℤ)=0).symm
    marker := rfl, marker_sign := rfl
    circle := by simp [Circle]
    nodup := by simp
    unit := by simp
    disjoint := fun vi ↦ vi.1.elim
    cover := fun d ↦ Or.inr (Or.inr ⟨rfl,rfl⟩)
    corners := fun v ↦ v.elim }

lemma OuterRibbon.value_one (ρ : Perm I) (a : I → A) (s : I → ℤ) :
    (OuterRibbon.one ρ a s).value = 1 := by
  simp [OuterRibbon.value,OuterRibbon.one,dartEval,dartLetter,corner]

/-- A word is realized by a finite genus-zero relator ribbon. The dart and vertex
sets range over ordinary finite types; the coefficient group has arbitrary universe. -/
def Realized (ρ : Perm I) (a : I → A) (s : I → ℤ) (w : FreeProd A) : Prop :=
  ∃ (D V : Type) (_ : Fintype D) (_ : DecidableEq D) (_ : Fintype V)
    (o : D) (l : List D) (r : OuterRibbon (V := V) ρ a s o l), r.value = w

lemma Realized.one (ρ : Perm I) (a : I → A) (s : I → ℤ) : Realized ρ a s 1 :=
  ⟨PUnit,PEmpty,inferInstance,inferInstance,inferInstance,PUnit.unit,[],OuterRibbon.one ρ a s,
    OuterRibbon.value_one ρ a s⟩

lemma Realized.mul {ρ : Perm I} {a : I → A} {s : I → ℤ} {w z : FreeProd A}
    (h : Realized ρ a s w) (k : Realized ρ a s z) : Realized ρ a s (w*z) := by
  obtain ⟨D,V,fd,dd,fv,o,l,r,rfl⟩ := h
  obtain ⟨E,W,fe,de,fw,p,m,q,rfl⟩ := k
  exact ⟨D⊕E,V⊕W,inferInstance,inferInstance,inferInstance,Sum.inl o,
    l.map Sum.inl ++ m.map Sum.inr,r.mul q,r.value_mul q⟩

lemma Realized.inv {ρ : Perm I} {a : I → A} {s : I → ℤ} {w : FreeProd A}
    (h : Realized ρ a s w) : Realized ρ a s w⁻¹ := by
  obtain ⟨D,V,fd,dd,fv,o,l,r,rfl⟩ := h
  exact ⟨D,V,fd,dd,fv,o,l.reverse,r.inv,r.value_inv⟩

lemma Realized.conjCoefficient {ρ : Perm I} {a : I → A} {s : I → ℤ} {w : FreeProd A}
    (h : Realized ρ a s w) (g : A) : Realized ρ a s (Coprod.inl g*w*(Coprod.inl g)⁻¹) := by
  obtain ⟨D,V,fd,dd,fv,o,l,r,rfl⟩ := h
  exact ⟨D,V,fd,dd,fv,o,l,r.conjCoefficient g,r.value_conjCoefficient g⟩

lemma Realized.conjLetter {ρ : Perm I} {a : I → A} {s : I → ℤ} {w : FreeProd A}
    (h : Realized ρ a s w) (n : ℤ) (hn : n=1 ∨ n = -1) :
    Realized ρ a s (Coprod.inr (ofAdd n)*w*(Coprod.inr (ofAdd n))⁻¹) := by
  obtain ⟨D,V,fd,dd,fv,o,l,r,rfl⟩ := h
  exact ⟨D⊕Bool,V,inferInstance,inferInstance,fv,Sum.inl o,
    Sum.inr false :: l.map Sum.inl ++ [Sum.inr true],r.conjLetter n hn,r.value_conjLetter n hn⟩

def realizedSubgroup (ρ : Perm I) (a : I → A) (s : I → ℤ) : Subgroup (FreeProd A) where
  carrier := Realized ρ a s
  one_mem' := Realized.one ρ a s
  mul_mem' := Realized.mul
  inv_mem' := Realized.inv

lemma Realized.conjZpow {ρ : Perm I} {a : I → A} {s : I → ℤ} {w : FreeProd A}
    (h : Realized ρ a s w) (n : ℤ) :
    Realized ρ a s (Coprod.inr (ofAdd n)*w*(Coprod.inr (ofAdd n))⁻¹) := by
  induction n using Int.induction_on with
  | zero => simpa using h
  | succ n ih =>
    have hh := ih.conjLetter 1 (Or.inl rfl)
    convert hh using 1
    rw [add_comm,ofAdd_add,map_mul]
    group
  | pred n ih =>
    have hh := ih.conjLetter (-1) (Or.inr rfl)
    convert hh using 1
    rw [sub_eq_add_neg,add_comm,ofAdd_add,map_mul]
    group

lemma Realized.conj {ρ : Perm I} {a : I → A} {s : I → ℤ} {w : FreeProd A}
    (h : Realized ρ a s w) (x : FreeProd A) : Realized ρ a s (x*w*x⁻¹) := by
  induction x using Coprod.induction_on generalizing w with
  | inl g => exact h.conjCoefficient g
  | inr n => exact h.conjZpow (toAdd n)
  | mul x y hx hy =>
    have hh := hx (hy h)
    convert hh using 1
    group

instance realizedSubgroup_normal (ρ : Perm I) (a : I → A) (s : I → ℤ) :
    (realizedSubgroup ρ a s).Normal where
  conj_mem := fun _ hw x ↦ hw.conj x

lemma Realized.coefficient_eq_one [Fintype I] [Nonempty I] {ρ : Perm I} {a : I → A} {s : I → ℤ}
    (hρ : ∀ i j, ρ.SameCycle i j) (hs : ∀ i, s i=1 ∨ s i = -1)
    (hsum : (∑ i, s i)=1 ∨ (∑ i, s i) = -1) {g : A}
    (h : Realized ρ a s (Coprod.inl g)) : g=1 := by
  obtain ⟨D,V,fd,dd,fv,o,l,r,hr⟩ := h
  exact r.coefficient_eq_one hρ hs hsum g hr
end KervaireRibbon

end
end

end OAI
