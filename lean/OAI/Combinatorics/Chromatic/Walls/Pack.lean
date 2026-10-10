import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.Split

namespace OAI

section
namespace ElementaryPositivity.PackConvolution
open ElementaryPositivity.ShuffleConvolution
variable {I : Type*} [Fintype I] {A : I → Type*}
variable [∀ i,DecidableEq (A i)]
variable {R : Type*} [CommSemiring R]

abbrev Pack := ∀ i, Finset (A i)
abbrev Cut (s : Pack (A := A)) := ∀ i, Split (s i)

def left {s : Pack (A := A)} (p : Cut s) : Pack (A := A) := fun i => (p i).val.1
def right {s : Pack (A := A)} (p : Cut s) : Pack (A := A) := fun i => (p i).val.2

def kernel (w : (Σi,A i) → (Σi,A i) → R) (s t : Pack (A := A)) : R :=
  ∏ i, ∏ x ∈ s i, ∏ j, ∏ y ∈ t j, w ⟨i,x⟩ ⟨j,y⟩

lemma kernel_union_left (w : (Σi,A i) → (Σi,A i) → R) (s t u : Pack (A := A))
    (h : ∀ i,Disjoint (s i) (t i)) :
    kernel w (fun i => s i ∪ t i) u = kernel w s u * kernel w t u := by
  simp only [kernel, Finset.prod_union (h _), Finset.prod_mul_distrib]
lemma kernel_union_right (w : (Σi,A i) → (Σi,A i) → R) (s t u : Pack (A := A))
    (h : ∀ i,Disjoint (t i) (u i)) :
    kernel w s (fun i => t i ∪ u i) = kernel w s t * kernel w s u := by
  simp only [kernel, Finset.prod_union (h _), Finset.prod_mul_distrib]

variable [DecidableEq I] [∀ i,Fintype (A i)]

abbrev LeftIndex (s : Pack (A := A)) := Σ p : Cut s, Cut (left p)
abbrev RightIndex (s : Pack (A := A)) := Σ p : Cut s, Cut (right p)

def distribute {J : Type*} {B : J → Type*} {C : ∀ j, B j → Type*} :
    (Σ f : ∀ j,B j, ∀ j,C j (f j)) ≃ (∀ j,Σ b : B j,C j b) where
  toFun z j := ⟨z.1 j,z.2 j⟩
  invFun z := ⟨fun j => (z j).1,fun j => (z j).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def rebracket (s : Pack (A := A)) : LeftIndex s ≃ RightIndex s :=
  distribute.trans ((Equiv.piCongrRight fun i => ShuffleConvolution.rebracket (s i)).trans
    distribute.symm)

def shuffle (w : (Σi,A i) → (Σi,A i) → R)
    (f g : Pack (A := A) → R) (s : Pack (A := A)) : R :=
  ∑ p : Cut s, f (left p) * g (right p) * kernel w (left p) (right p)

lemma shuffle_assoc (w : (Σi,A i) → (Σi,A i) → R)
    (f g h : Pack (A := A) → R) :
    shuffle w (shuffle w f g) h = shuffle w f (shuffle w g h) := by
  funext s
  have lhs : shuffle w (shuffle w f g) h s =
      ∑ z : LeftIndex s, (f (left z.2) * g (right z.2) * kernel w (left z.2) (right z.2)) *
        h (right z.1) * kernel w (left z.1) (right z.1) := by
    simp only [shuffle, Fintype.sum_sigma, Finset.sum_mul]
  have rhs : shuffle w f (shuffle w g h) s =
      ∑ z : RightIndex s, f (left z.1) *
        (g (left z.2) * h (right z.2) * kernel w (left z.2) (right z.2)) *
          kernel w (left z.1) (right z.1) := by
    simp only [shuffle, Fintype.sum_sigma, Finset.mul_sum, Finset.sum_mul]
  rw [lhs,rhs,← (rebracket s).sum_comp]
  apply Finset.sum_congr rfl
  intro z hz
  change (f (left z.2) * g (right z.2) * kernel w (left z.2) (right z.2)) *
      h (right z.1) * kernel w (left z.1) (right z.1) =
    f (left z.2) * (g (right z.2) * h (right z.1) * kernel w (right z.2) (right z.1)) *
      kernel w (left z.2) (fun i => right z.2 i ∪ right z.1 i)
  have hu : left z.1 = fun i => left z.2 i ∪ right z.2 i := by
    funext i; exact (z.2 i).property.2.symm
  have hk := congrArg (fun t => kernel w t (right z.1)) hu
  rw [hk, kernel_union_left w (left z.2) (right z.2) (right z.1) (fun i => (z.2 i).property.1),
    kernel_union_right w (left z.2) (right z.2) (right z.1) (fun i =>
      (z.1 i).property.1.mono_left (z.2 i).right_subset)]
  ac_rfl

end ElementaryPositivity.PackConvolution

namespace ElementaryPositivity.PackEnumeration
variable {A : Type*} [DecidableEq A]

abbrev Split (s : Finset A) :=
  {p : Finset A × Finset A // Disjoint p.1 p.2 ∧ p.1 ∪ p.2 = s}

def embedding {n : ℕ} {s : Finset A} (r : Fin n ≃ s) : Fin n ↪ A :=
  r.toEmbedding.trans (Function.Embedding.subtype _)

omit [DecidableEq A] in
lemma map_univ {n : ℕ} {s : Finset A} (r : Fin n ≃ s) :
    Finset.univ.map (embedding r) = s := by
  ext x
  simp only [Finset.mem_map, Finset.mem_univ, true_and, embedding,
    Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨y,rfl⟩; exact (r y).property
  · intro hx
    exact ⟨r.symm ⟨x,hx⟩,congrArg Subtype.val (r.apply_symm_apply ⟨x,hx⟩)⟩

def split {n : ℕ} {s : Finset A} (r : Fin n ≃ s) (t : Finset (Fin n)) : Split s :=
  ⟨(t.map (embedding r),tᶜ.map (embedding r)),
    (Finset.disjoint_map _).mpr (disjoint_compl_right), by
      rw [← Finset.map_union, Finset.union_compl, map_univ]⟩

lemma split_injective {n : ℕ} {s : Finset A} (r : Fin n ≃ s) : Function.Injective (split r) := by
  intro a b hab
  apply Finset.map_injective (embedding r)
  exact congrArg (fun p => p.val.1) hab

lemma split_right_unique {s : Finset A} (p q : Split s) (h : p.val.1 = q.val.1) : p = q := by
  apply Subtype.ext
  apply Prod.ext h
  have hp := p.property
  have hq := q.property
  apply Finset.ext
  intro x
  have hh : x ∈ p.val.2 ↔ x ∈ s ∧ x ∉ p.val.1 := by
    have hu : x ∈ s ↔ x ∈ p.val.1 ∨ x ∈ p.val.2 := by
      simpa only [Finset.mem_union] using (congrArg (fun t => x ∈ t) hp.2.symm).to_iff
    have hd : ¬(x ∈ p.val.1 ∧ x ∈ p.val.2) := by
      intro hmem
      exact Finset.disjoint_left.mp hp.1 hmem.1 hmem.2
    tauto
  have hh' : x ∈ q.val.2 ↔ x ∈ s ∧ x ∉ q.val.1 := by
    have hu : x ∈ s ↔ x ∈ q.val.1 ∨ x ∈ q.val.2 := by
      simpa only [Finset.mem_union] using (congrArg (fun t => x ∈ t) hq.2.symm).to_iff
    have hd : ¬(x ∈ q.val.1 ∧ x ∈ q.val.2) := by
      intro hmem
      exact Finset.disjoint_left.mp hq.1 hmem.1 hmem.2
    tauto
  rw [hh,hh',h]

lemma split_surjective {n : ℕ} {s : Finset A} (r : Fin n ≃ s) : Function.Surjective (split r) := by
  intro p
  let t := Finset.univ.filter fun j => ↑(r j) ∈ p.val.1
  refine ⟨t,split_right_unique _ _ ?_⟩
  change t.map (embedding r) = p.val.1
  ext x
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact (Finset.mem_filter.mp hj).2
  · intro hx
    have hs : x ∈ s := p.property.2 ▸ Finset.mem_union_left p.val.2 hx
    refine ⟨r.symm ⟨x,hs⟩,?_,?_⟩
    · simp [t,hx]
    · exact congrArg Subtype.val (r.apply_symm_apply ⟨x,hs⟩)

noncomputable def splitEquiv {n : ℕ} {s : Finset A} (r : Fin n ≃ s) : Finset (Fin n) ≃ Split s :=
  Equiv.ofBijective (split r) ⟨split_injective r,split_surjective r⟩

@[simp] lemma splitEquiv_left {n : ℕ} {s : Finset A} (r : Fin n ≃ s) (t : Finset (Fin n)) :
    (splitEquiv r t).val.1 = t.map (embedding r) := rfl
@[simp] lemma splitEquiv_right {n : ℕ} {s : Finset A} (r : Fin n ≃ s) (t : Finset (Fin n)) :
    (splitEquiv r t).val.2 = tᶜ.map (embedding r) := rfl

noncomputable def sizedSplitEquiv {n : ℕ} {s : Finset A} (r : Fin n ≃ s) (k : ℕ) :
    {t : Finset (Fin n) // t.card = k} ≃ {p : Split s // p.val.1.card = k} :=
  (splitEquiv r).subtypeEquiv (by intro t; simp)

noncomputable def mapEquiv {B : Type*} (f : B ↪ A) (t : Finset B) : ↥t ≃ ↥(t.map f) :=
  Equiv.ofBijective (fun x => ⟨f x.val,Finset.mem_map.mpr ⟨x.val,x.property,rfl⟩⟩)
    ⟨by
      intro x y h
      apply Subtype.ext
      exact f.injective (congrArg Subtype.val h), by
      intro y
      obtain ⟨x,hx,hxy⟩ := Finset.mem_map.mp y.property
      exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩⟩

omit [DecidableEq A] in
@[simp] lemma mapEquiv_apply {B : Type*} (f : B ↪ A) (t : Finset B) (x : t) :
    ↑(mapEquiv f t x) = f x.val := rfl

end ElementaryPositivity.PackEnumeration

end

end OAI
