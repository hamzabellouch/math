import Mathlib
import OAI.Analysis.FreeWords.FreeWordCore

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

omit [StarOrderedRing A]

section

omit [PartialOrder A]

def upow (u : unitary A) (k : ℤ) : A := (u ^ k : unitary A)

@[simp] theorem upow_zero (u : unitary A) : upow u 0 = 1 := by simp [upow]

@[simp] theorem upow_one (u : unitary A) : upow u 1 = u := by simp [upow]

theorem upow_add (u : unitary A) (k l : ℤ) : upow u (k+l) = upow u k * upow u l := by
  simp [upow, zpow_add]

@[simp] theorem upow_neg_mul (u : unitary A) (k : ℤ) : upow u (-k) * upow u k = 1 := by
  rw [← upow_add]; simp

@[simp] theorem upow_mul_neg (u : unitary A) (k : ℤ) : upow u k * upow u (-k) = 1 := by
  rw [← upow_add]; simp

@[simp] theorem star_upow (u : unitary A) (k : ℤ) : star (upow u k) = upow u (-k) := by
  change ((star (u^k) : unitary A) : A) = _
  rw [Unitary.star_eq_inv, ← zpow_neg]
  rfl

theorem upow_mem (u : unitary A) (hu : (u:A) ∈ S) (k : ℤ) : upow u k ∈ S := by
  cases k with
  | ofNat n => simpa [upow] using S.pow_mem hu n
  | negSucc n =>
    have h : upow u (Int.ofNat (n+1)) ∈ S := by
      change ((u ^ ((n+1:ℕ):ℤ) : unitary A) : A) ∈ S
      rw [zpow_natCast, SubmonoidClass.coe_pow]
      exact S.pow_mem hu (n+1)
    have hn : Int.negSucc n = -Int.ofNat (n+1) := by
      change Int.negSucc n = -((n+1:ℕ):ℤ)
      omega
    rw [hn, ← star_upow]
    exact star_mem h

def conjugate (u : unitary A) (k : ℤ) : A ≃⋆ₐ[ℂ] A :=
  Unitary.conjStarAlgAut ℂ A (u^(-k))

@[simp] theorem conjugate_apply (u : unitary A) (k : ℤ) (x : A) :
    conjugate u k x = upow u (-k) * x * upow u k := by
  rw [conjugate, Unitary.conjStarAlgAut_apply]
  change upow u (-k) * x * star (upow u (-k)) = _
  rw [star_upow, neg_neg]

@[simp] theorem conjugate_inverse (u : unitary A) (k : ℤ) (x : A) :
    conjugate u (-k) (conjugate u k x) = x := by
  simp only [conjugate_apply, neg_neg]
  calc upow u k * (upow u (-k) * x * upow u k) * upow u (-k)
      = (upow u k * upow u (-k)) * x * (upow u k * upow u (-k)) := by
        simp only [mul_assoc]
    _ = x := by simp

end

theorem trace_conjugate (hτ : ∀ x y, τ (x*y) = τ (y*x))
    (u : unitary A) (k : ℤ) (x : A) : τ (conjugate u k x) = τ x := by
  rw [conjugate_apply, hτ]
  simp only [← mul_assoc, upow_mul_neg, one_mul]

section

omit [PartialOrder A]

def powerWord (u : unitary A) (k : ℤ) : List (Bool × A) :=
  if k=0 then [] else [(false, upow u k)]

def separatedWord (u : unitary A) : List (ℤ × A) → List (Bool × A)
  | [] => []
  | [(k,x)] => (true,x) :: powerWord u k
  | (k,x)::(l,y)::w => (true,x) :: powerWord u (k-l) ++ separatedWord u ((l,y)::w)

def expandedWord (u : unitary A) : List (ℤ × A) → List (Bool × A)
  | [] => []
  | (k,x)::w => powerWord u (-k) ++ separatedWord u ((k,x)::w)

@[simp] theorem powerWord_value (u : unitary A) (k : ℤ) :
    ((powerWord u k).map Prod.snd).prod = upow u k := by
  by_cases h : k=0 <;> simp [powerWord, h]

@[simp] theorem separatedWord_head (u : unitary A) (k : ℤ) (x : A) (w : List (ℤ×A)) :
    (separatedWord u ((k,x)::w)).head? = some (true,x) := by
  cases w <;> simp [separatedWord]

@[simp] theorem separatedWord_ne_nil (u : unitary A) (k : ℤ) (x : A) (w : List (ℤ×A)) :
    separatedWord u ((k,x)::w) ≠ [] := by
  cases w <;> simp [separatedWord]

theorem separatedWord_value (u : unitary A) (k : ℤ) (x : A) (w : List (ℤ×A)) :
    ((separatedWord u ((k,x)::w)).map Prod.snd).prod =
      upow u k * (((k,x)::w).map (fun y => conjugate u y.1 y.2)).prod := by
  induction w generalizing k x with
  | nil => simp [separatedWord, conjugate_apply, ← mul_assoc]
  | cons y w ih =>
    obtain ⟨l,y⟩ := y
    simp only [separatedWord, List.map_append, List.map_cons, List.prod_append,
      List.prod_cons, powerWord_value, ih]
    have hpow : upow u (k-l) * upow u l = upow u k := by rw [← upow_add]; congr 1; omega
    have lead (z : A) : upow u k * (conjugate u k x * z) = x * (upow u k * z) := by
      simp only [conjugate_apply, ← mul_assoc, upow_mul_neg, one_mul]
    rw [lead, mul_assoc, ← mul_assoc (upow u (k-l)), hpow]

theorem expandedWord_value (u : unitary A) (w : List (ℤ×A)) :
    ((expandedWord u w).map Prod.snd).prod =
      (w.map (fun y => conjugate u y.1 y.2)).prod := by
  cases w with
  | nil => simp [expandedWord]
  | cons y w =>
    obtain ⟨k,x⟩ := y
    rw [expandedWord, List.map_append, List.prod_append, powerWord_value,
      separatedWord_value, ← mul_assoc, upow_neg_mul, one_mul]

def binaryCopy (S P : StarSubalgebra ℂ A) (b : Bool) : StarSubalgebra ℂ A :=
  if b then P else S

theorem separatedWord_chain (u : unitary A) {k : ℤ} {x : A} {w : List (ℤ×A)}
    (h : ((k,x)::w).IsChain (fun x y => x.1 ≠ y.1)) :
    (separatedWord u ((k,x)::w)).IsChain (fun x y => x.1 ≠ y.1) := by
  induction w generalizing k x with
  | nil =>
    by_cases hk : k=0 <;> simp [separatedWord, powerWord, hk]
  | cons y w ih =>
    obtain ⟨l,y⟩ := y
    have hkl : k ≠ l := (List.isChain_cons_cons.mp h).1
    have hh := ih h.tail
    rw [separatedWord, powerWord, ite_eq_right (sub_ne_zero.mpr hkl)]
    simpa [List.isChain_cons, separatedWord_head] using hh

theorem expandedWord_chain (u : unitary A) {w : List (ℤ×A)}
    (h : w.IsChain (fun x y => x.1 ≠ y.1)) :
    (expandedWord u w).IsChain (fun x y => x.1 ≠ y.1) := by
  cases w with
  | nil => simp [expandedWord]
  | cons y w =>
    obtain ⟨k,x⟩ := y
    have hh := separatedWord_chain u h
    by_cases hk : -k=0 <;> simpa [expandedWord, powerWord, hk, List.isChain_cons] using hh

end

theorem powerWord_centered (u : unitary A) (hu : (u:A) ∈ S)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow u k) = 0) (k : ℤ) :
    ∀ x ∈ powerWord u k, x.2 ∈ binaryCopy S P x.1 ∧ τ x.2 = 0 := by
  intro x hx
  by_cases hk : k=0
  · simp [powerWord, hk] at hx
  · have he : x = (false, upow u k) := by
      simpa only [powerWord, ite_eq_right hk, List.mem_singleton] using hx
    subst x
    exact ⟨upow_mem u hu k, hHaar k hk⟩

theorem separatedWord_centered (u : unitary A) (hu : (u:A) ∈ S)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow u k) = 0) {w : List (ℤ×A)}
    (hw : ∀ x ∈ w, x.2 ∈ P ∧ τ x.2 = 0) :
    ∀ x ∈ separatedWord u w, x.2 ∈ binaryCopy S P x.1 ∧ τ x.2 = 0 := by
  induction w with
  | nil => simp [separatedWord]
  | cons y w ih =>
    obtain ⟨k,y⟩ := y
    have hy := hw (k,y) (by simp)
    have ht := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))
    intro x hx
    cases w with
    | nil =>
      simp only [separatedWord, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hy
      · exact powerWord_centered u hu hHaar k x hx
    | cons z w =>
      obtain ⟨l,z⟩ := z
      simp only [separatedWord, List.mem_append, List.mem_cons] at hx
      rcases hx with (rfl | hx) | hx
      · exact hy
      · exact powerWord_centered u hu hHaar (k-l) x hx
      · exact ht x hx

theorem expandedWord_centered (u : unitary A) (hu : (u:A) ∈ S)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow u k) = 0) {w : List (ℤ×A)}
    (hw : ∀ x ∈ w, x.2 ∈ P ∧ τ x.2 = 0) :
    ∀ x ∈ expandedWord u w, x.2 ∈ binaryCopy S P x.1 ∧ τ x.2 = 0 := by
  cases w with
  | nil => simp [expandedWord]
  | cons y w =>
    obtain ⟨k,y⟩ := y
    intro x hx
    rw [expandedWord, List.mem_append] at hx
    exact hx.elim (powerWord_centered u hu hHaar (-k) x)
      (separatedWord_centered u hu hHaar hw x)

theorem trace_conjugate_word (u : unitary A) (hu : (u:A) ∈ S)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow u k) = 0)
    (hfree : ScalarFree τ (binaryCopy S P)) {w : List (ℤ×A)}
    (hne : w ≠ []) (hchain : w.IsChain (fun x y => x.1 ≠ y.1))
    (hw : ∀ x ∈ w, x.2 ∈ P ∧ τ x.2 = 0) :
    τ ((w.map (fun x => conjugate u x.1 x.2)).prod) = 0 := by
  have hne' : expandedWord u w ≠ [] := by
    cases w with
    | nil => contradiction
    | cons y w =>
      obtain ⟨k,x⟩ := y
      intro he
      exact separatedWord_ne_nil u k x w (List.append_eq_nil_iff.mp he).2
  simpa only [expandedWord_value] using hfree (expandedWord u w) hne'
    (expandedWord_chain u hchain) (expandedWord_centered u hu hHaar hw)

def conjugateCopy (u : unitary A) (P : StarSubalgebra ℂ A) (k : ℤ) :
    StarSubalgebra ℂ A := P.map (conjugate u k).toStarAlgHom

theorem conjugates_scalarFree (hτ : ∀ x y, τ (x*y) = τ (y*x))
    (u : unitary A) (hu : (u:A) ∈ S)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow u k) = 0)
    (hfree : ScalarFree τ (binaryCopy S P)) :
    ScalarFree τ (conjugateCopy u P) := by
  intro w hne hchain hw
  let w₀ := w.map (fun x : ℤ × A => (x.1, conjugate u (-x.1) x.2))
  have he := trace_conjugate_word u hu hHaar hfree (w := w₀)
  have hne₀ : w₀ ≠ [] := by simpa [w₀] using hne
  have hchain₀ : w₀.IsChain (fun x y => x.1 ≠ y.1) := by
    simpa only [w₀, List.isChain_map] using hchain
  have hw₀ : ∀ x ∈ w₀, x.2 ∈ P ∧ τ x.2 = 0 := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    obtain ⟨hyP, hyτ⟩ := hw y hy
    constructor
    · obtain ⟨z,hz,hze⟩ := StarSubalgebra.mem_map.mp hyP
      change conjugate u y.1 z = y.2 at hze
      rw [← hze, conjugate_inverse]
      exact hz
    · simpa only [trace_conjugate hτ] using hyτ
  have hzero := he hne₀ hchain₀ hw₀
  have hinv (k : ℤ) (x : A) : conjugate u k (conjugate u (-k) x) = x := by
    simpa only [neg_neg] using conjugate_inverse u (-k) x
  simpa only [w₀, List.map_map, Function.comp_def, hinv] using hzero

theorem ScalarFree.mono {ι : Type*} {T U : ι → StarSubalgebra ℂ A}
    (h : ScalarFree τ T) (hTU : ∀ i, U i ≤ T i) : ScalarFree τ U := by
  intro w hne hchain hw
  exact h w hne hchain (fun x hx => ⟨hTU x.1 (hw x hx).1, (hw x hx).2⟩)

theorem ScalarFree.reindex {ι κ : Type*} {T : ι → StarSubalgebra ℂ A}
    (h : ScalarFree τ T) {f : κ → ι} (hf : Function.Injective f) :
    ScalarFree τ (T ∘ f) := by
  intro w hne hchain hw
  have hne' : w.map (fun x => (f x.1, x.2)) ≠ [] := by simpa using hne
  have hc : (w.map (fun x => (f x.1, x.2))).IsChain (fun x y => x.1 ≠ y.1) := by
    rw [List.isChain_map]
    exact hchain.imp (fun x y hxy heq => hxy (hf heq))
  have hz := h (w.map (fun x => (f x.1, x.2))) hne' hc (by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    exact hw y hy)
  simpa only [List.map_map, Function.comp_def] using hz

end

end KKFreeWords
end

end OAI
