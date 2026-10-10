import Mathlib
import OAI.Analysis.FreeWords.HaarTwistLetters

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

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

def letterBlock (b : Bool) (n : ℕ) (x : A) : List (Bool × A) :=
  List.replicate n (b,(1:A)) ++ [(b,x)]

def powerBlock (k : ℤ) (x : A) : List (Bool × A) :=
  match k with
  | .ofNat 0 => []
  | .ofNat (n+1) => letterBlock true n x
  | .negSucc n => letterBlock false n x

omit [PartialOrder A] [StarOrderedRing A] in
theorem letterBlock_value (u : unitary A) (b : Bool) (n : ℕ) (x : A) :
    letterWord u (letterBlock b n x) = unitaryLetter u b ^ (n+1) * x := by
  simp [letterWord,letterBlock,List.map_replicate,List.prod_replicate,pow_succ,mul_assoc]

omit [PartialOrder A] [StarOrderedRing A] in
theorem powerBlock_value (u : unitary A) (k : ℤ) (hk : k ≠ 0) (x : A) :
    letterWord u (powerBlock k x) = upow u k * x := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => contradiction
    | succ n =>
      rw [powerBlock,letterBlock_value]
      change unitaryLetter u true ^ (n+1) * x = upow u ((n+1:ℕ):ℤ) * x
      simp only [unitaryLetter,ite_true,upow,zpow_natCast,SubmonoidClass.coe_pow]
  | negSucc n =>
    rw [powerBlock,letterBlock_value]
    have he : Int.negSucc n = -((n+1:ℕ):ℤ) := by omega
    rw [he,← star_upow]
    simp only [unitaryLetter,Bool.false_eq_true,ite_false,upow,zpow_natCast,
      SubmonoidClass.coe_pow,star_pow]

omit [PartialOrder A] [StarOrderedRing A] in
theorem letterBlock_mem (b : Bool) (n : ℕ) (x : A) (hx : x ∈ P) :
    ∀ a ∈ letterBlock b n x, a.2 ∈ P := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · have he := List.eq_of_mem_replicate ha
    subst a
    exact P.one_mem
  · have he : a = (b,x) := by simpa using ha
    subst a
    exact hx

omit [PartialOrder A] [StarOrderedRing A] in
theorem powerBlock_mem (k : ℤ) (x : A) (hx : x ∈ P) :
    ∀ a ∈ powerBlock k x, a.2 ∈ P := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => simp [powerBlock]
    | succ n => exact letterBlock_mem true n x hx
  | negSucc n => exact letterBlock_mem false n x hx

omit [PartialOrder A] [StarOrderedRing A] in
theorem powerBlock_ne_nil (k : ℤ) (hk : k ≠ 0) (x : A) : powerBlock k x ≠ [] := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => contradiction
    | succ n => simp [powerBlock,letterBlock]
  | negSucc n => simp [powerBlock,letterBlock]

omit [StarOrderedRing A] in
theorem letterBlock_chain (b : Bool) (n : ℕ) (x : A) :
    (letterBlock b n x).IsChain (LetterRelation τ) := by
  induction n with
  | zero => simp [letterBlock]
  | succ n ih =>
    cases n with
    | zero => simp [letterBlock,LetterRelation]
    | succ n => simpa [letterBlock,List.replicate_succ,List.isChain_cons_cons,LetterRelation] using ih

omit [StarOrderedRing A] in
theorem letterBlock_chain_append (b : Bool) (n : ℕ) (x : A) (hx : τ x = 0)
    {w : List (Bool × A)} (hw : w.IsChain (LetterRelation τ)) :
    (letterBlock b n x ++ w).IsChain (LetterRelation τ) := by
  induction n with
  | zero =>
    cases w with
    | nil => simp [letterBlock]
    | cons a w =>
      exact List.isChain_cons_cons.mpr ⟨fun _ => hx,hw⟩
  | succ n ih =>
    cases n with
    | zero =>
      exact List.isChain_cons_cons.mpr ⟨fun h => (h rfl).elim,ih⟩
    | succ n =>
      exact List.isChain_cons_cons.mpr ⟨fun h => (h rfl).elim,ih⟩

omit [StarOrderedRing A] in
theorem powerBlock_chain (k : ℤ) (x : A) :
    (powerBlock k x).IsChain (LetterRelation τ) := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => simp [powerBlock]
    | succ n => exact letterBlock_chain true n x
  | negSucc n => exact letterBlock_chain false n x

omit [StarOrderedRing A] in
theorem powerBlock_chain_append (k : ℤ) (x : A) (hx : τ x = 0)
    {w : List (Bool × A)} (hw : w.IsChain (LetterRelation τ)) :
    (powerBlock k x ++ w).IsChain (LetterRelation τ) := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => simpa [powerBlock] using hw
    | succ n => exact letterBlock_chain_append true n x hx hw
  | negSucc n => exact letterBlock_chain_append false n x hx hw

def powerBlocks (w : List (ℤ × A)) : List (Bool × A) :=
  w.flatMap (fun a => powerBlock a.1 a.2)

omit [PartialOrder A] [StarOrderedRing A] in
theorem powerBlocks_value (u : unitary A) {w : List (ℤ × A)}
    (hw : ∀ a ∈ w, a.1 ≠ 0) : letterWord u (powerBlocks w) = signedWord u w := by
  induction w with
  | nil => simp [powerBlocks,letterWord,signedWord]
  | cons a w ih =>
    have htail : ∀ a ∈ w, a.1 ≠ 0 := fun a ha => hw a (List.mem_cons_of_mem _ ha)
    calc
      _ = letterWord u (powerBlock a.1 a.2) * letterWord u (powerBlocks w) := by
        simp [powerBlocks,letterWord,List.map_append,List.prod_append]
      _ = _ := by
        rw [powerBlock_value u a.1 (hw a (by simp)),ih htail]
        simp [signedWord]

omit [PartialOrder A] [StarOrderedRing A] in
theorem powerBlocks_mem {w : List (ℤ × A)} (hw : ∀ a ∈ w, a.2 ∈ P) :
    ∀ a ∈ powerBlocks w, a.2 ∈ P := by
  intro a ha
  obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp ha
  exact powerBlock_mem b.1 b.2 (hw b hb) a ha

omit [StarOrderedRing A] in
theorem powerBlocks_chain {w : List (ℤ × A)} (hw : ∀ a ∈ w, τ a.2 = 0) :
    (powerBlocks w).IsChain (LetterRelation τ) := by
  induction w with
  | nil => simp [powerBlocks]
  | cons a w ih =>
    exact powerBlock_chain_append a.1 a.2 (hw a (by simp))
      (ih (fun b hb => hw b (List.mem_cons_of_mem _ hb)))

omit [PartialOrder A] [StarOrderedRing A] in
theorem powerBlocks_ne_nil {w : List (ℤ × A)} (hne : w ≠ [])
    (hw : ∀ a ∈ w, a.1 ≠ 0) : powerBlocks w ≠ [] := by
  cases w with
  | nil => contradiction
  | cons a w =>
    intro h
    have he : powerBlock a.1 a.2 = [] := (List.append_eq_nil_iff.mp h).1
    exact powerBlock_ne_nil a.1 (hw a (by simp)) a.2 he

omit [StarOrderedRing A] in
theorem haar_twist_moments (hτ : FaithfulTracial τ)
    (s U : unitary A) (hs : (s:A) ∈ S) (hU : (U:A) ∈ P)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow s k) = 0)
    (hfree : ScalarFree τ (binaryCopy S P)) :
    (∀ k : ℤ, k ≠ 0 → τ (upow (s*U) k) = 0) ∧
    (∀ w : List (ℤ × A), w ≠ [] →
      (∀ a ∈ w, a.1 ≠ 0 ∧ a.2 ∈ P ∧ τ a.2 = 0) →
      τ ((w.map (fun a => upow (s*U) a.1 * a.2)).prod) = 0) := by
  constructor
  · intro k hk
    have hz := trace_letterWord hτ.1 hτ.2.1 s U hs hU hHaar hfree
      (powerBlock_ne_nil k hk 1) (powerBlock_mem k 1 P.one_mem) (powerBlock_chain k 1)
    simpa only [powerBlock_value _ _ hk, mul_one] using hz
  · intro w hne hw
    have hk : ∀ a ∈ w, a.1 ≠ 0 := fun a ha => (hw a ha).1
    have hz := trace_letterWord hτ.1 hτ.2.1 s U hs hU hHaar hfree
      (powerBlocks_ne_nil hne hk) (powerBlocks_mem (fun a ha => (hw a ha).2.1))
      (powerBlocks_chain (fun a ha => (hw a ha).2.2))
    simpa only [powerBlocks_value _ hk, signedWord] using hz

end

end KKFreeWords
end

end OAI
