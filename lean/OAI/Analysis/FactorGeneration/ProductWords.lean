import OAI.Analysis.FactorGeneration.ResidualMoments

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Exact signed-word expansion for a product of two unitaries. A unit gap
is allowed only between equal signs; opposite signs retain a centered gap. -/

section Algebra
variable {A : Type*} [Monoid A] [StarMul A]

def productLeft (u : A) (s : Bool) : A := if s then 1 else u
def productRight (u : A) (s : Bool) : A := if s then star u else 1

theorem signed_product_split (u v : A) (s : Bool) :
    algebraSignedLetter (u*v) s = productLeft u s*algebraSignedLetter v s*productRight u s := by
  cases s <;> simp [algebraSignedLetter,productLeft,productRight,star_mul]

def betweenWord (v : A) (s : Bool) : List (A × Bool) → A → A
  | [], b => algebraSignedLetter v s*b
  | (d,t)::xs, b => algebraSignedLetter v s*d*betweenWord v t xs b

def productGapList (u : A) (s : Bool) : List (A × Bool) → List (Bool × A)
  | [] => []
  | (d,t)::xs => (s,productRight u s*d*productLeft u t)::productGapList u t xs

def finalWordSign (s : Bool) : List (A × Bool) → Bool
  | [] => s
  | (_,t)::xs => finalWordSign t xs

theorem betweenWord_product (u v : A) (s : Bool) (xs : List (A × Bool)) (b : A) :
    betweenWord (u*v) s xs b = productLeft u s * algebraPatchingWord v
      (productGapList u s xs ++ [(finalWordSign s xs,productRight u (finalWordSign s xs)*b)]) := by
  induction xs generalizing s with
  | nil => simp [betweenWord,productGapList,finalWordSign,algebraPatchingWord,
      signed_product_split,mul_assoc]
  | cons a xs ih =>
    simp only [betweenWord,productGapList,finalWordSign,List.cons_append,
      algebraPatchingWord,signed_product_split,ih,mul_assoc]

end Algebra
section

open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem exactOrderedMoments_values (v : Q τ ω) (y : ℕ → Q τ ω)
    (hm : ExactOrderedMoments τ ω v y) (a b : Q τ ω)
    (ha : ∃ i : Option ℕ,optionalCoefficient y i=a)
    (hb : ∃ i : Option ℕ,optionalCoefficient y i=b)
    (xs : List (Bool × Q τ ω)) (hxs : ∀ z ∈ xs,∃ i,y i=z.2) (s : Bool) :
    quotientTrace τ ω (a*algebraPatchingWord v (xs++[(s,b)]))=0 := by
  have hencode : ∃ is : List (Bool × ℕ),is.map (fun z => (z.1,y z.2))=xs := by
    induction xs with
    | nil => exact ⟨[],rfl⟩
    | cons z xs ih =>
      obtain ⟨i,hi⟩ := hxs z (by simp)
      obtain ⟨is,his⟩ := ih (fun z hz => hxs z (by simp [hz]))
      exact ⟨(z.1,i)::is,by simp [hi,his]⟩
  obtain ⟨i,rfl⟩ := ha
  obtain ⟨j,rfl⟩ := hb
  obtain ⟨is,rfl⟩ := hencode
  exact hm i j is s

/-- Centered coefficients may separate arbitrary signs; unit coefficients may
only separate equal signs. This excludes cancellation through an internal unit. -/
def ProductGaps (x : ℕ → Q τ ω) (s : Bool) : List (Q τ ω × Bool) → Prop
  | [] => True
  | (d,t)::xs => ((∃ i,x i=d) ∨ (d=1 ∧ s=t)) ∧ ProductGaps x t xs

def ReducedOrderedMoments (t : Q τ ω) (x : ℕ → Q τ ω) : Prop :=
  ∀ a b : Option ℕ,∀ s : Bool,∀ xs : List (Q τ ω × Bool),
    ProductGaps τ ω x s xs →
    quotientTrace τ ω (optionalCoefficient x a*betweenWord t s xs (optionalCoefficient x b))=0

end

/-! The actual countable centered coefficients needed to expand words in UV. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

abbrev ProductFamilyIndex := ℕ ⊕ ((Bool × Option ℕ) ⊕ ℕ)

def productFamilyValue (u : Q τ ω) (x : ℕ → Q τ ω) : ProductFamilyIndex → Q τ ω
  | .inl i => x i
  | .inr (.inl (s,i)) => if s then star u*optionalCoefficient x i else optionalCoefficient x i*u
  | .inr (.inr i) => star u*x i*u

def productCenteredFamily (u : Q τ ω) (x : ℕ → Q τ ω) (n : ℕ) : Q τ ω :=
  match Encodable.decode (α := ProductFamilyIndex) n with
  | none => 0
  | some i => productFamilyValue τ ω u x i

theorem productCenteredFamily_encode (u : Q τ ω) (x : ℕ → Q τ ω) (i : ProductFamilyIndex) :
    productCenteredFamily τ ω u x (Encodable.encode i)=productFamilyValue τ ω u x i := by
  simp [productCenteredFamily]

theorem productCenteredFamily_centered (u : Q τ ω) (x : ℕ → Q τ ω)
    (hu : u*star u=1) (hx : ∀ i,quotientTrace τ ω (x i)=0)
    (hm : ExactOrderedMoments τ ω u x) :
    ∀ i,quotientTrace τ ω (productCenteredFamily τ ω u x i)=0 := by
  intro n
  unfold productCenteredFamily
  cases Encodable.decode (α := ProductFamilyIndex) n with
  | none => exact (traceLinear τ ω).map_zero
  | some i =>
    cases i with
    | inl j => exact hx j
    | inr i =>
      cases i with
      | inl a =>
        rcases a with ⟨s,j⟩
        cases s
        · simpa [productFamilyValue,algebraPatchingWord,algebraSignedLetter,optionalCoefficient]
            using hm j none [] false
        · simpa [productFamilyValue,algebraPatchingWord,algebraSignedLetter,optionalCoefficient]
            using hm none j [] true
      | inr j =>
        change quotientTrace τ ω (star u*x j*u)=0
        rw [quotientTrace_mul_comm τ ω (star u*x j),← mul_assoc,hu,one_mul]
        exact hx j

theorem productFamily_original (u : Q τ ω) (x : ℕ → Q τ ω) (i : ℕ) :
    ∃ j,productCenteredFamily τ ω u x j=x i :=
  ⟨Encodable.encode (Sum.inl i : ProductFamilyIndex),productCenteredFamily_encode τ ω u x _⟩

theorem productFamily_right (u : Q τ ω) (x : ℕ → Q τ ω) (i : Option ℕ) :
    ∃ j,productCenteredFamily τ ω u x j=optionalCoefficient x i*u :=
  ⟨Encodable.encode (Sum.inr (Sum.inl (false,i)) : ProductFamilyIndex),
    productCenteredFamily_encode τ ω u x _⟩

theorem productFamily_left (u : Q τ ω) (x : ℕ → Q τ ω) (i : Option ℕ) :
    ∃ j,productCenteredFamily τ ω u x j=star u*optionalCoefficient x i :=
  ⟨Encodable.encode (Sum.inr (Sum.inl (true,i)) : ProductFamilyIndex),
    productCenteredFamily_encode τ ω u x _⟩

theorem productFamily_conjugate (u : Q τ ω) (x : ℕ → Q τ ω) (i : ℕ) :
    ∃ j,productCenteredFamily τ ω u x j=star u*x i*u :=
  ⟨Encodable.encode (Sum.inr (Sum.inr i) : ProductFamilyIndex),
    productCenteredFamily_encode τ ω u x _⟩

theorem productFamily_optional (u : Q τ ω) (x : ℕ → Q τ ω) (i : Option ℕ) :
    ∃ j : Option ℕ,optionalCoefficient (productCenteredFamily τ ω u x) j=optionalCoefficient x i := by
  cases i with
  | none => exact ⟨none,rfl⟩
  | some i =>
    obtain ⟨j,hj⟩ := productFamily_original τ ω u x i
    exact ⟨some j,hj⟩

theorem productFamily_first (u : Q τ ω) (x : ℕ → Q τ ω) (a : Option ℕ) (s : Bool) :
    ∃ j : Option ℕ,optionalCoefficient (productCenteredFamily τ ω u x) j=
      optionalCoefficient x a*productLeft u s := by
  cases s
  · obtain ⟨j,hj⟩ := productFamily_right τ ω u x a
    exact ⟨some j,hj⟩
  · simpa [productLeft] using productFamily_optional τ ω u x a

theorem productFamily_last (u : Q τ ω) (x : ℕ → Q τ ω) (b : Option ℕ) (s : Bool) :
    ∃ j : Option ℕ,optionalCoefficient (productCenteredFamily τ ω u x) j=
      productRight u s*optionalCoefficient x b := by
  cases s
  · simpa [productRight] using productFamily_optional τ ω u x b
  · obtain ⟨j,hj⟩ := productFamily_left τ ω u x b
    exact ⟨some j,hj⟩

theorem productFamily_gap (u : Q τ ω) (x : ℕ → Q τ ω)
    (s t : Bool) (d : Q τ ω) (hd : (∃ i,x i=d) ∨ (d=1 ∧ s=t)) :
    ∃ j,productCenteredFamily τ ω u x j=productRight u s*d*productLeft u t := by
  rcases hd with ⟨i,rfl⟩ | ⟨rfl,rfl⟩
  · cases s <;> cases t
    · simpa [productRight,productLeft,optionalCoefficient] using productFamily_right τ ω u x (some i)
    · simpa [productRight,productLeft] using productFamily_original τ ω u x i
    · simpa [productRight,productLeft] using productFamily_conjugate τ ω u x i
    · simpa [productRight,productLeft,optionalCoefficient] using productFamily_left τ ω u x (some i)
  · cases s
    · simpa [productRight,productLeft,optionalCoefficient] using productFamily_right τ ω u x none
    · simpa [productRight,productLeft,optionalCoefficient] using productFamily_left τ ω u x none

theorem productGapList_members (u : Q τ ω) (x : ℕ → Q τ ω)
    (s : Bool) (xs : List (Q τ ω × Bool)) (hx : ProductGaps τ ω x s xs) :
    ∀ z ∈ productGapList u s xs,∃ i,productCenteredFamily τ ω u x i=z.2 := by
  induction xs generalizing s with
  | nil => simp [productGapList]
  | cons a xs ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact productFamily_gap τ ω u x s a.2 a.1 hx.1
    · exact ih a.2 hx.2 z hz

/-- The product has every reduced signed moment, including same-sign unit gaps. -/
theorem product_reduced_moment (u v : Q τ ω) (x : ℕ → Q τ ω)
    (hm : ExactOrderedMoments τ ω v (productCenteredFamily τ ω u x))
    (a b : Option ℕ) (s : Bool) (xs : List (Q τ ω × Bool))
    (hx : ProductGaps τ ω x s xs) :
    quotientTrace τ ω (optionalCoefficient x a*betweenWord (u*v) s xs
      (optionalCoefficient x b))=0 := by
  rw [betweenWord_product,← mul_assoc]
  exact exactOrderedMoments_values τ ω v _ hm _ _
    (productFamily_first τ ω u x a s)
    (productFamily_last τ ω u x b (finalWordSign s xs)) _
    (productGapList_members τ ω u x s xs hx) _

end

/-! Expand positive-length signed powers into individual letters. Repeated
letters have unit gaps; boundaries between powers retain centered coefficients. -/

section Algebra
variable {A : Type*} [Monoid A] [StarMul A]

def powerBlockGaps (s : Bool) (n : ℕ) : List (A × (Bool × ℕ)) → List (A × Bool)
  | [] => List.replicate n (1,s)
  | (d,(t,k))::xs => List.replicate n (1,s) ++ (d,t)::powerBlockGaps t k xs

def powerBlockWord (v : A) (s : Bool) (n : ℕ) : List (A × (Bool × ℕ)) → A → A
  | [],b => algebraSignedLetter v s^(n+1)*b
  | (d,(t,k))::xs,b => algebraSignedLetter v s^(n+1)*d*powerBlockWord v t k xs b

theorem betweenWord_repeat_prefix (v : A) (s : Bool) (n : ℕ) (xs : List (A × Bool)) (b : A) :
    betweenWord v s (List.replicate n (1,s) ++ xs) b =
      algebraSignedLetter v s^n*betweenWord v s xs b := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ,betweenWord,ih,pow_succ',mul_assoc]

theorem powerBlockWord_expand (v : A) (s : Bool) (n : ℕ)
    (xs : List (A × (Bool × ℕ))) (b : A) :
    powerBlockWord v s n xs b = betweenWord v s (powerBlockGaps s n xs) b := by
  induction xs generalizing s n with
  | nil =>
    rw [powerBlockGaps,← List.append_nil (List.replicate n (1,s)),betweenWord_repeat_prefix]
    simp [powerBlockWord,betweenWord,pow_succ,mul_assoc]
  | cons a xs ih =>
    rcases a with ⟨d,t,k⟩
    simp only [powerBlockGaps,betweenWord_repeat_prefix,betweenWord,powerBlockWord,ih,
      pow_succ,mul_assoc]

/-- Magnitude is encoded as predecessor, so every resulting block has positive length. -/
def integerPowerBlock : ℤ → Bool × ℕ
  | .ofNat n => (false,n-1)
  | .negSucc n => (true,n)

theorem integerPowerBlock_eval (v : unitary A) (n : ℤ) (hn : n ≠ 0) :
    (↑(v^n) : A)=algebraSignedLetter (v : A) (integerPowerBlock n).1^
      ((integerPowerBlock n).2+1) := by
  cases n with
  | ofNat n =>
    cases n with
    | zero => exact (hn rfl).elim
    | succ n =>
      change (↑(v^((n+1 : ℕ) : ℤ)) : A)=(v : A)^(n+1)
      rw [zpow_natCast]
      rfl
  | negSucc n =>
    rw [zpow_negSucc]
    change star ((v : A)^(n+1))=_
    simp [integerPowerBlock,algebraSignedLetter,star_pow]

def integerWord (v : unitary A) (x : ℕ → A) (n : ℤ) : List (ℕ × ℤ) → A → A
  | [],b => (↑(v^n) : A)*b
  | (i,m)::xs,b => (↑(v^n) : A)*x i*integerWord v x m xs b

theorem integerWord_blocks (v : unitary A) (x : ℕ → A) (n : ℤ) (hn : n ≠ 0)
    (xs : List (ℕ × ℤ)) (hxs : ∀ a ∈ xs,a.2 ≠ 0) (b : A) :
    integerWord v x n xs b = powerBlockWord (v : A) (integerPowerBlock n).1
      (integerPowerBlock n).2 (xs.map (fun a => (x a.1,integerPowerBlock a.2))) b := by
  induction xs generalizing n with
  | nil => simp [integerWord,powerBlockWord,integerPowerBlock_eval v n hn]
  | cons a xs ih =>
    simp only [integerWord,List.map_cons,powerBlockWord,integerPowerBlock_eval v n hn]
    rw [ih a.2 (hxs a (by simp)) (fun z hz => hxs z (by simp [hz]))]

end Algebra

open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem productGaps_repeat_prefix (x : ℕ → Q τ ω) (s : Bool) (n : ℕ)
    (xs : List (Q τ ω × Bool)) (hx : ProductGaps τ ω x s xs) :
    ProductGaps τ ω x s (List.replicate n (1,s)++xs) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [List.replicate_succ,List.cons_append]
    exact ⟨Or.inr ⟨rfl,rfl⟩,ih⟩

theorem productGaps_powerBlocks (x : ℕ → Q τ ω) (s : Bool) (n : ℕ)
    (xs : List (Q τ ω × (Bool × ℕ))) (hx : ∀ z ∈ xs,∃ i,x i=z.1) :
    ProductGaps τ ω x s (powerBlockGaps s n xs) := by
  induction xs generalizing s n with
  | nil =>
    simpa [powerBlockGaps] using productGaps_repeat_prefix τ ω x s n [] trivial
  | cons a xs ih =>
    apply productGaps_repeat_prefix
    exact ⟨Or.inl (hx a (by simp)),ih a.2.1 a.2.2 (fun z hz => hx z (by simp [hz]))⟩

theorem reducedOrderedMoments_integerWord (v : unitary (Q τ ω)) (x : ℕ → Q τ ω)
    (hm : ReducedOrderedMoments τ ω (v : Q τ ω) x)
    (a b : Option ℕ) (n : ℤ) (hn : n ≠ 0) (xs : List (ℕ × ℤ))
    (hxs : ∀ z ∈ xs,z.2 ≠ 0) :
    quotientTrace τ ω (optionalCoefficient x a*integerWord v x n xs (optionalCoefficient x b))=0 := by
  rw [integerWord_blocks v x n hn xs hxs,powerBlockWord_expand]
  apply hm
  apply productGaps_powerBlocks
  intro z hz
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hz
  exact ⟨j.1,rfl⟩

theorem reducedOrderedMoments_haar (v : unitary (Q τ ω)) (x : ℕ → Q τ ω)
    (hm : ReducedOrderedMoments τ ω (v : Q τ ω) x) (n : ℤ) (hn : n ≠ 0) :
    quotientTrace τ ω (↑(v^n) : Q τ ω)=0 := by
  simpa [optionalCoefficient,integerWord] using
    reducedOrderedMoments_integerWord τ ω v x hm none none n hn [] (by simp)

end Generator.Tracial

end

end OAI
