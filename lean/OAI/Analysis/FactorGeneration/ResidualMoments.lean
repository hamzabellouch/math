import Mathlib.Logic.Encodable.Basic
import OAI.Analysis.FactorGeneration.HaarPatches
import OAI.Analysis.FactorGeneration.QuotientHilbert

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Valid residual-corner identities in the actual quotient. Compression
centering requires two exact moments; global centering alone is insufficient. -/
section
open Filter
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem quotient_partial_residual_annihilation (v p : Q τ ω) (hp : IsStarProjection p)
    (hi : star v*v=p) (hf : v*star v=p) :
    v*(1-p)=0 ∧ star v*(1-p)=0 ∧ (1-p)*v=0 ∧ (1-p)*star v=0 := by
  have hpf : p*(1-p)=0 := by rw [mul_sub,mul_one,hp.isIdempotentElem.eq,sub_self]
  have hstar : star (1-p)=1-p := by rw [star_sub,star_one,hp.isSelfAdjoint.star_eq]
  have hright (a : Q τ ω) (ha : star a*a=p) : a*(1-p)=0 := by
    apply trace_square_faithful τ ω
    rw [star_mul,hstar,mul_assoc,← mul_assoc (star a),ha,hpf,mul_zero]
    exact (traceLinear τ ω).map_zero
  have h1 := hright v hi
  have h2 := hright (star v) (by simpa only [star_star] using hf)
  refine ⟨h1,h2,?_,?_⟩
  · simpa only [star_mul,hstar,star_star,star_zero] using congrArg star h2
  · simpa only [star_mul,hstar,star_zero] using congrArg star h1

theorem quotient_residual_compression_trace (v p z : Q τ ω)
    (hp : IsStarProjection p) (hf : v*star v=p) :
    quotientTrace τ ω ((1-p)*z*(1-p)) =
      quotientTrace τ ω z - quotientTrace τ ω (star v*z*v) := by
  have hff : (1-p)*(1-p)=1-p := by
    noncomm_ring [hp.isIdempotentElem.eq]
  calc quotientTrace τ ω ((1-p)*z*(1-p)) = quotientTrace τ ω (z*(1-p)*(1-p)) := by
         rw [mul_assoc (1-p) z (1-p),quotientTrace_mul_comm τ ω (1-p) (z*(1-p))]
       _ = quotientTrace τ ω (z*(1-p)) := by rw [mul_assoc,hff]
       _ = quotientTrace τ ω z - quotientTrace τ ω (z*p) := by
         rw [mul_sub,mul_one]
         exact (traceLinear τ ω).map_sub z (z*p)
       _ = quotientTrace τ ω z - quotientTrace τ ω (star v*z*v) := by
         rw [← hf,← mul_assoc z v (star v),quotientTrace_mul_comm τ ω (z*v) (star v),mul_assoc]

theorem quotient_residual_centered (v p z : Q τ ω) (hp : IsStarProjection p)
    (hf : v*star v=p) (hz : quotientTrace τ ω z=0)
    (hvz : quotientTrace τ ω (star v*z*v)=0) :
    quotientTrace τ ω ((1-p)*z*(1-p))=0 := by
  rw [quotient_residual_compression_trace τ ω v p z hp hf,hz,hvz,sub_self]

theorem algebraPatchingWord_append {A : Type*} [Monoid A] [Star A]
    (v : A) (xs ys : List (Bool × A)) :
    algebraPatchingWord v (xs++ys)=algebraPatchingWord v xs*algebraPatchingWord v ys := by
  induction xs with
  | nil => simp [algebraPatchingWord]
  | cons a xs ih => simp only [List.cons_append,algebraPatchingWord,ih,mul_assoc]

theorem quotient_residual_word_centered (v p : Q τ ω) (hp : IsStarProjection p)
    (hf : v*star v=p) (x : ℕ → Q τ ω)
    (hm : ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
      quotientTrace τ ω (optionalCoefficient x first *
        algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++
          [(s,optionalCoefficient x last)]))=0)
    (i j : ℕ) (xs : List (Bool × ℕ)) (s : Bool) :
    quotientTrace τ ω ((1-p)*(x i *
      algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++ [(s,x j)]))*(1-p))=0 := by
  apply quotient_residual_centered τ ω v p _ hp hf
  · exact hm (some i) (some j) xs s
  · have h := hm none none ((true,i)::(xs++[(s,j)])) false
    simpa [optionalCoefficient,algebraPatchingWord,algebraSignedLetter,
      algebraPatchingWord_append,mul_assoc] using h

/-! All residual middle coefficients from exact independence: the original
centered coefficients, words with two centered endpoints, and the vanishing
compressions when an endpoint is the unit. -/

theorem quotient_residual_signed_annihilation (v p : Q τ ω) (hp : IsStarProjection p)
    (hi : star v*v=p) (hf : v*star v=p) (s : Bool) :
    (1-p)*algebraSignedLetter v s=0 ∧ algebraSignedLetter v s*(1-p)=0 := by
  obtain ⟨h1,h2,h3,h4⟩ := quotient_partial_residual_annihilation τ ω v p hp hi hf
  cases s
  · exact ⟨h3,h1⟩
  · exact ⟨h4,h2⟩

theorem quotient_residual_word_unit_left (v p : Q τ ω) (hp : IsStarProjection p)
    (hi : star v*v=p) (hf : v*star v=p) (ys : List (Bool × Q τ ω)) (hy : ys ≠ []) :
    (1-p)*algebraPatchingWord v ys=0 := by
  cases ys with
  | nil => exact (hy rfl).elim
  | cons a ys =>
    simp only [algebraPatchingWord,← mul_assoc,
      (quotient_residual_signed_annihilation τ ω v p hp hi hf a.1).1,zero_mul]

theorem quotient_residual_word_unit_right (v p : Q τ ω) (hp : IsStarProjection p)
    (hi : star v*v=p) (hf : v*star v=p) (ys : List (Bool × Q τ ω)) (s : Bool) :
    algebraPatchingWord v (ys++[(s,1)])*(1-p)=0 := by
  rw [algebraPatchingWord_append]
  simp only [algebraPatchingWord,mul_one,mul_assoc,
    (quotient_residual_signed_annihilation τ ω v p hp hi hf s).2,mul_zero]

theorem quotient_residual_all_words_centered (v p : Q τ ω) (hp : IsStarProjection p)
    (hi : star v*v=p) (hf : v*star v=p) (x : ℕ → Q τ ω)
    (hm : ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
      quotientTrace τ ω (optionalCoefficient x first *
        algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++
          [(s,optionalCoefficient x last)]))=0)
    (first last : Option ℕ) (xs : List (Bool × ℕ)) (s : Bool) :
    quotientTrace τ ω ((1-p)*(optionalCoefficient x first *
      algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++
        [(s,optionalCoefficient x last)]))*(1-p))=0 := by
  cases first with
  | none =>
    simp only [optionalCoefficient,one_mul]
    rw [quotient_residual_word_unit_left τ ω v p hp hi hf _ (by simp),zero_mul]
    exact (traceLinear τ ω).map_zero
  | some i =>
    cases last with
    | none =>
      change quotientTrace τ ω ((1-p)*(x i*algebraPatchingWord v
        (xs.map (fun a => (a.1,x a.2)) ++ [(s,1)]))*(1-p))=0
      rw [mul_assoc,mul_assoc,
        quotient_residual_word_unit_right τ ω v p hp hi hf,mul_zero,mul_zero]
      exact (traceLinear τ ω).map_zero
    | some j => exact quotient_residual_word_centered τ ω v p hp hf x hm i j xs s

theorem quotient_residual_coefficient_centered (v p : Q τ ω) (hp : IsStarProjection p)
    (hf : v*star v=p) (x : ℕ → Q τ ω) (hc : ∀ i,quotientTrace τ ω (x i)=0)
    (hm : ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
      quotientTrace τ ω (optionalCoefficient x first *
        algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++
          [(s,optionalCoefficient x last)]))=0) (i : ℕ) :
    quotientTrace τ ω ((1-p)*x i*(1-p))=0 := by
  apply quotient_residual_centered τ ω v p (x i) hp hf (hc i)
  simpa [optionalCoefficient,algebraPatchingWord,algebraSignedLetter] using
      hm none none [(true,i)] false

end

/-! A countable family containing every original coefficient and every old
nonempty ordered signed word, with both optional endpoints retained. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

abbrev ResidualWordIndex := ℕ ⊕ (Option ℕ × Option ℕ × List (Bool × ℕ) × Bool)

def residualWordValue (v : Q τ ω) (x : ℕ → Q τ ω) : ResidualWordIndex → Q τ ω
  | .inl i => x i
  | .inr (first,last,xs,s) => optionalCoefficient x first *
      algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++ [(s,optionalCoefficient x last)])

def residualWordFamily (v : Q τ ω) (x : ℕ → Q τ ω) (i : ℕ) : Q τ ω :=
  match Encodable.decode (α := ResidualWordIndex) i with
  | none => 0
  | some k => residualWordValue τ ω v x k

theorem residualWordFamily_encode (v : Q τ ω) (x : ℕ → Q τ ω) (k : ResidualWordIndex) :
    residualWordFamily τ ω v x (Encodable.encode k)=residualWordValue τ ω v x k := by
  simp [residualWordFamily]

theorem residualWordFamily_contains_coefficient (v : Q τ ω) (x : ℕ → Q τ ω) (i : ℕ) :
    ∃ j,residualWordFamily τ ω v x j=x i :=
  ⟨Encodable.encode (Sum.inl i : ResidualWordIndex),residualWordFamily_encode τ ω v x (.inl i)⟩

theorem residualWordFamily_contains_word (v : Q τ ω) (x : ℕ → Q τ ω)
    (first last : Option ℕ) (xs : List (Bool × ℕ)) (s : Bool) :
    ∃ j,residualWordFamily τ ω v x j=optionalCoefficient x first *
      algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++ [(s,optionalCoefficient x last)]) :=
  ⟨Encodable.encode (Sum.inr (first,last,xs,s) : ResidualWordIndex),
    residualWordFamily_encode τ ω v x (.inr (first,last,xs,s))⟩

theorem residualWordFamily_compression_centered (v p : Q τ ω) (hp : IsStarProjection p)
    (hi : star v*v=p) (hf : v*star v=p) (x : ℕ → Q τ ω)
    (hc : ∀ i,quotientTrace τ ω (x i)=0)
    (hm : ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
      quotientTrace τ ω (optionalCoefficient x first *
        algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++
          [(s,optionalCoefficient x last)]))=0) :
    ∀ i,quotientTrace τ ω ((1-p)*residualWordFamily τ ω v x i*(1-p))=0 := by
  intro i
  unfold residualWordFamily
  cases h : Encodable.decode (α := ResidualWordIndex) i with
  | none => simp only [mul_zero,zero_mul]; exact (traceLinear τ ω).map_zero
  | some k =>
    cases k with
    | inl j => exact quotient_residual_coefficient_centered τ ω v p hp hf x hc hm j
    | inr k =>
      rcases k with ⟨first,last,xs,s⟩
      exact quotient_residual_all_words_centered τ ω v p hp hi hf x hm first last xs s

/-! Ordered mixed words grouped at each increment letter. The intervening
old runs are actual members of the previously enumerated residual family. -/

theorem residualWordFamily_contains_run (v : Q τ ω) (x : ℕ → Q τ ω)
    (i : ℕ) (pre : List (Bool × ℕ)) :
    ∃ j,residualWordFamily τ ω v x j=x i*
      algebraPatchingWord v (pre.map (fun a => (a.1,x a.2))) := by
  induction pre using List.reverseRecOn with
  | nil => simpa [algebraPatchingWord] using residualWordFamily_contains_coefficient τ ω v x i
  | append_singleton pre a ih =>
    simpa [List.map_append,optionalCoefficient] using
      residualWordFamily_contains_word τ ω v x (some i) (some a.2) pre a.1

theorem residualWordFamily_contains_outer_run (v : Q τ ω) (x : ℕ → Q τ ω)
    (first : Option ℕ) (pre : List (Bool × ℕ)) :
    ∃ j : Option ℕ,optionalCoefficient (residualWordFamily τ ω v x) j=
      optionalCoefficient x first*algebraPatchingWord v (pre.map (fun a => (a.1,x a.2))) := by
  induction pre using List.reverseRecOn with
  | nil =>
    cases first with
    | none => exact ⟨none,by simp [optionalCoefficient,algebraPatchingWord]⟩
    | some i =>
      obtain ⟨j,hj⟩ := residualWordFamily_contains_coefficient τ ω v x i
      exact ⟨some j,by simpa [optionalCoefficient,algebraPatchingWord] using hj⟩
  | append_singleton pre a ih =>
    obtain ⟨j,hj⟩ := residualWordFamily_contains_word τ ω v x first (some a.2) pre a.1
    exact ⟨some j,by simpa [List.map_append,optionalCoefficient] using hj⟩

def algebraMixedTail {A : Type*} [Monoid A] [Star A] (v w : A) (x : ℕ → A)
    (last : Option ℕ) (b s : Bool) : List (Bool × Bool × ℕ) → A
  | [] => algebraSignedLetter (if b then w else v) s * optionalCoefficient x last
  | (c,t,i)::xs => algebraSignedLetter (if c then w else v) t*x i*
      algebraMixedTail v w x last b s xs

/-- Every actual ordered mixed term is either the original word or an ordered
increment word with enumerated internal blocks and an explicit old prefix. -/
theorem algebraMixedTail_normalize (v w : Q τ ω) (x : ℕ → Q τ ω)
    (last : Option ℕ) (b s : Bool) (xs : List (Bool × Bool × ℕ)) :
    algebraMixedTail v w x last b s xs =
      algebraPatchingWord v (xs.map (fun a => (a.2.1,x a.2.2)) ++
        [(s,optionalCoefficient x last)]) ∨
    ∃ pre : List (Bool × ℕ), ∃ ys : List (Bool × ℕ), ∃ t : Bool, ∃ last' : Option ℕ,
      algebraMixedTail v w x last b s xs =
        algebraPatchingWord v (pre.map (fun a => (a.1,x a.2))) *
        algebraPatchingWord w (ys.map (fun a => (a.1,residualWordFamily τ ω v x a.2)) ++
          [(t,optionalCoefficient (residualWordFamily τ ω v x) last')]) := by
  induction xs with
  | nil =>
    cases b with
    | false => exact Or.inl (by simp [algebraMixedTail,algebraPatchingWord])
    | true =>
      obtain ⟨j,hj⟩ := residualWordFamily_contains_outer_run τ ω v x last []
      refine Or.inr ⟨[],[],s,j,?_⟩
      simp only [List.map_nil,algebraPatchingWord,mul_one] at hj
      simp [algebraMixedTail,algebraPatchingWord,hj]
  | cons a xs ih =>
    rcases a with ⟨c,t,i⟩
    cases c with
    | false =>
      rcases ih with h | ⟨pre,ys,u,last',h⟩
      · exact Or.inl (by simp [algebraMixedTail,algebraPatchingWord,h])
      · exact Or.inr ⟨(t,i)::pre,ys,u,last',by
          simp only [algebraMixedTail,Bool.false_eq_true,↓reduceIte,h,List.map_cons,
            algebraPatchingWord,mul_assoc]⟩
    | true =>
      rcases ih with h | ⟨pre,ys,u,last',h⟩
      · obtain ⟨j,hj⟩ := residualWordFamily_contains_word τ ω v x (some i) last
          (xs.map (fun a => (a.2.1,a.2.2))) s
        refine Or.inr ⟨[],[],t,some j,?_⟩
        simp only [algebraMixedTail,↓reduceIte,h,List.map_nil,List.nil_append,
          algebraPatchingWord,one_mul,mul_one,optionalCoefficient]
        simp only [List.map_map,Function.comp_def,optionalCoefficient] at hj
        rw [hj,mul_assoc]
      · obtain ⟨j,hj⟩ := residualWordFamily_contains_run τ ω v x i pre
        refine Or.inr ⟨[],(t,j)::ys,u,last',?_⟩
        simp only [algebraMixedTail,↓reduceIte,h,List.map_nil,List.map_cons,
          List.cons_append,algebraPatchingWord,one_mul]
        rw [hj]
        simp only [mul_assoc]

end

/-! Cyclic endpoint correction for residual patching. Outer endpoints are
multiplied before compression, and the scalar part is handled separately. -/
section
open UltrapowerBridge Filter

def algebraWordCore {A : Type*} [Monoid A] [Star A] (v : A) (x : ℕ → A)
    (s : Bool) : List (Bool × ℕ) → A
  | [] => algebraSignedLetter v s
  | (t,i)::xs => algebraSignedLetter v t*x i*algebraWordCore v x s xs

theorem algebraWordCore_endpoints {A : Type*} [Monoid A] [Star A]
    (v : A) (x : ℕ → A) (last : Option ℕ) (s : Bool) (xs : List (Bool × ℕ)) :
    algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++
      [(s,optionalCoefficient x last)])=algebraWordCore v x s xs*optionalCoefficient x last := by
  induction xs with
  | nil => simp [algebraPatchingWord,algebraWordCore]
  | cons a xs ih => simp [algebraPatchingWord,algebraWordCore,ih,mul_assoc]

theorem algebraWordCore_map {A : Type*} [Monoid A] [Star A]
    (w : A) (x y : ℕ → A) (k : ℕ → ℕ) (h : ∀ i,x i=y (k i))
    (s : Bool) (xs : List (Bool × ℕ)) :
    algebraWordCore w x s xs=algebraWordCore w y s (xs.map (fun a => (a.1,k a.2))) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [algebraWordCore,List.map_cons,h,ih]

theorem algebraWordCore_support {A : Type*} [Monoid A] [Star A]
    (w f : A) (hw : ∀ s,f*algebraSignedLetter w s=algebraSignedLetter w s ∧
      algebraSignedLetter w s*f=algebraSignedLetter w s)
    (x : ℕ → A) (s : Bool) (xs : List (Bool × ℕ)) :
    f*algebraWordCore w x s xs=algebraWordCore w x s xs ∧
      algebraWordCore w x s xs*f=algebraWordCore w x s xs := by
  induction xs with
  | nil => exact hw s
  | cons a xs ih =>
    constructor
    · simp only [algebraWordCore,← mul_assoc,(hw a.1).1]
    · simp only [algebraWordCore,mul_assoc,ih.2]

theorem algebraWordCore_compress {A : Type*} [Monoid A] [Star A]
    (w f : A) (hw : ∀ s,f*algebraSignedLetter w s=algebraSignedLetter w s ∧
      algebraSignedLetter w s*f=algebraSignedLetter w s)
    (x : ℕ → A) (s : Bool) (xs : List (Bool × ℕ)) :
    algebraWordCore w (fun i => f*x i*f) s xs=algebraWordCore w x s xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [algebraWordCore,ih]
    calc algebraSignedLetter w a.1*(f*x a.2*f)*algebraWordCore w x s xs =
        (algebraSignedLetter w a.1*f)*x a.2*(f*algebraWordCore w x s xs) := by
          simp only [mul_assoc]
         _ = _ := by rw [(hw a.1).2,(algebraWordCore_support w f hw x s xs).1]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def ExactOrderedMoments (w : Q τ ω) (x : ℕ → Q τ ω) : Prop :=
  ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
    quotientTrace τ ω (optionalCoefficient x first * algebraPatchingWord w
      (xs.map (fun a => (a.1,x a.2)) ++ [(s,optionalCoefficient x last)]))=0

theorem exactOrderedMoments_core (w : Q τ ω) (x : ℕ → Q τ ω)
    (h : ExactOrderedMoments τ ω w x) (last : Option ℕ) (s : Bool) (xs : List (Bool × ℕ)) :
    quotientTrace τ ω (algebraWordCore w x s xs*optionalCoefficient x last)=0 := by
  have hh := h none last xs s
  rw [algebraWordCore_endpoints] at hh
  simpa only [optionalCoefficient,one_mul] using hh

theorem trace_supported_cyclic_compression (c f z : Q τ ω)
    (hl : f*c=c) (hr : c*f=c) :
    quotientTrace τ ω (c*(f*z*f))=quotientTrace τ ω (c*z) := by
  calc quotientTrace τ ω (c*(f*z*f)) = quotientTrace τ ω ((c*(f*z))*f) := by simp only [mul_assoc]
       _ = quotientTrace τ ω (f*(c*(f*z))) := quotientTrace_mul_comm τ ω _ _
       _ = quotientTrace τ ω (c*z) := by rw [← mul_assoc f c,hl,← mul_assoc c f,hr]

/-- Transfer exact moments from compressed internal coefficients and centered
cyclic endpoint products. The scalar correction uses the moment with both
endpoints equal to the unit. -/
theorem exact_moment_of_cyclic_family (w f : Q τ ω)
    (hw : ∀ s,f*algebraSignedLetter w s=algebraSignedLetter w s ∧
      algebraSignedLetter w s*f=algebraSignedLetter w s)
    (y z : ℕ → Q τ ω) (k : ℕ → ℕ) (hk : ∀ i,f*y i*f=z (k i))
    (hc : ∀ a b : Option ℕ,∃ j : ℕ,∃ c : ℂ,
      f*(optionalCoefficient y b*optionalCoefficient y a)*f=z j+c • f)
    (hm : ExactOrderedMoments τ ω w z)
    (a b : Option ℕ) (xs : List (Bool × ℕ)) (s : Bool) :
    quotientTrace τ ω (optionalCoefficient y a*algebraPatchingWord w
      (xs.map (fun t => (t.1,y t.2)) ++ [(s,optionalCoefficient y b)]))=0 := by
  let C := algebraWordCore w y s xs
  have hs := algebraWordCore_support w f hw y s xs
  have he : C=algebraWordCore w z s (xs.map (fun t => (t.1,k t.2))) := by
    dsimp only [C]
    rw [← algebraWordCore_compress w f hw y s xs]
    exact algebraWordCore_map w _ z k hk s xs
  obtain ⟨j,c,hj⟩ := hc a b
  have hzero : quotientTrace τ ω (C*z j)=0 := by
    rw [he]
    exact exactOrderedMoments_core τ ω w z hm (some j) s _
  have hunit : quotientTrace τ ω C=0 := by
    simpa only [he,optionalCoefficient,mul_one] using
      exactOrderedMoments_core τ ω w z hm none s (xs.map (fun t => (t.1,k t.2)))
  rw [algebraWordCore_endpoints,← mul_assoc]
  change quotientTrace τ ω (optionalCoefficient y a*C*optionalCoefficient y b)=0
  rw [quotientTrace_mul_comm τ ω (optionalCoefficient y a*C),← mul_assoc,
    quotientTrace_mul_comm τ ω (optionalCoefficient y b*optionalCoefficient y a) C]
  rw [← trace_supported_cyclic_compression τ ω C f _ hs.1 hs.2,hj,mul_add,
    mul_smul_comm,hs.2,trace_add,trace_smul,hzero,hunit,mul_zero,add_zero]

end

/-! Countable supported family for actual residual patching, including centered
cyclic products of the two outer blocks. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def quotientCornerCenter (f z : Q τ ω) : Q τ ω :=
  f*z*f-(quotientTrace τ ω (f*z*f)/quotientTrace τ ω f) • f

theorem quotientCornerCenter_supported (f z : Q τ ω) (hf : f*f=f) :
    f*quotientCornerCenter τ ω f z=quotientCornerCenter τ ω f z ∧
    quotientCornerCenter τ ω f z*f=quotientCornerCenter τ ω f z := by
  constructor
  · simp only [quotientCornerCenter,mul_sub,mul_smul_comm,← mul_assoc,hf]
  · simp only [quotientCornerCenter,sub_mul,smul_mul_assoc,mul_assoc,hf]

theorem quotientCornerCenter_trace (f z : Q τ ω) (ht : quotientTrace τ ω f ≠ 0) :
    quotientTrace τ ω (quotientCornerCenter τ ω f z)=0 := by
  unfold quotientCornerCenter
  change (traceLinear τ ω) (_-_) = 0
  rw [map_sub]
  change quotientTrace τ ω (f*z*f)-quotientTrace τ ω
    ((quotientTrace τ ω (f*z*f)/quotientTrace τ ω f) • f)=0
  rw [trace_smul,div_mul_cancel₀ _ ht,sub_self]

theorem quotientCornerCenter_decompose (f z : Q τ ω) :
    f*z*f=quotientCornerCenter τ ω f z+
      (quotientTrace τ ω (f*z*f)/quotientTrace τ ω f) • f := by
  unfold quotientCornerCenter
  abel

abbrev CyclicFamilyIndex := ℕ ⊕ (Option ℕ × Option ℕ)

def cyclicFamilyValue (f : Q τ ω) (y : ℕ → Q τ ω) : CyclicFamilyIndex → Q τ ω
  | .inl i => f*y i*f
  | .inr (a,b) => quotientCornerCenter τ ω f (optionalCoefficient y b*optionalCoefficient y a)

def cyclicResidualFamily (f : Q τ ω) (y : ℕ → Q τ ω) (i : ℕ) : Q τ ω :=
  match Encodable.decode (α := CyclicFamilyIndex) i with
  | none => 0
  | some k => cyclicFamilyValue τ ω f y k

theorem cyclicResidualFamily_encode (f : Q τ ω) (y : ℕ → Q τ ω) (k : CyclicFamilyIndex) :
    cyclicResidualFamily τ ω f y (Encodable.encode k)=cyclicFamilyValue τ ω f y k := by
  simp [cyclicResidualFamily]

theorem cyclicResidualFamily_supported (f : Q τ ω) (hf : f*f=f) (y : ℕ → Q τ ω) :
    ∀ i,f*cyclicResidualFamily τ ω f y i*f=cyclicResidualFamily τ ω f y i := by
  intro i
  unfold cyclicResidualFamily
  cases Encodable.decode (α := CyclicFamilyIndex) i with
  | none => simp only [mul_zero,zero_mul]
  | some k =>
    cases k with
    | inl j => simp only [cyclicFamilyValue,← mul_assoc,hf]; simp only [mul_assoc,hf]
    | inr ab =>
      obtain ⟨hl,hr⟩ := quotientCornerCenter_supported τ ω f
        (optionalCoefficient y ab.2*optionalCoefficient y ab.1) hf
      exact (congrArg (fun z => z*f) hl).trans hr

theorem cyclicResidualFamily_centered (f : Q τ ω) (hf : f*f=f)
    (ht : quotientTrace τ ω f ≠ 0) (y : ℕ → Q τ ω)
    (hy : ∀ i,quotientTrace τ ω (f*y i*f)=0) :
    ∀ i,quotientTrace τ ω (f*cyclicResidualFamily τ ω f y i*f)=0 := by
  intro i
  rw [cyclicResidualFamily_supported τ ω f hf]
  unfold cyclicResidualFamily
  cases Encodable.decode (α := CyclicFamilyIndex) i with
  | none => exact (traceLinear τ ω).map_zero
  | some k =>
    cases k with
    | inl j => exact hy j
    | inr ab => exact quotientCornerCenter_trace τ ω f _ ht

theorem cyclicResidualFamily_internal (f : Q τ ω) (y : ℕ → Q τ ω) :
    ∃ k : ℕ → ℕ,∀ i,f*y i*f=cyclicResidualFamily τ ω f y (k i) := by
  refine ⟨fun i => Encodable.encode (Sum.inl i : CyclicFamilyIndex),fun i => ?_⟩
  exact (cyclicResidualFamily_encode τ ω f y (.inl i)).symm

theorem cyclicResidualFamily_outer (f : Q τ ω) (y : ℕ → Q τ ω) :
    ∀ a b : Option ℕ,∃ j : ℕ,∃ c : ℂ,
      f*(optionalCoefficient y b*optionalCoefficient y a)*f=
        cyclicResidualFamily τ ω f y j+c • f := by
  intro a b
  refine ⟨Encodable.encode (Sum.inr (a,b) : CyclicFamilyIndex),
    quotientTrace τ ω (f*(optionalCoefficient y b*optionalCoefficient y a)*f)/quotientTrace τ ω f,?_⟩
  rw [cyclicResidualFamily_encode]
  exact quotientCornerCenter_decompose τ ω f _

end

/-! Exact preservation of every original ordered moment under orthogonal
patching, once the constructed cyclic residual family has exact moments. -/
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem algebraSignedLetter_add' {A : Type*} [AddMonoid A] [StarAddMonoid A]
    (v w : A) (s : Bool) :
    algebraSignedLetter (v+w) s=algebraSignedLetter v s+algebraSignedLetter w s := by
  cases s <;> simp [algebraSignedLetter,star_add]

/-- Distribute every signed letter while preserving the full multiplication
order. The premise is checked for actual mixed terms, not scalar estimates. -/
theorem ordered_sum_zero_of_all_mixed (v w : Q τ ω) (x : ℕ → Q τ ω)
    (last : Option ℕ) (s : Bool) (xs : List (Bool × ℕ)) (a : Q τ ω)
    (h : ∀ cs : List (Bool × Bool × ℕ),∀ b : Bool,
      quotientTrace τ ω (a*algebraMixedTail v w x last b s cs)=0) :
    quotientTrace τ ω (a*algebraPatchingWord (v+w)
      (xs.map (fun t => (t.1,x t.2)) ++ [(s,optionalCoefficient x last)]))=0 := by
  induction xs generalizing a with
  | nil =>
    have hv := h [] false
    have hw := h [] true
    simp only [algebraMixedTail,↓reduceIte,Bool.false_eq_true] at hv hw
    simp only [List.map_nil,List.nil_append,algebraPatchingWord,mul_one,
      algebraSignedLetter_add',add_mul,mul_add,trace_add,hv,hw,add_zero]
  | cons t xs ih =>
    have ht (b : Bool) : quotientTrace τ ω
        ((a*algebraSignedLetter (if b then w else v) t.1*x t.2)*
          algebraPatchingWord (v+w)
            (xs.map (fun t => (t.1,x t.2)) ++ [(s,optionalCoefficient x last)]))=0 := by
      apply ih
      intro cs c
      simpa only [algebraMixedTail,mul_assoc] using h ((b,t.1,t.2)::cs) c
    have hv := ht false
    have hw := ht true
    simp only [Bool.false_eq_true,↓reduceIte] at hv hw
    simp only [List.map_cons,List.cons_append,algebraPatchingWord,algebraSignedLetter_add',
      add_mul,mul_add,trace_add]
    simpa only [mul_assoc,add_zero] using congrArg₂ (·+·) hv hw

theorem exactOrderedMoments_add_of_cyclic (v w f : Q τ ω) (x : ℕ → Q τ ω)
    (hm : ExactOrderedMoments τ ω v x)
    (hs : ∀ s,f*algebraSignedLetter w s=algebraSignedLetter w s ∧
      algebraSignedLetter w s*f=algebraSignedLetter w s)
    (hw : ExactOrderedMoments τ ω w
      (cyclicResidualFamily τ ω f (residualWordFamily τ ω v x))) :
    ExactOrderedMoments τ ω (v+w) x := by
  intro first last xs s
  apply ordered_sum_zero_of_all_mixed τ ω v w x last s xs
  intro cs b
  rcases algebraMixedTail_normalize τ ω v w x last b s cs with h | ⟨pre,ys,t,last',h⟩
  · rw [h]
    simpa only [List.map_map,Function.comp_def] using
      hm first last (cs.map (fun a => (a.2.1,a.2.2))) s
  · obtain ⟨first',hfirst⟩ := residualWordFamily_contains_outer_run τ ω v x first pre
    rw [h,← mul_assoc,← hfirst]
    obtain ⟨k,hk⟩ := cyclicResidualFamily_internal τ ω f (residualWordFamily τ ω v x)
    exact exact_moment_of_cyclic_family τ ω w f hs _ _ k hk
      (cyclicResidualFamily_outer τ ω f _) hw first' last' ys t

end Generator.Tracial

end

end OAI
