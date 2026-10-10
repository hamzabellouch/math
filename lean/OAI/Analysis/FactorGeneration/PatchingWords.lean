import OAI.Analysis.FactorGeneration.PartialUnitaries

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Ordered signed mixed words in Popa 1308.3982v3, Lemma 3.2.
The L2 continuity estimate keeps the order of every coefficient. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def signedLetter (v : M.toStarSubalgebra) (s : Bool) : M.toStarSubalgebra :=
  if s then star v else v

def patchingWord (v : M.toStarSubalgebra) : List (Bool × M.toStarSubalgebra) → M.toStarSubalgebra
  | [] => 1
  | (s,x)::xs => signedLetter v s*x*patchingWord v xs

theorem signedLetter_norm (v : M.toStarSubalgebra) (s : Bool) :
    ‖signedLetter v s‖=‖v‖ := by
  cases s
  · rfl
  · change ‖star (v : H →L[ℂ] H)‖=‖(v : H →L[ℂ] H)‖
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.adjoint.norm_map _

theorem signedLetter_sub (v w : M.toStarSubalgebra) (s : Bool) :
    signedLetter v s-signedLetter w s=signedLetter (v-w) s := by
  cases s <;> simp [signedLetter,star_sub]

theorem signedLetter_norm₂ (τ : TracialRepresentation M) (v : M.toStarSubalgebra) (s : Bool) :
    τ.norm₂ (signedLetter v s)=τ.norm₂ v := by cases s <;> simp [signedLetter,τ.norm₂_star]

theorem patchingWord_norm_le_one (v : M.toStarSubalgebra) (hv : ‖v‖ ≤ 1)
    (xs : List (Bool × M.toStarSubalgebra)) (hx : ∀ a ∈ xs, ‖a.2‖ ≤ 1) :
    ‖patchingWord v xs‖ ≤ 1 := by
  induction xs with
  | nil => exact (IsStarProjection.one (M.toStarSubalgebra)).norm_le
  | cons a xs ih =>
    have ha := hx a (by simp)
    have ht := ih (fun b hb => hx b (by simp [hb]))
    have hs : ‖signedLetter v a.1*a.2‖ ≤ 1 :=
      (norm_mul_le _ _).trans ((mul_le_mul (by rw [signedLetter_norm]; exact hv) ha
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))
    exact (norm_mul_le _ _).trans ((mul_le_mul hs ht (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))

theorem patchingWord_norm₂_sub_le (τ : TracialRepresentation M)
    (v w : M.toStarSubalgebra) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (xs : List (Bool × M.toStarSubalgebra)) (hx : ∀ a ∈ xs, ‖a.2‖ ≤ 1) :
    τ.norm₂ (patchingWord v xs-patchingWord w xs) ≤ xs.length*τ.norm₂ (v-w) := by
  induction xs with
  | nil => simp [patchingWord]
  | cons a xs ih =>
    have ha := hx a (by simp)
    have htail : ∀ b ∈ xs, ‖b.2‖ ≤ 1 := fun b hb => hx b (by simp [hb])
    have he : patchingWord v (a::xs)-patchingWord w (a::xs) =
        ((signedLetter v a.1-signedLetter w a.1)*a.2)*patchingWord v xs+
        (signedLetter w a.1*a.2)*(patchingWord v xs-patchingWord w xs) := by
      simp [patchingWord,sub_mul,mul_sub]
    have hfirst : τ.norm₂ (((signedLetter v a.1-signedLetter w a.1)*a.2)*patchingWord v xs) ≤
        τ.norm₂ (v-w) := by
      have h1 := τ.norm₂_mul_le_right ((signedLetter v a.1-signedLetter w a.1)*a.2) (patchingWord v xs)
      have h2 := τ.norm₂_mul_le_right (signedLetter v a.1-signedLetter w a.1) a.2
      rw [signedLetter_sub,signedLetter_norm₂] at h2
      calc _ ≤ τ.norm₂ ((signedLetter v a.1-signedLetter w a.1)*a.2) :=
             h1.trans (mul_le_of_le_one_right (norm_nonneg _) (patchingWord_norm_le_one v hv xs htail))
           _ ≤ τ.norm₂ (v-w) := by
             rw [signedLetter_sub]
             exact h2.trans (mul_le_of_le_one_right (norm_nonneg _) ha)
    have hs : ‖signedLetter w a.1*a.2‖ ≤ 1 := by
      calc _ ≤ ‖signedLetter w a.1‖*‖a.2‖ := norm_mul_le _ _
           _ ≤ 1 := by rw [signedLetter_norm]; nlinarith [norm_nonneg w,norm_nonneg a.2]
    have hsecond : τ.norm₂ ((signedLetter w a.1*a.2)*(patchingWord v xs-patchingWord w xs)) ≤
        xs.length*τ.norm₂ (v-w) := by
      exact ((τ.norm₂_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hs)).trans (ih htail)
    rw [he]
    have hsum := τ.norm₂_add_le
      (((signedLetter v a.1-signedLetter w a.1)*a.2)*patchingWord v xs)
      ((signedLetter w a.1*a.2)*(patchingWord v xs-patchingWord w xs))
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

/-- Uniform trace continuity of every actual signed mixed word. -/
theorem mixed_trace_sub_le (τ : TracialRepresentation M)
    (v w x₀ : M.toStarSubalgebra) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (h₀ : ‖x₀‖ ≤ 1)
    (xs : List (Bool × M.toStarSubalgebra)) (hx : ∀ a ∈ xs, ‖a.2‖ ≤ 1) :
    ‖τ.trace (x₀*patchingWord v xs)-τ.trace (x₀*patchingWord w xs)‖ ≤
      xs.length*τ.norm₂ (v-w) := by
  rw [← trace_sub,← mul_sub]
  exact ((τ.norm_trace_le_norm₂ _).trans ((τ.norm₂_mul_le _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) h₀))).trans
    (patchingWord_norm₂_sub_le τ v w hv hw xs hx)

/-- Actual simultaneous control of signed one-patch terms, including arbitrary
ambient coefficients. This uses the constructed corner unitaries in P. -/
theorem exists_cornerUnitary_small_signed_traces (τ : TracialRepresentation M)
    {P : VonNeumannAlgebra H} (hPM : P ≤ M)
    (hdiffP : ∀ p : P.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : P.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : AlgebraProjection P) (hp : p.val ≠ 0) (F G : Finset M.toStarSubalgebra)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ v : CornerUnitary p, ∀ x ∈ F, ∀ y ∈ G, ∀ s : Bool,
      ‖τ.trace (x*signedLetter (coordinateInclusion hPM v.val) s*y)‖ < ε := by
  classical
  obtain ⟨v,hv⟩ := exists_cornerUnitary_small_mixed_traces τ hPM hdiffP p hp
    (F ∪ G.image star) (G ∪ F.image star) ε hε
  refine ⟨v,fun x hx y hy s => ?_⟩
  cases s
  · exact hv x (Finset.mem_union_left _ hx) y (Finset.mem_union_left _ hy)
  · have hh := hv (star y) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y,hy,rfl⟩))
      (star x) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩))
    have he : τ.trace (star (x*star (coordinateInclusion hPM v.val)*y)) =
        star (τ.trace (x*star (coordinateInclusion hPM v.val)*y)) := by
      let z := x*star (coordinateInclusion hPM v.val)*y
      change inner ℂ τ.vector (star (z : H →L[ℂ] H) τ.vector)=
        star (inner ℂ τ.vector ((z : H →L[ℂ] H) τ.vector))
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
      exact (inner_conj_symm _ _).symm
    simp only [star_mul,star_star,← mul_assoc] at he
    rw [he,norm_star] at hh
    exact hh

end

/-! The scalar-commutant specialization of the error-constrained chain and
Zorn step in Popa 1308.3982v3 Lemma 3.2. The internal coefficients are in F;
only the two endpoints may be 1. No local-quantization or growth assumption. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- The last coefficient is an endpoint; all earlier coefficients are internal. -/
def patchingCoefficients (F : Set M.toStarSubalgebra) : List (Bool × M.toStarSubalgebra) → Prop
  | [] => True
  | [a] => a.2 ∈ F ∪ {1}
  | a::b::xs => a.2 ∈ F ∧ patchingCoefficients F (b::xs)

theorem patchingCoefficients_norm (F : Set M.toStarSubalgebra)
    (hF : ∀ x ∈ F, ‖x‖ ≤ 1) (xs : List (Bool × M.toStarSubalgebra))
    (hx : patchingCoefficients F xs) : ∀ a ∈ xs, ‖a.2‖ ≤ 1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases xs with
    | nil =>
      have ha : ‖a.2‖ ≤ 1 := by
        rcases hx with h | h
        · exact hF _ h
        · rw [Set.mem_singleton_iff.mp h]; exact (IsStarProjection.one (M.toStarSubalgebra)).norm_le
      simpa using ha
    | cons b xs =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hF _ hx.1
      · exact ih hx.2 c hc

def PatchingAdmissible (f : AlgebraProjection M) (F : Set M.toStarSubalgebra)
    (n : ℕ) (ε : ℕ → ℝ) (v : PartialUnitary M) : Prop :=
  v.support ≤ f ∧ ∀ x₀ ∈ F ∪ {1}, ∀ xs : List (Bool × M.toStarSubalgebra),
    1 ≤ xs.length → xs.length ≤ n → patchingCoefficients F xs →
      ‖τ.trace (x₀*patchingWord v.val xs)‖ ≤ ε xs.length*(τ.trace v.support.val).re

theorem mixed_trace_limit (a : ℕ → PartialUnitary M) (v : PartialUnitary M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0))
    (x₀ : M.toStarSubalgebra) (h₀ : ‖x₀‖ ≤ 1)
    (xs : List (Bool × M.toStarSubalgebra)) (hx : ∀ a ∈ xs, ‖a.2‖ ≤ 1) :
    Tendsto (fun n => τ.trace (x₀*patchingWord (a n).val xs)) atTop
      (𝓝 (τ.trace (x₀*patchingWord v.val xs))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => mixed_trace_sub_le τ _ _ _ (a n).unitary.norm_le_one v.unitary.norm_le_one h₀ xs hx)
  simpa using hv.const_mul (xs.length : ℝ)

theorem patchingAdmissible_limit (f : AlgebraProjection M) (F : Set M.toStarSubalgebra)
    (hF : ∀ x ∈ F, ‖x‖ ≤ 1) (n : ℕ) (ε : ℕ → ℝ)
    (a : ℕ → PartialUnitary M) (v : PartialUnitary M)
    (ha : ∀ i, PatchingAdmissible τ f F n ε (a i))
    (hv : Tendsto (fun i => τ.norm₂ ((a i).val-v.val)) atTop (𝓝 0)) :
    PatchingAdmissible τ f F n ε v := by
  have hp := PartialUnitary.support_limit τ a v hv
  have hsupport : v.support ≤ f := by
    have ht := norm₂_limit_mul τ (fun _ => f.val) (fun i => (a i).support.val)
      f.val v.support.val 1 (fun _ => f.property.norm_le)
      (by simp only [sub_self,TracialRepresentation.norm₂_zero]; exact tendsto_const_nhds) hp
    have he : (fun i => f.val*(a i).support.val)=(fun i => (a i).support.val) :=
      funext (fun i => (ha i).1)
    simp only [show ∀ i, f.val*(a i).support.val=(a i).support.val from fun i => (ha i).1] at ht
    exact norm₂_limit_unique τ _ ht hp
  refine ⟨hsupport,fun x₀ hx₀ xs hlen hn hx => ?_⟩
  have h₀ : ‖x₀‖ ≤ 1 := by
    rcases hx₀ with h | h
    · exact hF _ h
    · rw [Set.mem_singleton_iff.mp h]; exact (IsStarProjection.one (M.toStarSubalgebra)).norm_le
  have ht := (mixed_trace_limit τ a v hv x₀ h₀ xs (patchingCoefficients_norm F hF xs hx)).norm
  have hr := (PartialUnitary.support_trace_limit τ a v hv).const_mul (ε xs.length)
  exact le_of_tendsto_of_tendsto ht hr (Eventually.of_forall (fun i => (ha i).2 x₀ hx₀ xs hlen hn hx))

def zeroPartialUnitary : PartialUnitary M :=
  ⟨⟨0,IsStarProjection.zero _⟩,⟨0,by simp,by simp⟩⟩

theorem patchingAdmissible_zero (f : AlgebraProjection M) (F : Set M.toStarSubalgebra)
    (n : ℕ) (ε : ℕ → ℝ) : PatchingAdmissible τ f F n ε zeroPartialUnitary := by
  constructor
  · change f.val*0=0; exact mul_zero _
  · intro x₀ hx₀ xs hlen hn hx
    cases xs with
    | nil => simp at hlen
    | cons a xs =>
      have hs : signedLetter (0 : M.toStarSubalgebra) a.1=0 := by
        cases a.1 <;> simp [signedLetter]
      change ‖τ.trace (x₀*(signedLetter 0 a.1*a.2*patchingWord 0 xs))‖ ≤
        ε (xs.length+1)*(τ.trace 0).re
      simp only [hs,zero_mul,mul_zero]
      have ht : τ.trace 0=0 := inner_zero_right _
      rw [ht,norm_zero,Complex.zero_re,mul_zero]

/-- A maximal element in the scalar mixed-word admissible set. -/
theorem exists_maximal_patchingAdmissible (f : AlgebraProjection M) (F : Set M.toStarSubalgebra)
    (hF : ∀ x ∈ F, ‖x‖ ≤ 1) (n : ℕ) (ε : ℕ → ℝ) :
    ∃ v : PartialUnitary M, PatchingAdmissible τ f F n ε v ∧
      ∀ w : PartialUnitary M, PatchingAdmissible τ f F n ε w → v ≤ w → w ≤ v := by
  obtain ⟨v,hv⟩ := zorn_le₀ {v | PatchingAdmissible τ f F n ε v} (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · obtain ⟨a,v,hac,ham,hav,hlim⟩ := PartialUnitary.chain_limit τ c hchain hne
      exact ⟨v,patchingAdmissible_limit τ f F hF n ε a v (fun i => hc (hac i)) hlim,hav⟩
    · exact ⟨zeroPartialUnitary,patchingAdmissible_zero τ f F n ε,
        fun w hw => (hne ⟨w,hw⟩).elim⟩)
  exact ⟨v,hv.1,fun w hw hvw => hv.2 hw hvw⟩

end

/-! The error-constrained partial unitaries stay in the prescribed algebra P,
while all word coefficients and the trace live in M. This prevents replacing
the source inclusion P subset M by the trivial inclusion M subset M. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M P : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hPM : P ≤ M)

include hPM
theorem inclusion_mem_of_bounded_L2_limit (a : ℕ → M.toStarSubalgebra) (b : M.toStarSubalgebra)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C)
    (hmem : ∀ n, (a n).val ∈ P)
    (hb : Tendsto (fun n => τ.norm₂ (a n-b)) atTop (𝓝 0)) : b.val ∈ P := by
  let aP : ℕ → P.toStarSubalgebra := fun n => ⟨(a n).val,hmem n⟩
  have ht := (tendsto_vector_iff_norm₂ τ atTop a b).mpr hb
  obtain ⟨c,hc,he⟩ := bounded_trace_limit (restrictedTrace τ hPM) aP C hC ha
    ((b : H →L[ℂ] H) τ.vector) ht
  have hcb : coordinateInclusion hPM c=b := by
    apply sub_eq_zero.mp
    apply τ.separating
    change (c : H →L[ℂ] H) τ.vector-(b : H →L[ℂ] H) τ.vector=0
    exact sub_eq_zero.mpr he
  have hv := congrArg Subtype.val hcb
  rw [← hv]
  exact c.property

def PatchingAdmissibleIn (f : AlgebraProjection M) (F : Set M.toStarSubalgebra)
    (n : ℕ) (ε : ℕ → ℝ) (v : PartialUnitary M) : Prop :=
  PatchingAdmissible τ f F n ε v ∧ v.val.val ∈ P

theorem patchingAdmissibleIn_limit (f : AlgebraProjection M) (F : Set M.toStarSubalgebra)
    (hF : ∀ x ∈ F, ‖x‖ ≤ 1) (n : ℕ) (ε : ℕ → ℝ)
    (a : ℕ → PartialUnitary M) (v : PartialUnitary M)
    (ha : ∀ i, PatchingAdmissibleIn (P := P) τ f F n ε (a i))
    (hv : Tendsto (fun i => τ.norm₂ ((a i).val-v.val)) atTop (𝓝 0)) :
    PatchingAdmissibleIn (P := P) τ f F n ε v := by
  exact ⟨patchingAdmissible_limit τ f F hF n ε a v (fun i => (ha i).1) hv,
    inclusion_mem_of_bounded_L2_limit τ hPM _ _ 1 (by norm_num)
      (fun i => (a i).unitary.norm_le_one) (fun i => (ha i).2) hv⟩

/-- The actual maximal admissible partial unitary lies in P, with mixed-word
errors measured in the ambient tracial algebra M. No support-growth bound. -/
theorem exists_maximal_patchingAdmissibleIn (f : AlgebraProjection M)
    (F : Set M.toStarSubalgebra) (hF : ∀ x ∈ F, ‖x‖ ≤ 1) (n : ℕ) (ε : ℕ → ℝ) :
    ∃ v : PartialUnitary M, PatchingAdmissibleIn (P := P) τ f F n ε v ∧
      ∀ w : PartialUnitary M, PatchingAdmissibleIn (P := P) τ f F n ε w → v ≤ w → w ≤ v := by
  obtain ⟨v,hv⟩ := zorn_le₀ {v | PatchingAdmissibleIn (P := P) τ f F n ε v} (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · obtain ⟨a,v,hac,ham,hav,hlim⟩ := PartialUnitary.chain_limit τ c hchain hne
      exact ⟨v,patchingAdmissibleIn_limit τ hPM f F hF n ε a v (fun i => hc (hac i)) hlim,hav⟩
    · refine ⟨zeroPartialUnitary,⟨patchingAdmissible_zero τ f F n ε,?_⟩,
        fun w hw => (hne ⟨w,hw⟩).elim⟩
      exact P.zero_mem)
  exact ⟨v,hv.1,fun w hw hvw => hv.2 hw hvw⟩

end

/-! Finite enumeration of the actual ordered word family. Only endpoints may
be 1. The middle segments retain all signs and their precise lengths. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- All lists of length at most n over a finite alphabet. -/
def boundedLists {α : Type*} (A : Finset α) : ℕ → Finset (List α)
  | 0 => {[]}
  | n+1 => by
    classical
    exact insert [] ((A ×ˢ boundedLists A n).image (fun z => z.1 :: z.2))

theorem mem_boundedLists {α : Type*} (A : Finset α) (n : ℕ) (xs : List α) :
    xs ∈ boundedLists A n ↔ xs.length ≤ n ∧ ∀ a ∈ xs, a ∈ A := by
  classical
  induction n generalizing xs with
  | zero => cases xs <;> simp [boundedLists]
  | succ n ih =>
    cases xs with
    | nil => simp [boundedLists]
    | cons a xs => simp [boundedLists, ih, List.length_cons, and_left_comm]

/-- A finite alphabet of signs and coefficients. -/
def signedAlphabet (F : Finset M.toStarSubalgebra) : Finset (Bool × M.toStarSubalgebra) :=
  Finset.univ ×ˢ F

@[simp] theorem mem_signedAlphabet (F : Finset M.toStarSubalgebra)
    (a : Bool × M.toStarSubalgebra) : a ∈ signedAlphabet F ↔ a.2 ∈ F := by
  simp [signedAlphabet]

/-- Every word admitted by the source definition, with its leading coefficient. -/
def admissibleWordFamily (F : Finset M.toStarSubalgebra) (n : ℕ) :
    Finset (M.toStarSubalgebra × List (Bool × M.toStarSubalgebra)) := by
  classical
  exact ((insert 1 F) ×ˢ boundedLists (signedAlphabet (insert 1 F)) n).filter
    (fun z => 1 ≤ z.2.length ∧ patchingCoefficients (F : Set M.toStarSubalgebra) z.2)

theorem patchingCoefficients_mem (F : Set M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) (hx : patchingCoefficients F xs) :
    ∀ a ∈ xs, a.2 ∈ F ∪ {1} := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases xs with
    | nil => simpa [patchingCoefficients, or_comm] using hx
    | cons b xs =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact Or.inl hx.1
      · exact ih hx.2 c hc

theorem mem_admissibleWordFamily (F : Finset M.toStarSubalgebra) (n : ℕ)
    (x : M.toStarSubalgebra) (xs : List (Bool × M.toStarSubalgebra)) :
    (x,xs) ∈ admissibleWordFamily F n ↔
      x ∈ (F : Set M.toStarSubalgebra) ∪ {1} ∧ 1 ≤ xs.length ∧ xs.length ≤ n ∧
        patchingCoefficients (F : Set M.toStarSubalgebra) xs := by
  classical
  simp only [admissibleWordFamily, Finset.mem_filter, Finset.mem_product,
    Finset.mem_insert, mem_boundedLists, mem_signedAlphabet]
  constructor
  · rintro ⟨⟨hx,hlen,ha⟩,hpos,hc⟩
    exact ⟨hx.symm,hpos,hlen,hc⟩
  · rintro ⟨hx,hpos,hlen,hc⟩
    refine ⟨⟨hx.symm,hlen,?_⟩,hpos,hc⟩
    intro a ha
    exact (patchingCoefficients_mem _ xs hc a ha).symm

/-- The uncompressed middle coefficient between the first two patch letters.
Every coefficient here is internal to the original word. -/
def middleWordFamily (F : Finset M.toStarSubalgebra) (n : ℕ) :
    Finset (M.toStarSubalgebra × List (Bool × M.toStarSubalgebra)) := by
  classical
  exact (F ×ˢ boundedLists (signedAlphabet F) n).filter (fun z => z.2.length+2 ≤ n)

theorem mem_middleWordFamily (F : Finset M.toStarSubalgebra) (n : ℕ)
    (x : M.toStarSubalgebra) (xs : List (Bool × M.toStarSubalgebra)) :
    (x,xs) ∈ middleWordFamily F n ↔
      x ∈ F ∧ xs.length+2 ≤ n ∧ ∀ a ∈ xs,a.2 ∈ F := by
  classical
  simp only [middleWordFamily,Finset.mem_filter,Finset.mem_product,
    mem_boundedLists,mem_signedAlphabet]
  constructor
  · rintro ⟨⟨hx,hlen,ha⟩,hb⟩; exact ⟨hx,hb,ha⟩
  · rintro ⟨hx,hb,ha⟩; exact ⟨⟨hx,by omega,ha⟩,hb⟩

/-- Actual fixed outer coefficients needed for one-patch terms. -/
def outerWordFamily (v : M.toStarSubalgebra) (F : Finset M.toStarSubalgebra) (n : ℕ) :
    Finset M.toStarSubalgebra := by
  classical
  exact ((insert 1 F) ×ˢ boundedLists (signedAlphabet (insert 1 F)) n).image
    (fun z => z.1*patchingWord v z.2)

theorem mem_outerWordFamily (v : M.toStarSubalgebra) (F : Finset M.toStarSubalgebra)
    (n : ℕ) (x : M.toStarSubalgebra) (xs : List (Bool × M.toStarSubalgebra))
    (hx : x ∈ (F : Set M.toStarSubalgebra) ∪ {1}) (hlen : xs.length ≤ n)
    (ha : ∀ a ∈ xs,a.2 ∈ (F : Set M.toStarSubalgebra) ∪ {1}) :
    x*patchingWord v xs ∈ outerWordFamily v F n := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨(x,xs),Finset.mem_product.mpr ⟨by simpa using hx.symm,?_⟩,rfl⟩
  exact (mem_boundedLists _ _ _).mpr ⟨hlen,fun a h => by
    simpa using (ha a h).symm⟩

end

/-! The two moment bounds in Popa Lemma 3.2 equation (6), derived from
admissibility for the actual signed internal segment, including length zero. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem patchingCoefficients_of_internal (F : Set M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) (hx : ∀ a ∈ xs,a.2 ∈ F) :
    patchingCoefficients F xs := by
  induction xs with
  | nil => trivial
  | cons a xs ih =>
    cases xs with
    | nil => exact Or.inl (hx a (by simp))
    | cons b xs =>
      exact ⟨hx a (by simp),ih (fun c hc => hx c (by simp [hc]))⟩

theorem patchingCoefficients_append_endpoint (F : Set M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) (hx : ∀ a ∈ xs,a.2 ∈ F)
    (a : Bool × M.toStarSubalgebra) (ha : a.2 ∈ F ∪ {1}) :
    patchingCoefficients F (xs ++ [a]) := by
  induction xs with
  | nil => exact ha
  | cons b xs ih =>
    have ht := ih (fun c hc => hx c (by simp [hc]))
    cases xs with
    | nil => exact ⟨hx b (by simp),ht⟩
    | cons c xs => exact ⟨hx b (by simp),ht⟩

theorem patchingWord_append (v : M.toStarSubalgebra)
    (xs ys : List (Bool × M.toStarSubalgebra)) :
    patchingWord v (xs++ys)=patchingWord v xs*patchingWord v ys := by
  induction xs with
  | nil => simp [patchingWord]
  | cons a xs ih => simp [patchingWord,ih,mul_assoc]

/-- A_i is zero for an empty middle segment, since its sole coefficient is centered. -/
def middleMomentError (ε : ℕ → ℝ) (r : ℕ) : ℝ := if r=0 then 0 else ε r

theorem admissible_middle_trace (v : PartialUnitary M) (f : AlgebraProjection M)
    (F : Set M.toStarSubalgebra) (n : ℕ) (ε : ℕ → ℝ)
    (hv : PatchingAdmissible τ f F n ε v) (hcenter : ∀ x ∈ F,τ.trace x=0)
    (x : M.toStarSubalgebra) (xs : List (Bool × M.toStarSubalgebra))
    (hx : x ∈ F) (hxs : ∀ a ∈ xs,a.2 ∈ F) (hlen : xs.length ≤ n) :
    ‖τ.trace (x*patchingWord v.val xs)‖ ≤
      middleMomentError ε xs.length*(τ.trace v.support.val).re := by
  cases xs with
  | nil => simp [patchingWord,middleMomentError,hcenter x hx]
  | cons a xs =>
    exact hv.2 x (Or.inl hx) (a::xs) (by simp) hlen
      (patchingCoefficients_of_internal F _ hxs)

/-- Appending a positive v and prepending v* gives an admitted word of length r+2.
The two new endpoint coefficients are exactly 1. -/
theorem admissible_middle_second_trace (v : PartialUnitary M) (f : AlgebraProjection M)
    (F : Set M.toStarSubalgebra) (n : ℕ) (ε : ℕ → ℝ)
    (hv : PatchingAdmissible τ f F n ε v)
    (x : M.toStarSubalgebra) (xs : List (Bool × M.toStarSubalgebra))
    (hx : x ∈ F) (hxs : ∀ a ∈ xs,a.2 ∈ F) (hlen : xs.length+2 ≤ n) :
    ‖τ.trace (star v.val*(x*patchingWord v.val xs)*v.val)‖ ≤
      ε (xs.length+2)*(τ.trace v.support.val).re := by
  let ys : List (Bool × M.toStarSubalgebra) := (true,x)::(xs++[(false,1)])
  have hi : ∀ a ∈ (true,x)::xs,a.2 ∈ F := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hx
    · exact hxs a ha
  have hc : patchingCoefficients F ys :=
    patchingCoefficients_append_endpoint F ((true,x)::xs) hi (false,1) (Or.inr rfl)
  have hy : ys.length=xs.length+2 := by simp [ys]
  have hh := hv.2 1 (Or.inr rfl) ys (by rw [hy]; omega) (by rw [hy]; exact hlen) hc
  rw [hy] at hh
  simpa only [ys,patchingWord,patchingWord_append,signedLetter, Bool.false_eq_true,
    ↓reduceIte, mul_one,one_mul,mul_assoc] using hh

theorem middleWordFamily_moments (v : PartialUnitary M) (f : AlgebraProjection M)
    (F : Finset M.toStarSubalgebra) (n : ℕ) (ε : ℕ → ℝ)
    (hv : PatchingAdmissible τ f (F : Set M.toStarSubalgebra) n ε v)
    (hcenter : ∀ x ∈ F,τ.trace x=0)
    (i : M.toStarSubalgebra × List (Bool × M.toStarSubalgebra))
    (hi : i ∈ middleWordFamily F n) :
    ‖τ.trace (i.1*patchingWord v.val i.2)‖ ≤
        middleMomentError ε i.2.length*(τ.trace v.support.val).re ∧
      ‖τ.trace (star v.val*(i.1*patchingWord v.val i.2)*v.val)‖ ≤
        ε (i.2.length+2)*(τ.trace v.support.val).re := by
  obtain ⟨hx,hlen,hxs⟩ := (mem_middleWordFamily F n i.1 i.2).mp hi
  exact ⟨admissible_middle_trace τ v f F n ε hv hcenter i.1 i.2 hx hxs (by omega),
    admissible_middle_second_trace τ v f F n ε hv i.1 i.2 hx hxs hlen⟩

end

/-! Actual noncommutative binary expansion in Popa Lemma 3.2, equation (1).
Each list entry retains the number of patch letters used and its ordered
operator product. There is no commuting-coefficient hypothesis. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def patchingExpansion (v w : M.toStarSubalgebra) :
    List (Bool × M.toStarSubalgebra) → List (ℕ × M.toStarSubalgebra)
  | [] => [(0,1)]
  | (s,x)::xs =>
      (patchingExpansion v w xs).map (fun z => (z.1,signedLetter v s*x*z.2)) ++
      (patchingExpansion v w xs).map (fun z => (z.1+1,signedLetter w s*x*z.2))

theorem sum_map_left_mul (a : M.toStarSubalgebra) (xs : List M.toStarSubalgebra) :
    (xs.map (fun x => a*x)).sum=a*xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,mul_add]

theorem signedLetter_add (v w : M.toStarSubalgebra) (s : Bool) :
    signedLetter (v+w) s=signedLetter v s+signedLetter w s := by
  cases s <;> simp [signedLetter,star_add]

theorem patchingExpansion_sum (v w : M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) :
    ((patchingExpansion v w xs).map Prod.snd).sum=patchingWord (v+w) xs := by
  induction xs with
  | nil => simp [patchingExpansion,patchingWord]
  | cons a xs ih =>
    simp only [patchingExpansion,List.map_append,List.sum_append,List.map_map,Function.comp_def]
    have hv : ((patchingExpansion v w xs).map (fun z => signedLetter v a.1*a.2*z.2)).sum =
        (signedLetter v a.1*a.2)*((patchingExpansion v w xs).map Prod.snd).sum := by
      simpa only [List.map_map,Function.comp_def] using
        sum_map_left_mul (signedLetter v a.1*a.2) ((patchingExpansion v w xs).map Prod.snd)
    have hw : ((patchingExpansion v w xs).map (fun z => signedLetter w a.1*a.2*z.2)).sum =
        (signedLetter w a.1*a.2)*((patchingExpansion v w xs).map Prod.snd).sum := by
      simpa only [List.map_map,Function.comp_def] using
        sum_map_left_mul (signedLetter w a.1*a.2) ((patchingExpansion v w xs).map Prod.snd)
    rw [hv,hw,ih]
    simp only [patchingWord,signedLetter_add,add_mul]

theorem patchingExpansion_length (v w : M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) :
    (patchingExpansion v w xs).length=2^xs.length := by
  induction xs with
  | nil => simp [patchingExpansion]
  | cons a xs ih => simp [patchingExpansion,ih,pow_succ]; omega

theorem patchingExpansion_degree_le (v w : M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) :
    ∀ z ∈ patchingExpansion v w xs, z.1 ≤ xs.length := by
  induction xs with
  | nil => simp [patchingExpansion]
  | cons a xs ih =>
    intro z hz
    rcases List.mem_append.mp hz with h | h
    · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp h
      have he := ih y hy
      simpa using he.trans (Nat.le_succ _)
    · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp h
      exact Nat.succ_le_succ (ih y hy)

/-- The unique term containing no patch letters is exactly the original word. -/
theorem patchingExpansion_zero_filter (v w : M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) :
    (patchingExpansion v w xs).filter (fun z => z.1==0)=[(0,patchingWord v xs)] := by
  induction xs with
  | nil => simp [patchingExpansion,patchingWord]
  | cons a xs ih =>
    simp only [patchingExpansion,List.filter_append,List.filter_map]
    simp only [Function.comp_def]
    simp [patchingWord,ih]

end Generator.Tracial

end

end OAI
