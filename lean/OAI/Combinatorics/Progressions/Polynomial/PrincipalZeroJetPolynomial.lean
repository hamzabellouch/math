import OAI.Combinatorics.Progressions.Sampling.PrincipalZeroRationalForecast

namespace OAI

section

namespace Erdos3
open scoped BigOperators Matrix Classical

variable {Z X K α O N : Type*} [DecidableEq α] [Fintype N]

noncomputable def integerMappedVertexPolynomial
    (input : K → Option α → Z ⊕ X) (t : Finset α) (k : K) :
    MvPolynomial ((N ⊕ X) ⊕ Z) ℤ :=
  let slot : Z ⊕ X → (N ⊕ X) ⊕ Z := Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)
  MvPolynomial.X (slot (input k none)) +
    ∑ i ∈ t, MvPolynomial.X (slot (input k (some i)))

noncomputable def integerMappedJetOutputPolynomial
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X)
    (rows : O → Finset α) (o : O) : MvPolynomial ((N ⊕ X) ⊕ Z) ℤ :=
  booleanCoefficient (fun t => ∑ n,
    MvPolynomial.X (Sum.inl (Sum.inl n)) *
      (e n).prod (fun k d => integerMappedVertexPolynomial input t k ^ d)) (rows o)

omit [DecidableEq α] [Fintype N] in
theorem integerMappedVertexPolynomial_eval
    (input : K → Option α → Z ⊕ X) (c : N → ℤ) (z : Z → ℤ) (x : X → ℤ)
    (t : Finset α) (k : K) :
    MvPolynomial.eval (Sum.elim (Sum.elim c x) z)
      (integerMappedVertexPolynomial input t k) = integerMappedCubeTuple input z x t k := by
  have hslot (s : Z ⊕ X) :
      Sum.elim (Sum.elim c x) z ((Sum.elim Sum.inr (Sum.inl ∘ Sum.inr) : Z ⊕ X → (N ⊕ X) ⊕ Z) s) =
        Sum.elim z x s := by cases s <;> rfl
  simp only [integerMappedVertexPolynomial, map_add, map_sum, MvPolynomial.eval_X,
    hslot, integerMappedCubeTuple, integerAffineCube]

theorem integerMappedJetOutputPolynomial_eval
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X)
    (rows : O → Finset α) (c : N → ℤ) (z : Z → ℤ) (x : X → ℤ) (o : O) :
    MvPolynomial.eval (Sum.elim (Sum.elim c x) z)
      (integerMappedJetOutputPolynomial e input rows o) =
        (integerMappedJetMatrix e input z rows x *ᵥ c) o := by
  rw [integerMappedJetMatrix, integerJetMatrix_apply_coefficients]
  simp only [integerMappedJetOutputPolynomial, booleanCoefficient_map, map_sum, map_mul,
    MvPolynomial.eval_X, Sum.elim_inl, map_prod, map_pow, Finsupp.prod,
    integerMappedVertexPolynomial_eval, MvPolynomial.eval_C,
    MvPolynomial.eval_monomial, one_mul]

noncomputable def integerMappedLongJetOutputPolynomial
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X)
    (rows : O → Finset α) (o : O) : MvPolynomial (X ⊕ (N ⊕ Z)) ℤ :=
  MvPolynomial.rename (Sum.elim (Sum.elim (Sum.inr ∘ Sum.inl) Sum.inl) (Sum.inr ∘ Sum.inr))
    (integerMappedJetOutputPolynomial e input rows o)

theorem integerMappedLongJetOutputPolynomial_eval
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X)
    (rows : O → Finset α) (c : N → ℤ) (z : Z → ℤ) (x : X → ℤ) (o : O) :
    MvPolynomial.eval (Sum.elim x (Sum.elim c z))
      (integerMappedLongJetOutputPolynomial e input rows o) =
        (integerMappedJetMatrix e input z rows x *ᵥ c) o := by
  rw [integerMappedLongJetOutputPolynomial, MvPolynomial.eval_rename]
  have hcoord : Sum.elim x (Sum.elim c z) ∘
      Sum.elim (Sum.elim (Sum.inr ∘ Sum.inl) Sum.inl) (Sum.inr ∘ Sum.inr) =
        Sum.elim (Sum.elim c x) z := by
    funext v
    rcases v with (n | i) | j <;> rfl
  rw [hcoord]
  exact integerMappedJetOutputPolynomial_eval e input rows c z x o

end Erdos3

end

section

namespace Erdos3
open scoped Classical Matrix BigOperators

variable {D K Z O N α : Type*} {B : D → Type*} {h : D → ℕ}
variable [Fintype N] [DecidableEq α]

noncomputable def principalZeroJetOutputPolynomial
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (rows : O → Finset α) (o : O) :
    MvPolynomial (PrincipalTupleIndex B h ⊕ (N ⊕ Z)) ℤ :=
  MvPolynomial.rename
    (Sum.map (fun a : JointBlockParameter B h α => (⟨a.1,a.2.1,a.2.2.1⟩ : PrincipalTupleIndex B h)) id)
    (integerMappedLongJetOutputPolynomial e input rows o)

theorem principalZeroJetOutputPolynomial_eval [IsEmpty α]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (rows : O → Finset α) (c : N → ℤ) (z : Z → ℤ)
    {L : PrincipalTupleIndex B h → ℕ} (y : PrincipalIntegerTuples B h α L) (o : O) :
    MvPolynomial.eval (Sum.elim (fun a => (y a none : ℤ)) (Sum.elim c z))
      (principalZeroJetOutputPolynomial e input rows o) =
        (integerMappedJetMatrix e input z rows (principalTupleIntegers y) *ᵥ c) o := by
  rw [principalZeroJetOutputPolynomial, MvPolynomial.eval_rename]
  have hv : Sum.elim (fun a => (y a none : ℤ)) (Sum.elim c z) ∘
      Sum.map (fun a : JointBlockParameter B h α => (⟨a.1,a.2.1,a.2.2.1⟩ : PrincipalTupleIndex B h)) id =
        Sum.elim (principalTupleIntegers y) (Sum.elim c z) := by
    funext v
    cases v with
    | inl a =>
      have ha : a.2.2.2 = none := Subsingleton.elim _ _
      simp only [Function.comp_apply, Sum.map_inl, Sum.elim_inl, principalTupleIntegers, ha]
    | inr a => rfl
  rw [hv]
  exact integerMappedLongJetOutputPolynomial_eval e input rows c z (principalTupleIntegers y) o

theorem principalZeroJet_rationalInactiveForecast_error
    [Fintype D] [DecidableEq D] [Fintype α] [IsEmpty α]
    [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] [Fintype O] [DecidableEq O]
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    {Ω T : Type*} [Fintype Ω] [Fintype T]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → T)
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (rows : O → Finset α) (coefficient : Ω → N → ℤ) (fixed : Ω → Z → ℤ)
    {q M : ℕ} [NeZero q] [NeZero M] (hq : q ∣ M)
    {gridVolume : ℝ} (hvol : gridVolume ≠ 0)
    (test : T → (O → ZMod q) → ℂ) (htest : ∀ t r, ‖test t r‖ ≤ 1)
    (hsmall : (∑ j, (q : ℝ) / (L j : ℝ)) ≤ 1 / 2) :
    ‖inactive.complexMean (fun i =>
      (principalTupleWeights (α := α) B h L hL).complexMean
        (fun y => test (gridPoint i) (fun o =>
          ((integerMappedJetMatrix e input (fixed i) rows (principalTupleIntegers y) *ᵥ
            coefficient i) o : ZMod q)))) -
      (∑ t, 𝔼 b : O → ZMod M,
        ((rationalInactiveForecast inactive
          (fun _ => FiniteProbabilityWeights.uniform (PrincipalTupleIndex B h → ZMod M))
          gridPoint (fun i => integerLongPolynomialOutput
            (principalZeroJetOutputPolynomial e input rows)
            (Sum.elim (coefficient i) (fixed i)) M)
          M gridVolume t b / gridVolume : ℝ) : ℂ) *
            test t (fun o => ZMod.castHom hq (ZMod q) (b o)))‖ ≤
      2 * ∑ j, (q : ℝ) / (L j : ℝ) := by
  have he := principalTupleWeights_zero_rationalInactiveForecast_error (α := α) B h L hL
    inactive gridPoint (principalZeroJetOutputPolynomial e input rows)
    (fun i => Sum.elim (coefficient i) (fixed i)) hq hvol test htest hsmall
  simpa only [principalZeroJetOutputPolynomial_eval] using he

end Erdos3

end

end OAI
