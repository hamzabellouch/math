import OAI.NumberTheory.DirichletL.Reflection.Rows

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def reflectedExponent {φ ρ σ : Type*} (jF : φ → ℕ) : φ ⊕ (ρ ⊕ σ) → ℕ :=
  Sum.elim jF (Sum.elim (fun _ => 1) (fun _ => 0))

def frozenIndices (φ ρ σ : Type*) [Fintype φ] : Finset (φ ⊕ (ρ ⊕ σ)) :=
  @Finset.image φ (φ ⊕ (ρ ⊕ σ)) (Classical.decEq _) Sum.inl Finset.univ

def residualIndices (φ ρ σ : Type*) [Fintype ρ] : Finset (φ ⊕ (ρ ⊕ σ)) :=
  @Finset.image ρ (φ ⊕ (ρ ⊕ σ)) (Classical.decEq _) (Sum.inr ∘ Sum.inl) Finset.univ

def slotIndices (φ ρ σ : Type*) [Fintype σ] : Finset (φ ⊕ (ρ ⊕ σ)) :=
  @Finset.image σ (φ ⊕ (ρ ⊕ σ)) (Classical.decEq _) (Sum.inr ∘ Sum.inr) Finset.univ

lemma reflected_indices_partition (φ ρ σ : Type*) [Fintype φ] [Fintype ρ] [Fintype σ] :
    Disjoint (residualIndices φ ρ σ) (slotIndices φ ρ σ) ∧
    Disjoint (residualIndices φ ρ σ ∪ slotIndices φ ρ σ) (frozenIndices φ ρ σ) ∧
    (residualIndices φ ρ σ ∪ slotIndices φ ρ σ) ∪ frozenIndices φ ρ σ = Finset.univ := by
  classical
  simp only [residualIndices, slotIndices, frozenIndices, Finset.disjoint_left,
    Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Function.comp_apply]
  constructor
  · rintro i ⟨r, rfl⟩ ⟨s, h⟩
    cases h
  constructor
  · rintro i (⟨r, rfl⟩ | ⟨s, rfl⟩) ⟨f, h⟩ <;> cases h
  · ext i
    cases i with
    | inl f => simp
    | inr i => cases i with
      | inl r => simp
      | inr s => simp

lemma reflected_residual_exponent {φ ρ σ : Type*} [Fintype ρ] (jF : φ → ℕ) :
    ∀ i ∈ residualIndices φ ρ σ, reflectedExponent jF i = 1 := by
  let : DecidableEq (φ ⊕ (ρ ⊕ σ)) := Classical.decEq _
  rintro i hi
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
  rfl

namespace PrimeFamily
lemma reflected_residual_product {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) :
    (∏ i ∈ residualIndices φ (PrimeIndex K) σ,
      Ideal.span {(F.reflected K hK S).generator i}) = K := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  simp only [generator_span, residualIndices]
  rw [Finset.prod_image (Sum.inr_injective.comp Sum.inl_injective).injOn]
  exact residual_product K hK

lemma reflected_slot_product {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) :
    (∏ i ∈ slotIndices φ (PrimeIndex K) σ,
      Ideal.span {(F.reflected K hK S).generator i}) = ∏ i, S.ideal i := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  simp only [generator_span, slotIndices]
  rw [Finset.prod_image (Sum.inr_injective.comp Sum.inr_injective).injOn]
  rfl
end PrimeFamily

theorem moving_common_reflected_coefficients {α φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : α → Ideal Eis) (hK : ∀ x, Admissible (K x))
    (S : α → PrimeFamily σ) (jF : φ → ℕ)
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2 ∣ a-1
      else ConcretePrimeRowBridge.goodLambda^2 ∣ c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hS : ∀ x, Pairwise (Function.onFun IsCoprime (S x).ideal))
    (hKS : ∀ x, IsCoprime (K x) (∏ i, (S x).ideal i))
    (hFK : ∀ x f, IsCoprime (F.ideal f) (K x))
    (hFS : ∀ x f i, IsCoprime (F.ideal f) ((S x).ideal i))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hNK : ∀ x, IsCoprime (Ideal.span {N}) (K x))
    (hNS : ∀ x i, IsCoprime (Ideal.span {N}) ((S x).ideal i)) :
    ∃ E : ∀ x, ControlledStratumArithmetic (F.reflected (K x) (hK x) (S x)).generator N a c mode,
      ∃ (γ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → Eisˣ → ℕ → ℂ)
        (β : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ x u m, sourceFrozenPhase (E x) s
          (F.reflected (K x) (hK x) (S x)).generator_ne_zero
          (F.reflected (K x) (hK x) (S x)).generator_good
          (reflectedExponent jF) (frozenIndices φ (PrimeIndex (K x)) σ) u m =
          γ (separateSector N (primaryGenerator (K x))
            (primaryGenerator (∏ i, (S x).ideal i))) u m) ∧
        ∀ x u m n b, sourceColumn (E x) s hc
          (F.reflected (K x) (hK x) (S x)).generator_good
          (reflectedExponent jF) (frozenIndices φ (PrimeIndex (K x)) σ) u m n b =
          β (separateSector N (primaryGenerator (K x))
            (primaryGenerator (∏ i, (S x).ideal i))) u m n b := by
  classical
  simpa only [frozenIndices] using canonical_common_reflected_coefficients
    (fun x => F.reflected (K x) (hK x) (S x)) N a c mode s hc hN hbase hac
    (fun x => F.reflected_pairwise (K x) (hK x) (S x) hF (hS x) (hKS x) (hFK x) (hFS x))
    (fun x => F.reflected_period (K x) (hK x) (S x) N hNF (hNK x) (hNS x))
    (fun _ => reflectedExponent jF) (fun _ => Sum.inl) (fun _ => Sum.inl_injective)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) Finset.univ (∏ i, F.ideal i) K
    (fun x => ∏ i, (S x).ideal i) (fun x => F.reflected_product (K x) (hK x) (S x))

end
end SevenEighths.InverseReflectedPhase

end OAI
