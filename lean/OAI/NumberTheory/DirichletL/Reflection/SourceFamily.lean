import OAI.NumberTheory.DirichletL.Reflection.ActualExtractedEnergy

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def SourcePair (rows Pset : Finset (Ideal Eis)) :=
  {x : rows × Pset // IsCoprime x.1.val x.2.val}

variable {φ σ : Type*} [Fintype φ] [Fintype σ]

theorem exists_source_pair_templates (F : PrimeFamily φ)
    (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis → PrimeFamily σ)
    (hrows : ∀ K ∈ rows, Admissible K)
    (hprod : ∀ P ∈ Pset, (∏ i, (S P).ideal i)=P)
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hrowcop : ∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K)
    (hScop : ∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal))
    (hSN : ∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((S P).ideal i)) :
    ∃ E : ∀ x : SourcePair rows Pset,
      ControlledStratumArithmetic
        (F.reflected x.val.1.val (hrows x.val.1.val x.val.1.property) (S x.val.2.val)).generator N a c mode,
      ∃ (κ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → ℂ)
        (A : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ q, ‖κ q‖ ≤ 1) ∧ (∀ q u m n b, ‖A q u m n b‖ ≤ 1) ∧
        (∀ x, (E x).fixedFactor = κ (separateSector N (primaryGenerator x.val.1.val)
          (primaryGenerator x.val.2.val))) ∧
        ∀ x u m n b, actualCuspColumn (E x) s hc u m n b =
          A (separateSector N (primaryGenerator x.val.1.val) (primaryGenerator x.val.2.val)) u m n b := by
  let G := fun x : SourcePair rows Pset =>
    F.reflected x.val.1.val (hrows x.val.1.val x.val.1.property) (S x.val.2.val)
  have hpair (x : SourcePair rows Pset) : Pairwise (Function.onFun IsCoprime (G x).ideal) := by
    apply F.reflected_pairwise x.val.1.val (hrows x.val.1.val x.val.1.property) (S x.val.2.val) hF
    · intro i k hik
      change IsCoprime ((F.sum (S x.val.2.val)).ideal (Sum.inr i))
        ((F.sum (S x.val.2.val)).ideal (Sum.inr k))
      exact hScop x.val.2.val x.val.2.property (Sum.inr_injective.ne hik)
    · rw [hprod _ x.val.2.property]
      exact x.property
    · exact (hrowcop _ x.val.1.property).1
    · intro f i
      change IsCoprime ((F.sum (S x.val.2.val)).ideal (Sum.inl f))
        ((F.sum (S x.val.2.val)).ideal (Sum.inr i))
      exact hScop x.val.2.val x.val.2.property (Sum.inl_ne_inr : (Sum.inl f : φ ⊕ σ) ≠ Sum.inr i)
  have hNp (x : SourcePair rows Pset) : ∀ i, IsCoprime (Ideal.span {N}) ((G x).ideal i) :=
    F.reflected_period _ _ _ N hNF (hrowcop _ x.val.1.property).2 (hSN _ x.val.2.property)
  apply canonical_bounded_cusp_templates G N a c mode s hc hN hbase hac hpair hNp
    (∏ i, F.ideal i) (fun x => x.val.1.val) (fun x => x.val.2.val)
  intro x
  rw [PrimeFamily.reflected_product,hprod _ x.val.2.property]

theorem source_templates_equal_to_representative {α : Type*} {ι : α → Type*}
    [∀ x, Fintype (ι x)] (G : ∀ x, PrimeFamily (ι x))
    {N a c : Eis} {mode : Bool}
    (E : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    {Q : Type*} (q : α → Q) (κ : Q → ℂ) (A : Q → Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ)
    (hκ : ∀ x, (E x).fixedFactor = κ (q x))
    (hA : ∀ x u m n b, actualCuspColumn (E x) s hc u m n b = A (q x) u m n b)
    (x0 x : α) (hq : q x = q x0) :
    (E x).fixedFactor = (E x0).fixedFactor ∧
      ∀ u m n b, actualCuspColumn (E x) s hc u m n b = actualCuspColumn (E x0) s hc u m n b := by
  constructor
  · rw [hκ x,hκ x0,hq]
  · intro u m n b
    rw [hA x u m n b,hA x0 u m n b,hq]

end
end SevenEighths.InverseReflectedPhase

end OAI
