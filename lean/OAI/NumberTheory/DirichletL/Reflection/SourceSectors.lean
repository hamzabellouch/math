import OAI.NumberTheory.DirichletL.Reflection.SourceFamily

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

variable {φ σ : Type*} [Fintype φ] [Fintype σ]

theorem exists_fixed_ray_source_arithmetic (F : PrimeFamily φ)
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
    (hSN : ∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((S P).ideal i))
    (rowClass slotClass : Eis ⧸ Ideal.span {N^2})
    (hrowClass : ∀ K ∈ rows, Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)=rowClass)
    (hslotClass : ∀ P ∈ Pset, Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator P)=slotClass) :
    ∃ E : ∀ x : SourcePair rows Pset,
      ControlledStratumArithmetic
        (F.reflected x.val.1.val (hrows x.val.1.val x.val.1.property) (S x.val.2.val)).generator N a c mode,
      ∀ x0 x, (E x).fixedFactor = (E x0).fixedFactor ∧
        ∀ u m n b, actualCuspColumn (E x) s hc u m n b = actualCuspColumn (E x0) s hc u m n b := by
  obtain ⟨E,κ,A,_,_,hκ,hA⟩ := exists_source_pair_templates F rows Pset S hrows hprod
    N a c mode s hc hN hbase hac hF hNF hrowcop hScop hSN
  refine ⟨E,?_⟩
  intro x0 x
  have he (y : SourcePair rows Pset) :
      separateSector N (primaryGenerator y.val.1.val) (primaryGenerator y.val.2.val) = (rowClass,slotClass) := by
    exact Prod.ext (hrowClass _ y.val.1.property) (hslotClass _ y.val.2.property)
  constructor
  · rw [hκ x,hκ x0,he x,he x0]
  · intro u m n b
    rw [hA x u m n b,hA x0 u m n b,he x,he x0]

end
end SevenEighths.InverseReflectedPhase

end OAI
