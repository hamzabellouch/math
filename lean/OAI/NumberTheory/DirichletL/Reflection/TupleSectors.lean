import OAI.NumberTheory.DirichletL.Reflection.TupleFamily
import OAI.NumberTheory.DirichletL.Reflection.SourceSectors

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ]

lemma tuplePrimeFamily_pairwise (L : σ→Finset (Ideal Eis))
    (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hT : ∀ p∈tuples, ∀ i, p i∈L i)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, λ₀∉p i) (P : Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (tuplePrimeFamily tuples hne hmax hgood P).ideal) := by
  intro i j hij
  apply Ideal.isCoprime_of_isMaximal
  intro he
  have hp := tupleRepresentative_mem tuples hne P
  change tupleRepresentative tuples hne P i=tupleRepresentative tuples hne P j at he
  exact Finset.disjoint_left.mp (hL hij) (hT _ hp i) (he.symm ▸ hT _ hp j)

omit [Fintype φ] in
lemma tuplePrimeFamily_sum_pairwise (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (L : σ→Finset (Ideal Eis)) (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hT : ∀ p∈tuples, ∀ i, p i∈L i)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, λ₀∉p i)
    (hfixed : ∀ p∈tuples, ∀ f i, p i≠F.ideal f) (P : Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (F.sum (tuplePrimeFamily tuples hne hmax hgood P)).ideal) := by
  intro i j hij
  cases i with
  | inl f => cases j with
    | inl g => exact hF (fun h => hij (congrArg Sum.inl h))
    | inr t =>
      apply Ideal.isCoprime_of_isMaximal
      exact (hfixed _ (tupleRepresentative_mem tuples hne P) f t).symm
  | inr t => cases j with
    | inl f =>
      apply Ideal.isCoprime_of_isMaximal
      exact hfixed _ (tupleRepresentative_mem tuples hne P) f t
    | inr u => exact tuplePrimeFamily_pairwise L hL tuples hne hT hmax hgood P (fun h => hij (congrArg Sum.inr h))

theorem exists_tuple_sector_arithmetic (F : PrimeFamily φ)
    (L : σ→Finset (Ideal Eis)) (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hT : ∀ p∈tuples, ∀ i, p i∈L i)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, λ₀∉p i)
    (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows, Admissible K)
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c≠0) (hN : (9:Eis)*c∣N)
    (hbase : if mode then λ₀^2∣a-1 else λ₀^2∣c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hrowcop : ∀ K∈rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K)
    (hfixed : ∀ p∈tuples, ∀ f i, p i≠F.ideal f)
    (hperiod : ∀ p∈tuples, ∀ i, IsCoprime (Ideal.span {N}) (p i))
    (rowClass slotClass : Eis⧸Ideal.span {N^2})
    (hrowClass : ∀ K∈rows, Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)=rowClass)
    (hslotClass : ∀ p∈tuples, Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator (slotTupleProduct p))=slotClass) :
    ∃ E : ∀ x : SourcePair rows (tuples.image slotTupleProduct),
      ControlledStratumArithmetic
        (F.reflected x.val.1.val (hrows x.val.1.val x.val.1.property)
          (tuplePrimeFamily tuples hne hmax hgood x.val.2.val)).generator N a c mode,
      ∀ x0 x, (E x).fixedFactor=(E x0).fixedFactor ∧
        ∀ u m n b, actualCuspColumn (E x) s hc u m n b=actualCuspColumn (E x0) s hc u m n b := by
  refine exists_fixed_ray_source_arithmetic F rows (tuples.image slotTupleProduct)
    (tuplePrimeFamily tuples hne hmax hgood) hrows
    (tuplePrimeFamily_product tuples hne hmax hgood) N a c mode s hc hN hbase hac hF hNF hrowcop ?_ ?_ rowClass slotClass hrowClass ?_
  · intro P hP
    exact tuplePrimeFamily_sum_pairwise F hF L hL tuples hne hT hmax hgood hfixed P
  · intro P hP i
    exact hperiod _ (tupleRepresentative_mem tuples hne P) i
  · intro P hP
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hP
    exact hslotClass p hp
end
end SevenEighths.InverseReflectedPhase

end OAI
