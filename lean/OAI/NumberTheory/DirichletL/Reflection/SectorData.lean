import OAI.NumberTheory.DirichletL.Reflection.SourceSectors

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

structure SectorArithmetic (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows, Admissible K)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0) where
  referenceIndex : Type (max u v)
  [referenceFintype : Fintype referenceIndex]
  referencePrimes : PrimeFamily referenceIndex
  referenceArithmetic : ControlledStratumArithmetic referencePrimes.generator N a c mode
  completion : ∀ K : rows, ∀ P : Pset, IsCoprime K.val P.val →
    ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode
  fixedFactor_eq : ∀ K P hp, (completion K P hp).fixedFactor=referenceArithmetic.fixedFactor
  cuspColumn_eq : ∀ K P hp u m n b,
    actualCuspColumn (completion K P hp) s hc u m n b=actualCuspColumn referenceArithmetic s hc u m n b

attribute [instance] SectorArithmetic.referenceFintype

theorem exists_sector_arithmetic (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows, Admissible K)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hac : IsCoprime a c) (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hrowcop : ∀ K∈rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K)
    (hprod : ∀ P∈Pset, (∏ i,(S P).ideal i)=P)
    (hScop : ∀ P∈Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal))
    (hSN : ∀ P∈Pset, ∀ i, IsCoprime (Ideal.span {N}) ((S P).ideal i))
    (rowClass slotClass : Eis⧸Ideal.span {N^2})
    (hrowClass : ∀ K∈rows, Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)=rowClass)
    (hslotClass : ∀ P∈Pset, Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator P)=slotClass) :
    Nonempty (SectorArithmetic (N:=N) F rows Pset S hrows s hc) := by
  obtain ⟨E,hE⟩ := exists_fixed_ray_source_arithmetic F rows Pset S hrows hprod N a c mode s hc hN hbase hac
    hF hNF hrowcop hScop hSN rowClass slotClass hrowClass hslotClass
  let D := fun (K : rows) (P : Pset) (hp : IsCoprime K.val P.val) => E ⟨(K,P),hp⟩
  by_cases hnon : Nonempty (SourcePair rows Pset)
  · let x0 : SourcePair rows Pset := Classical.choice hnon
    exact ⟨{
      referenceIndex := φ ⊕ (PrimeIndex x0.val.1.val ⊕ σ)
      referencePrimes := F.reflected x0.val.1.val (hrows x0.val.1.val x0.val.1.property) (S x0.val.2.val)
      referenceArithmetic := E x0
      completion := D
      fixedFactor_eq := fun K P hp => (hE x0 ⟨(K,P),hp⟩).1
      cuspColumn_eq := fun K P hp => (hE x0 ⟨(K,P),hp⟩).2
    }⟩
  · let G0 : PrimeFamily (ULift.{v} φ) := ⟨fun x => F.ideal x.down,fun x => F.maximal x.down,fun x => F.good x.down⟩
    obtain ⟨D0⟩ := G0.exists_controlled N a c mode hc hN hbase hac
      (fun x y hxy => hF (fun h => hxy (ULift.ext x y h))) (fun x => hNF x.down)
    exact ⟨{
      referenceIndex := ULift.{v} φ
      referencePrimes := G0
      referenceArithmetic := D0
      completion := D
      fixedFactor_eq := fun K P hp => (hnon ⟨⟨(K,P),hp⟩⟩).elim
      cuspColumn_eq := fun K P hp => (hnon ⟨⟨(K,P),hp⟩⟩).elim
    }⟩
end
end SevenEighths.InverseReflectedPhase

end OAI
