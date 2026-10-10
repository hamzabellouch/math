import OAI.NumberTheory.DirichletL.Reflection.Common

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

structure PrimeFamily (ι : Type*) where
  ideal : ι → Ideal Eis
  maximal : ∀ i, (ideal i).IsMaximal
  good : ∀ i, λ₀ ∉ ideal i

namespace PrimeFamily
variable {ι : Type*} (G : PrimeFamily ι)
instance idealMaximal (i : ι) : (G.ideal i).IsMaximal := G.maximal i

def generator (i : ι) : Eis := primaryPrime (G.ideal i)

lemma generator_ne_zero (i : ι) : G.generator i ≠ 0 := primaryPrime_ne_zero _ (G.good i)
lemma generator_span (i : ι) : Ideal.span {G.generator i} = G.ideal i :=
  (primaryPrime_spec _ (G.generator_ne_zero i)).2.2.1
lemma generator_primary (i : ι) : λ₀^2 ∣ G.generator i-1 :=
  (primaryPrime_spec _ (G.generator_ne_zero i)).2.2.2
instance generatorMaximal (i : ι) : (Ideal.span {G.generator i}).IsMaximal :=
  G.generator_span i ▸ G.maximal i
lemma generator_good (i : ι) : λ₀ ∉ Ideal.span {G.generator i} := by
  rw [G.generator_span]
  exact G.good i

lemma generator_product [Fintype ι] :
    (∏ i, G.generator i) = primaryGenerator (∏ i, G.ideal i) := by
  change _ = primaryGeneratorHom (∏ i, G.ideal i)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact primaryPrime_eq_primaryGenerator (G.ideal i)

lemma generator_product_primary [Fintype ι] : λ₀^2 ∣ (∏ i, G.generator i)-1 :=
  primary_finset_product Finset.univ G.generator (fun i _ => G.generator_primary i)

lemma generator_coprime_period (N : Eis)
    (hN : ∀ i, IsCoprime (Ideal.span {N}) (G.ideal i)) (i : ι) :
    IsCoprime N (G.generator i) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [G.generator_span]
  exact hN i

lemma generator_product_coprime_period [Fintype ι] (N c : Eis) (hc : c ∣ N)
    (hN : ∀ i, IsCoprime (Ideal.span {N}) (G.ideal i)) :
    IsCoprime (∏ i, G.generator i) (N*c) := by
  have hh : IsCoprime N (∏ i, G.generator i) :=
    IsCoprime.prod_right (fun i _ => G.generator_coprime_period N hN i)
  exact hh.symm.mul_right (hh.symm.of_isCoprime_of_dvd_right hc)

theorem exists_controlled [Fintype ι] (N a c : Eis) (mode : Bool)
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hcop : Pairwise (Function.onFun IsCoprime G.ideal))
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (G.ideal i)) :
    Nonempty (ControlledStratumArithmetic G.generator N a c mode) := by
  apply exists_controlledStratumArithmetic G.generator G.generator_ne_zero
  · intro i k hik
    simpa only [G.generator_span] using hcop hik
  · exact G.generator_primary
  · exact hc
  · exact hN
  · exact hbase
  · exact hac
  · exact G.generator_coprime_period N hNp

end PrimeFamily

theorem canonical_common_reflected_coefficients {α κ : Type*} [Fintype κ]
    {ι : α → Type*} [∀ x, Fintype (ι x)] (G : ∀ x, PrimeFamily (ι x))
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hcop : ∀ x, Pairwise (Function.onFun IsCoprime (G x).ideal))
    (hNp : ∀ x i, IsCoprime (Ideal.span {N}) ((G x).ideal i))
    (j : ∀ x, ι x → ℕ) (f : ∀ x, κ → ι x) (hf : ∀ x, Function.Injective (f x))
    (hfixed : ∀ x y i, (G x).ideal (f x i)=(G y).ideal (f y i))
    (hjfixed : ∀ x y i, j x (f x i)=j y (f y i)) (F : Finset κ)
    (fixedIdeal : Ideal Eis) (row slot : α → Ideal Eis)
    (hprod : ∀ x, (∏ i, (G x).ideal i) = fixedIdeal*row x*slot x) :
    ∃ E : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode,
      ∃ (γ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → Eisˣ → ℕ → ℂ)
        (β : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ x u m, sourceFrozenPhase (E x) s (G x).generator_ne_zero (G x).generator_good
          (j x) (F.image (f x)) u m =
          γ (separateSector N (primaryGenerator (row x)) (primaryGenerator (slot x))) u m) ∧
        ∀ x u m n b, sourceColumn (E x) s hc (G x).generator_good (j x) (F.image (f x)) u m n b =
          β (separateSector N (primaryGenerator (row x)) (primaryGenerator (slot x))) u m n b := by
  let D : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode := fun x =>
    Classical.choice ((G x).exists_controlled N a c mode hc hN hbase hac (hcop x) (hNp x))
  have hproduct (x : α) : (∏ i, (G x).generator i) =
      primaryGenerator fixedIdeal*primaryGenerator (row x)*primaryGenerator (slot x) := by
    rw [(G x).generator_product,hprod x,primaryGenerator_mul,primaryGenerator_mul]
  obtain ⟨E,_,_,_,_,γ,β,hγ,hβ⟩ := exists_separate_common_reflected_coefficients
    (fun x => (G x).generator) N a c mode D s (fun x => (G x).generator_ne_zero) hc
    (fun x => (G x).generator_good) hN (fun x => (G x).generator_product_primary) hbase
    (fun x => (G x).generator_product_coprime_period N c ((dvd_mul_left c 9).trans hN) (hNp x))
    j f hf (fun x y i => congrArg primaryPrime (hfixed x y i)) hjfixed F
    (primaryGenerator fixedIdeal) (fun x => primaryGenerator (row x)) (fun x => primaryGenerator (slot x)) hproduct
  exact ⟨E,γ,β,hγ,hβ⟩

end
end SevenEighths.InverseReflectedPhase

end OAI
