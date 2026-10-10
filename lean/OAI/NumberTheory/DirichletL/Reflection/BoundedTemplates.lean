import OAI.NumberTheory.DirichletL.Reflection.Columns

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def boundedExtension (z : ℂ) : ℂ := if ‖z‖ ≤ 1 then z else 0
lemma boundedExtension_norm (z : ℂ) : ‖boundedExtension z‖ ≤ 1 := by
  unfold boundedExtension
  split_ifs with h
  · exact h
  · simp
lemma boundedExtension_eq (z : ℂ) (hz : ‖z‖ ≤ 1) : boundedExtension z = z := ite_eq_left hz

theorem canonical_bounded_cusp_templates {α : Type*} {ι : α → Type*}
    [∀ x, Fintype (ι x)] (G : ∀ x, PrimeFamily (ι x))
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hcop : ∀ x, Pairwise (Function.onFun IsCoprime (G x).ideal))
    (hNp : ∀ x i, IsCoprime (Ideal.span {N}) ((G x).ideal i))
    (fixedIdeal : Ideal Eis) (row slot : α → Ideal Eis)
    (hprod : ∀ x, (∏ i, (G x).ideal i) = fixedIdeal*row x*slot x) :
    ∃ E : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode,
      ∃ (κ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → ℂ)
        (A : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ q, ‖κ q‖ ≤ 1) ∧ (∀ q u m n b, ‖A q u m n b‖ ≤ 1) ∧
        (∀ x, (E x).fixedFactor = κ (separateSector N (primaryGenerator (row x))
          (primaryGenerator (slot x)))) ∧
        ∀ x u m n b, actualCuspColumn (E x) s hc u m n b =
          A (separateSector N (primaryGenerator (row x)) (primaryGenerator (slot x))) u m n b := by
  let D : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode := fun x =>
    Classical.choice ((G x).exists_controlled N a c mode hc hN hbase hac (hcop x) (hNp x))
  have hproduct (x : α) : (∏ i, (G x).generator i) =
      primaryGenerator fixedIdeal*primaryGenerator (row x)*primaryGenerator (slot x) := by
    rw [(G x).generator_product,hprod x,primaryGenerator_mul,primaryGenerator_mul]
  obtain ⟨E,_,_,_,_,κ,A,hκ,hA⟩ := exists_separate_ray_templates
    (fun x => (G x).generator) N a c mode D s hc hN
    (fun x => (G x).generator_product_primary) hbase
    (fun x => (G x).generator_product_coprime_period N c ((dvd_mul_left c 9).trans hN) (hNp x))
    (primaryGenerator fixedIdeal) (fun x => primaryGenerator (row x))
    (fun x => primaryGenerator (slot x)) hproduct
  refine ⟨E,fun q => boundedExtension (κ q),fun q u m n b => boundedExtension (A q u m n b),
    fun q => boundedExtension_norm _,fun q u m n b => boundedExtension_norm _,?_,?_⟩
  · intro x
    change (E x).fixedFactor = boundedExtension _
    rw [← hκ x,boundedExtension_eq _ ((E x).fixedFactor_norm hN
      (G x).generator_product_primary hbase).le]
  · intro x u m n b
    change actualCuspColumn (E x) s hc u m n b = boundedExtension _
    rw [← hA x u m n b]
    exact (boundedExtension_eq _ (actualCuspColumn_norm_le_one (E x) s hc u m n b)).symm

theorem common_frozen_branch_bound {φ Q : Type*} [Fintype φ]
    (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Q → Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ)
    (hA : ∀ q u m n b, ‖A q u m n b‖ ≤ 1) (q : Q) (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    ‖frozenBranchColumn F jF e (A q u m) n b‖ ≤ frozenBranchScale F jF e :=
  frozenBranchColumn_norm_le F jF e (A q u m) (hA q u m) n b

end
end SevenEighths.InverseReflectedPhase

end OAI
