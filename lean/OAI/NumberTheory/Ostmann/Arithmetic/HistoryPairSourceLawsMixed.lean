import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsBlocks

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceLaws
open Construction CompensationEqualityPatterns
attribute [local instance] Classical.propDecidable
variable {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]

abbrev SourceIndex (ρ β : Type*) := Bool ⊕ (ρ ⊕ β)

def mixedCarrier (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ) :
    SourceIndex ρ (Block p) → Type
  | .inl b => (giants b).Sample
  | .inr (.inl i) => (roots i).Sample
  | .inr (.inr _) => CommonSample sources origin

instance mixedCarrierFintype (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (i : SourceIndex ρ (Block p)) : Fintype (mixedCarrier giants roots sources origin p i) := by
  rcases i with b | i | q <;> dsimp [mixedCarrier] <;> infer_instance

def mixedValue (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ) :
    ∀ i, mixedCarrier giants roots sources origin p i → ℤ
  | .inl _, a => a.val
  | .inr (.inl _), a => a.val
  | .inr (.inr _), a => a.val

def mixedWeight (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ) :
    ∀ i, mixedCarrier giants roots sources origin p i → ℝ
  | .inl b, a => (giants b).law.mass a
  | .inr (.inl i), a => (roots i).law.mass a
  | .inr (.inr q), a => biasedBlockWeight sources origin p q a

omit [DecidableEq ι] [Fintype ρ] [DecidableEq ρ] in
theorem mixedValue_injective (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (i : SourceIndex ρ (Block p)) : Function.Injective (mixedValue giants roots sources origin p i) := by
  rcases i with b | i | q <;> intro a b h <;> exact Subtype.ext (Int.ofNat_injective h)

def mixedSupport (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (i : SourceIndex ρ (Block p)) : Finset ℤ :=
  integerSupport (mixedValue giants roots sources origin p i)

def mixedMass (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (i : SourceIndex ρ (Block p)) : ℤ → ℝ :=
  integerWeight (mixedValue giants roots sources origin p i)
    (mixedWeight giants roots sources origin p i)

omit [DecidableEq ι] in

theorem mixed_product_sum_reindex {η : Type*} [Fintype η] [DecidableEq η]
    (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (e : SourceIndex ρ (Block p) ≃ η) (F : (η → ℤ) → ℝ) :
    (∑ x : ∀ i, mixedCarrier giants roots sources origin p i,
      (∏ i, mixedWeight giants roots sources origin p i (x i))*
        F (fun j => mixedValue giants roots sources origin p (e.symm j) (x (e.symm j)))) =
      ∑ y ∈ Fintype.piFinset (fun j => mixedSupport giants roots sources origin p (e.symm j)),
        (∏ j, mixedMass giants roots sources origin p (e.symm j) (y j))*F y :=
  product_sum_integer_reindex e _ _ (mixedValue_injective giants roots sources origin p) _ F

omit [DecidableEq ι] [DecidableEq ρ] in

theorem mixed_weight_product (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (x : ∀ i, mixedCarrier giants roots sources origin p i) :
    (∏ i, mixedWeight giants roots sources origin p i (x i)) =
      (∏ b, (giants b).law.mass (x (.inl b))) *
        ((∏ i, (roots i).law.mass (x (.inr (.inl i)))) *
          ∏ q, biasedBlockWeight sources origin p q (x (.inr (.inr q)))) := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  rfl

end Ostmann.Arithmetic.HistoryPairSourceLaws

end

end OAI
