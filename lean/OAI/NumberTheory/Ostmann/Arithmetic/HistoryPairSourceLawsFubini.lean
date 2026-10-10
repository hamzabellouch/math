import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsMixed

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceLaws
open Construction CompensationEqualityPatterns
variable {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]

def assembleMixed (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (a : ∀ b, (giants b).Sample) (x : ∀ i, (roots i).Sample)
    (v : Block p → CommonSample sources origin) :
    ∀ i, mixedCarrier giants roots sources origin p i
  | .inl b => a b
  | .inr (.inl i) => x i
  | .inr (.inr q) => v q

def mixedDrawEquiv (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ) :
    (∀ i, mixedCarrier giants roots sources origin p i) ≃
      (∀ b, (giants b).Sample) × ((∀ i, (roots i).Sample) × (Block p → CommonSample sources origin)) where
  toFun x := ⟨fun b => x (.inl b), fun i => x (.inr (.inl i)), fun q => x (.inr (.inr q))⟩
  invFun z := assembleMixed giants roots sources origin p z.1 z.2.1 z.2.2
  left_inv x := by funext i; rcases i with b | i | q <;> rfl
  right_inv x := rfl

omit [DecidableEq ι] in

theorem mixed_product_sum_eq_nested (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (F : (∀ i, mixedCarrier giants roots sources origin p i) → ℝ) :
    (∑ x : ∀ i, mixedCarrier giants roots sources origin p i,
      (∏ i, mixedWeight giants roots sources origin p i (x i))*F x) =
      ∑ a : ∀ b, (giants b).Sample, ∑ x : ∀ i, (roots i).Sample,
        ∑ v : Block p → CommonSample sources origin,
          ((∏ b, (giants b).law.mass (a b))*
            ((∏ i, (roots i).law.mass (x i))*∏ q, biasedBlockWeight sources origin p q (v q)))*
            F (assembleMixed giants roots sources origin p a x v) := by
  have h := (mixedDrawEquiv giants roots sources origin p).symm.sum_comp
    (fun x => (∏ i, mixedWeight giants roots sources origin p i (x i))*F x)
  have hi (z) : (mixedDrawEquiv giants roots sources origin p).symm z =
      assembleMixed giants roots sources origin p z.1 z.2.1 z.2.2 := rfl
  simp_rw [hi, mixed_weight_product] at h
  simpa only [Fintype.sum_prod_type,assembleMixed,mixed_weight_product] using h.symm

end Ostmann.Arithmetic.HistoryPairSourceLaws

end

end OAI
