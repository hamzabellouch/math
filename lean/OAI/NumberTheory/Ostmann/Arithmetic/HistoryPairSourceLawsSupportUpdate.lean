import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsSupportBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceLaws
open Construction CompensationEqualityPatterns
attribute [local instance] Classical.propDecidable
variable {ι ρ η : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype η] [DecidableEq η]

omit [DecidableEq ι] in
theorem updated_mixed_mass_ne_zero [DecidableEq ι]
    (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (e : SourceIndex ρ (Block p) ≃ η) (q : Block p) (x : η → ℤ) (b : ℕ)
    (hx : (∏ j, dummyMass giants roots sources origin p e q j (x j)) ≠ 0)
    (hb : blockNaturalWeight sources origin p q b ≠ 0) :
    ∀ j, mixedMass giants roots sources origin p (e.symm j)
      (Function.update x (e (.inr (.inr q))) (b : ℤ) j) ≠ 0 := by
  have hbmem : b ∈ commonCandidates sources origin := by
    by_contra hn
    exact hb (by simp only [blockNaturalWeight,hn,dite_false])
  have hbw : biasedBlockWeight sources origin p q ⟨b,hbmem⟩ ≠ 0 := by
    simpa only [blockNaturalWeight,hbmem,dite_true] using hb
  intro j
  by_cases hj : j = e (.inr (.inr q))
  · subst j
    rw [Function.update_self,e.symm_apply_apply]
    change integerWeight (fun v : CommonSample sources origin => (v.val : ℤ))
      (biasedBlockWeight sources origin p q) ((⟨b,hbmem⟩ : CommonSample sources origin).val : ℤ) ≠ 0
    have hinj : Function.Injective (fun v : CommonSample sources origin => (v.val : ℤ)) := by
      intro a b h
      exact Subtype.ext (Int.ofNat_injective h)
    rw [integerWeight_apply (fun v : CommonSample sources origin => (v.val : ℤ)) hinj]
    exact hbw
  · have hm : dummyMass giants roots sources origin p e q j (x j) ≠ 0 :=
      fun hz => hx (Finset.prod_eq_zero (Finset.mem_univ j) hz)
    simpa only [dummyMass,Function.update_of_ne hj] using hm

omit [Fintype η] [DecidableEq η] in

theorem mixed_small_source_values (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (e : SourceIndex ρ (Block p) ≃ η) (y : η → ℤ)
    (hy : ∀ j, mixedMass giants roots sources origin p (e.symm j) (y j) ≠ 0) :
    (∀ i, PositiveSourceValue (roots i) (y (e (.inr (.inl i))))) ∧
    (∀ i, PositiveSourceValue (sources (origin i)) (y (e (.inr (.inr (label p i)))))) := by
  constructor
  · intro i
    have h := hy (e (.inr (.inl i)))
    rw [e.symm_apply_apply] at h
    exact positiveSourceValue_of_integerWeight (roots i) h
  · intro i
    have h := hy (e (.inr (.inr (label p i))))
    rw [e.symm_apply_apply] at h
    exact positiveSourceValue_of_block_integerWeight sources origin p (label p i) h ⟨i,rfl⟩

theorem updated_small_source_values (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (e : SourceIndex ρ (Block p) ≃ η) (q : Block p) (x : η → ℤ) (b : ℕ)
    (hx : (∏ j, dummyMass giants roots sources origin p e q j (x j)) ≠ 0)
    (hb : blockNaturalWeight sources origin p q b ≠ 0) :
    let y := Function.update x (e (.inr (.inr q))) (b : ℤ)
    (∀ i, PositiveSourceValue (roots i) (y (e (.inr (.inl i))))) ∧
    (∀ i, PositiveSourceValue (sources (origin i)) (y (e (.inr (.inr (label p i)))))) :=
  mixed_small_source_values giants roots sources origin p e _
    (updated_mixed_mass_ne_zero giants roots sources origin p e q x b hx hb)

end Ostmann.Arithmetic.HistoryPairSourceLaws

end

end OAI
