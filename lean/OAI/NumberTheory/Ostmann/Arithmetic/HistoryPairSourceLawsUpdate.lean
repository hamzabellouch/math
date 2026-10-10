import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsMixed

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceLaws
open Construction CompensationEqualityPatterns
attribute [local instance] Classical.propDecidable
variable {ι ρ η : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]
  [Fintype η] [DecidableEq η]

theorem integerWeight_sum_test {κ : Type*} [Fintype κ]
    (value : κ → ℤ) (hinj : Function.Injective value) (w : κ → ℝ) (F : ℤ → ℝ) :
    (∑ z ∈ integerSupport value, integerWeight value w z*F z) =
      ∑ a, w a*F (value a) := by
  classical
  unfold integerSupport
  rw [Finset.sum_image (fun a ha b hb h => hinj h)]
  simp only [integerWeight_apply value hinj]

def blockNaturalWeight (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ}
    (p : Pattern τ) (q : Block p) (n : ℕ) : ℝ :=
  if hn : n ∈ commonCandidates sources origin then biasedBlockWeight sources origin p q ⟨n,hn⟩ else 0

omit [DecidableEq ι] in
theorem blockNaturalWeight_sum (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ}
    (p : Pattern τ) (q : Block p) (F : ℕ → ℝ) :
    (∑ v : CommonSample sources origin, biasedBlockWeight sources origin p q v*F v.val) =
      ∑ n ∈ commonCandidates sources origin, blockNaturalWeight sources origin p q n*F n := by
  have h := Finset.sum_coe_sort (commonCandidates sources origin)
    (fun n => blockNaturalWeight sources origin p q n*F n)
  simpa only [blockNaturalWeight,Subtype.property,dite_true] using h

def dummyMass (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (e : SourceIndex ρ (Block p) ≃ η) (q : Block p) : η → ℤ → ℝ :=
  Function.update (fun j => mixedMass giants roots sources origin p (e.symm j))
    (e (.inr (.inr q)))
    (integerWeight (fun a : CommonSample sources origin => (a.val : ℤ))
      (sourceWeight sources origin (blockAnchor p q).val))

omit [Fintype ρ] [DecidableEq ρ] in

theorem mixed_product_sum_update (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (e : SourceIndex ρ (Block p) ≃ η) (q : Block p) (F : (η → ℤ) → ℝ) :
    (∑ y ∈ Fintype.piFinset (fun j => mixedSupport giants roots sources origin p (e.symm j)),
      (∏ j, mixedMass giants roots sources origin p (e.symm j) (y j))*F y) =
      ∑ x ∈ Fintype.piFinset (fun j => mixedSupport giants roots sources origin p (e.symm j)),
        (∏ j, dummyMass giants roots sources origin p e q j (x j))*
          ∑ b ∈ commonCandidates sources origin, blockNaturalWeight sources origin p q b*
            F (Function.update x (e (.inr (.inr q))) (b : ℤ)) := by
  let S := fun j => mixedSupport giants roots sources origin p (e.symm j)
  let r := e (.inr (.inr q))
  let ν := integerWeight (fun a : CommonSample sources origin => (a.val : ℤ))
    (biasedBlockWeight sources origin p q)
  have hS : S r = integerSupport (fun a : CommonSample sources origin => (a.val : ℤ)) := by
    change mixedSupport giants roots sources origin p (e.symm (e (.inr (.inr q)))) = _
    rw [e.symm_apply_apply]
    rfl
  have hu : ∑ z ∈ S r, dummyMass giants roots sources origin p e q r z = 1 := by
    rw [hS]
    simp only [dummyMass,r,Function.update_self]
    exact common_source_integerWeight_mass sources origin (blockAnchor p q).val
  have h := product_sum_update_normalized S (dummyMass giants roots sources origin p e q)
    r (S r) ν hu F
  have hμ : Function.update (dummyMass giants roots sources origin p e q) r ν =
      fun j => mixedMass giants roots sources origin p (e.symm j) := by
    funext j z
    by_cases hj : j = r
    · subst j
      simp only [Function.update_self]
      change ν z = mixedMass giants roots sources origin p (e.symm (e (.inr (.inr q)))) z
      rw [e.symm_apply_apply]
      rfl
    · simp only [dummyMass,Function.update_of_ne hj,show e (.inr (.inr q)) = r from rfl]
  rw [Function.update_eq_self,hμ] at h
  rw [←h]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  rw [hS]
  dsimp only [ν]
  have hv : Function.Injective (fun a : CommonSample sources origin => (a.val : ℤ)) := by
    intro a b he
    exact Subtype.ext (Int.ofNat_injective he)
  exact (integerWeight_sum_test (fun a : CommonSample sources origin => (a.val : ℤ)) hv
    (biasedBlockWeight sources origin p q) (fun z => F (Function.update x r z))).trans
      (blockNaturalWeight_sum sources origin p q (fun b => F (Function.update x r (b : ℤ))))

end Ostmann.Arithmetic.HistoryPairSourceLaws

end

end OAI
