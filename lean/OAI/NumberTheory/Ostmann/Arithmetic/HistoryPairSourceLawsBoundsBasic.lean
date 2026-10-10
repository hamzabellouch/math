import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsCarriers
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedFlagMassBoundsBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceLaws
open Construction CompensationEqualityPatterns HistorySelectedFlagMassBounds
attribute [local instance] Classical.propDecidable

structure SupportBounds {α : Type*} (k : ℕ) (L : ℝ)
    (S : Finset α) (w : α → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ w a
  mass : (∑ a ∈ S, w a) ≤ massCap k L
  atom : ∀ a, w a ≤ atomCap k L

theorem integerWeight_eq_zero_of_not_mem {κ : Type*} [Fintype κ]
    (value : κ → ℤ) (w : κ → ℝ) (z : ℤ) (hz : z ∉ integerSupport value) :
    integerWeight value w z = 0 := by
  classical
  unfold integerWeight
  apply Finset.sum_eq_zero
  intro a ha
  have h : value a ≠ z := by
    intro h
    exact hz (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, h⟩)
  simp only [h, ite_false]

theorem integerWeight_bounds {κ : Type*} [Fintype κ]
    (value : κ → ℤ) (hinj : Function.Injective value) (w : κ → ℝ)
    {k : ℕ} {L : ℝ} (hw : Bounds k L w) :
    SupportBounds k L (integerSupport value) (integerWeight value w) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro z
    exact Finset.sum_nonneg (fun a _ => by
      split_ifs <;> simp_all only [hw.nonneg, le_refl])
  · rw [integerWeight_mass value hinj w]
    exact hw.mass
  · intro z
    by_cases hz : z ∈ integerSupport value
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      rw [integerWeight_apply value hinj w a]
      exact hw.atom a
    · rw [integerWeight_eq_zero_of_not_mem value w z hz]
      exact (Real.exp_pos _).le

theorem source_integerValue_injective (S : PrimeSource) :
    Function.Injective (fun a : S.Sample => (a.val : ℤ)) := by
  intro a b h
  exact Subtype.ext (Int.ofNat_injective h)

theorem common_integerValue_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sources : SourceFamily) (origin : ι → ℕ) :
    Function.Injective (fun a : CommonSample sources origin => (a.val : ℤ)) := by
  intro a b h
  exact Subtype.ext (Int.ofNat_injective h)

end Ostmann.Arithmetic.HistoryPairSourceLaws

end

end OAI
