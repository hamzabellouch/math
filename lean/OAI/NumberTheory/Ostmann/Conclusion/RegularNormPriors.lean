import OAI.NumberTheory.Ostmann.Conclusion.RegularNormSourceRanges
import OAI.NumberTheory.Ostmann.Conclusion.RegularNormTupleScale
import OAI.NumberTheory.Ostmann.Construction.ActualIntegerTransfer
import OAI.NumberTheory.Ostmann.Construction.HalfListTest

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open scoped BigOperators
open Ostmann.Construction

theorem regular_mean_le_const_on_mass {α : Type*} [Fintype α]
    (μ : FinitePrior α) (f : α → ℝ) (B : ℝ)
    (h : ∀x,μ.mass x≠0 → f x≤B) : μ.mean f≤B := by
  rw [←μ.mean_const B]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hm : μ.mass x=0
  · simp only [hm,zero_mul,le_refl]
  · exact mul_le_mul_of_nonneg_left (h x hm) (μ.mass_nonneg x)

theorem regular_mean_fintype_sum {α β : Type*} [Fintype α] [Fintype β]
    (μ : FinitePrior α) (f : α → β → ℝ) :
    μ.mean (fun x => ∑y,f x y)=∑y,μ.mean (fun x => f x y) := by
  simp only [FinitePrior.mean,Finset.mul_sum]
  exact Finset.sum_comm

theorem regular_outer_mean (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (f : OuterSample sources T giant → ℝ) :
    (outerPrior sources T giant).mean f =
      (assignmentPrior sources T).mean (fun x => giant.law.mean (fun q =>
        giant.law.mean (fun p => f (p,q,x)))) := by
  rw [outerPrior,FinitePrior.pair_mean,FinitePrior.mean_comm]
  rw [FinitePrior.pair_mean,FinitePrior.mean_comm]

theorem regular_allowedFrequency_card (V : ℕ → ℕ) (l : ℕ) :
    Fintype.card (AllowedFrequency V l)=2*V l+1 := by
  rw [Fintype.card_coe,Int.card_Icc]
  omega

theorem actualRegularEnergy_le_of_tuple_means
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (giant spectator : PrimeSource) (m : ℕ) (g giantTransform : (p : ℕ) → ZMod p → ℂ)
    (l : ℕ) (B : ℝ)
    (hmean : ∀ x : SourceAssignment sources (Template.current seed l),
      (assignmentPrior sources (Template.current seed l)).mass x≠0 →
      ∀ outside s q, giant.law.mean (fun p =>
        ‖supportedRegularTransform g giantTransform outside
          (State.mk s p.val q (assignedSlots sources (Template.current seed l) x))‖^2)≤B) :
    actualRegularEnergy sources seed V giant spectator m g giantTransform l≤B*(2*(V l:ℝ)+1) := by
  rw [actualRegularEnergy,amplitudePrior,FinitePrior.pair_mean]
  apply regular_mean_le_const_on_mass
  intro ds hds
  rw [regular_outer_mean]
  apply regular_mean_le_const_on_mass
  intro x hx
  apply regular_mean_le_const_on_mass
  intro q hq
  rw [regular_mean_fintype_sum]
  calc
    _ ≤ ∑ _ : AllowedFrequency V l,B := Finset.sum_le_sum (fun s _ =>
      hmean x hx (spectatorList spectator ds) s.val q.val)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,regular_allowedFrequency_card,
      nsmul_eq_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]; ring

end Ostmann.Conclusion

end

end OAI
