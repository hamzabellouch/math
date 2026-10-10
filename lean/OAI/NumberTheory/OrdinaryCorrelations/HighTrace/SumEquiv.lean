import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AvgFintypeChange
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.NumericalLine
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.WitnessSlotCount
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Realizable

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.ArithmeticSaving
open OrdinaryCorrelations.SharedSlotPatterns OrdinaryCorrelations.SourceCylinder
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L t : ℕ}
namespace WitnessConfiguration

noncomputable def sumEquiv :
    ((w : NumericalLine D h ℓ) ×
      (↥(boundedLists (AttachedSpec w.line D L) t) × PrivateFamily w.line D L t)) ≃
        WitnessConfiguration D h ℓ L t where
  toFun z := ⟨z.1.line,z.1.labels,z.2.1.val,(mem_boundedLists _ _).mp z.2.1.property,z.2.2⟩
  invFun x := ⟨⟨x.line,x.labels⟩,⟨x.primitives,(mem_boundedLists _ _).mpr x.length_le⟩,x.family⟩
  left_inv z := by rcases z with ⟨⟨w,hw⟩,⟨l,hl⟩,F⟩; rfl
  right_inv x := by cases x; rfl

lemma sum_crude_eq :
    (∑ w : NumericalLine D h ℓ,
      ∑ l ∈ boundedLists (AttachedSpec w.line D L) t,
        ∑ F : PrivateFamily w.line D L t, crudeListWeight w.line (l++List.ofFn F.witness)) =
    ∑ x : WitnessConfiguration D h ℓ L t,
      crudeListWeight x.line (x.primitives++List.ofFn x.family.witness) := by
  rw [←sumEquiv.sum_comp (fun x : WitnessConfiguration D h ℓ L t =>
    crudeListWeight x.line (x.primitives++List.ofFn x.family.witness))]
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro w _
  rw [Fintype.sum_prod_type]
  exact (sum_coe_sort (boundedLists (AttachedSpec w.line D L) t)
    (fun l => ∑ F : PrivateFamily w.line D L t, crudeListWeight w.line (l++List.ofFn F.witness))).symm

lemma crude_le (x : WitnessConfiguration D h ℓ L t) :
    crudeListWeight x.line (x.primitives++List.ofFn x.family.witness) ≤
      if x.Realizable then
        (A^(ℓ*⌈C₀*Real.log B⌉₊) * 2^(witnessSlotCount ℓ L ⌈C₀*Real.log B⌉₊ t))*x.primeWeight
      else 0 := by
  by_cases hx : x.Realizable
  · rw [ite_eq_left hx,crudeListWeight,ite_eq_left (show JointlyRealizable _ _ from hx)]
    have hu : fullUsedIndices x.line (x.primitives++List.ofFn x.family.witness)=support x.primeCode :=
      x.support_eq_used.symm
    rw [hu]
    apply mul_le_mul_of_nonneg_right _ x.primeWeight_nonneg
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg A_pos.le _)
    exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (card_support_le x.primeCode)
  · rw [ite_eq_right hx,crudeListWeight,ite_eq_right (show ¬JointlyRealizable _ _ from hx)]

lemma sum_crude_le :
    (∑ x : WitnessConfiguration D h ℓ L t,
      crudeListWeight x.line (x.primitives++List.ofFn x.family.witness)) ≤
    (A^(ℓ*⌈C₀*Real.log B⌉₊) * 2^(witnessSlotCount ℓ L ⌈C₀*Real.log B⌉₊ t)) *
      ∑ x : {x : WitnessConfiguration D h ℓ L t // x.Realizable}, x.val.primeWeight := by
  calc
    _ ≤ ∑ x : WitnessConfiguration D h ℓ L t,
        if x.Realizable then
          (A^(ℓ*⌈C₀*Real.log B⌉₊) * 2^(witnessSlotCount ℓ L ⌈C₀*Real.log B⌉₊ t))*x.primeWeight
        else 0 := sum_le_sum (fun x _ => x.crude_le)
    _ = (A^(ℓ*⌈C₀*Real.log B⌉₊) * 2^(witnessSlotCount ℓ L ⌈C₀*Real.log B⌉₊ t)) *
        ∑ x : WitnessConfiguration D h ℓ L t, if x.Realizable then x.primeWeight else 0 := by
      rw [mul_sum]
      exact sum_congr rfl (fun x _ => by split_ifs <;> simp)
    _ = _ := by
      congr 1
      rw [←sum_filter]
      exact sum_subtype _ (by simp) _

end WitnessConfiguration
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
