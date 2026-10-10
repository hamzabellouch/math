import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SlotWeight
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RecordPacket
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ExceptionalCodeSlot
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FlatCode

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.TaggedPrimeGroups
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma untagged_reference_weight {v w : ClosedLine h ℓ} (H : SameGeometry v w)
    (hh : 0 < h) (𝔏 : List (AttachedSpec v D L)) (a : S.FixedResidues v)
    (pC pZ : S.Index) (_hpC : S.IsCore pC) (_hpZ : ¬S.IsCore pZ) :
    (∏ p : S.Index, TypeFibers.factor (untaggedReference H hh 𝔏 a)
      (fun t p => tokenWeight w pC pZ t * slotWeight S (t.1=true) p) p) =
    FactorialAssignments.unorderedWeight (TypeFibers.multiplicity (untaggedType v hh 𝔏 a))
      (fun t (p : S.Index) => tokenWeight v pC pZ t * (p:ℝ)⁻¹)
      (TypeFibers.unordered (untaggedType v hh 𝔏 a)) := by
  rw [TypeFibers.unorderedWeight_eq]
  apply prod_congr rfl
  intro p hp
  rcases he : untaggedType v hh 𝔏 a p with _ | t
  · simp only [TypeFibers.factor,untaggedReference,he,Option.map_none]
  · have ht := (untaggedType_some v hh 𝔏 a p t he).1
    simp only [TypeFibers.factor,untaggedReference,he,Option.map_some,slotWeight,ht,ite_true]
    rw [← tokenWeight_reference H]

namespace RecordPacket
variable {w₀ : ClosedLine h ℓ} {hh : 0 < h} {r : ℕ}
variable {hr₀ : (returnSteps w₀).card=r} {n N : ℕ}

noncomputable instance fintype : Fintype (RecordPacket D L w₀ hh r hr₀ n N) := Fintype.ofFinite _

noncomputable def exceptionalWeight (c : FlatCode S w₀ C₀ B L n N) : ℝ :=
  weight (paddedGroupWeight (fun p : S.Index => (p:ℝ)⁻¹)) c.2.1 *
    ∏ i : Fin N, paddedShapeWeight (fun p s => localTokenWeight w₀ p (taggedShapeCode w₀ s))
      (c.2.1 (exceptionalPick L ⌈C₀*Real.log B⌉₊ n N i)) (c.2.2.1 i)

noncomputable def flatWeight (pC pZ : S.Index) (c : FlatCode S w₀ C₀ B L n N) : ℝ :=
  exceptionalWeight c * ∏ p : S.Index, TypeFibers.factor c.2.2.2
    (fun t p => tokenWeight w₀ pC pZ t * slotWeight S (t.1=true) p) p

noncomputable def nativeWeight (x : RecordPacket D L w₀ hh r hr₀ n N) : ℝ :=
  ∏ p : S.Index, (if UsedPrime x.line x.primitives p then (p:ℝ)⁻¹ else 1) *
    recordTreeWeight x.line hh x.primitives x.record p

lemma flatWeight_code (pC pZ : S.Index) (hpC : S.IsCore pC) (hpZ : ¬S.IsCore pZ)
    (x : RecordPacket D L w₀ hh r hr₀ n N) : flatWeight pC pZ x.flatCode=x.nativeWeight := by
  unfold nativeWeight flatWeight exceptionalWeight
  rw [← x.realized_residues,record_weight_factorization x.line hh x.primitives x.residues pC pZ hpC hpZ]
  rw [exceptionalCode_weight x.geometry hh x.primitives x.residues n N x.length_le x.tagCount]
  congr 1
  exact untagged_reference_weight x.geometry hh x.primitives x.residues pC pZ hpC hpZ

lemma factor_nonneg {P T : Type*} (f : P → Option T) (W : T → P → ℝ)
    (hW : ∀ t p, 0 ≤ W t p) (p : P) : 0 ≤ TypeFibers.factor f W p := by
  unfold TypeFibers.factor
  cases he : f p with
  | none => exact zero_le_one
  | some t => exact hW t p

lemma exceptionalWeight_nonneg (c : FlatCode S w₀ C₀ B L n N) : 0 ≤ exceptionalWeight c := by
  unfold exceptionalWeight
  apply mul_nonneg
  · exact weight_nonneg _ (paddedGroupWeight_nonneg _ (fun p => by positivity)) _
  · exact prod_nonneg (fun i _ => paddedShapeWeight_nonneg _ (fun p s => localTokenWeight_nonneg w₀ p _) _ _)

lemma flatWeight_nonneg (pC pZ : S.Index) (c : FlatCode S w₀ C₀ B L n N) :
    0 ≤ flatWeight pC pZ c := by
  exact mul_nonneg (exceptionalWeight_nonneg c) (prod_nonneg (fun p _ =>
    factor_nonneg _ _ (fun t p => mul_nonneg (tokenWeight_nonneg _ _ _ _) (slotWeight_nonneg _ _ _)) p))

theorem native_sum_le_gated_code (pC pZ : S.Index) (hpC : S.IsCore pC) (hpZ : ¬S.IsCore pZ) :
    (∑ x : RecordPacket D L w₀ hh r hr₀ n N, x.nativeWeight) ≤
      ∑ c : FlatCode S w₀ C₀ B L n N, if flatGate D.H τ c then flatWeight pC pZ c else 0 := by
  let W := fun c : FlatCode S w₀ C₀ B L n N => if flatGate D.H τ c then flatWeight pC pZ c else 0
  have hx (x : RecordPacket D L w₀ hh r hr₀ n N) : W x.flatCode=x.nativeWeight := by
    rw [show W x.flatCode=flatWeight pC pZ x.flatCode from ite_eq_left x.flatCode_gate,
      flatWeight_code pC pZ hpC hpZ]
  simp_rw [← hx]
  calc
    _ = ∑ c ∈ univ.image flatCode, W c := (sum_image (fun x _ y _ he => flatCode_injective he)).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun c _ _ => by
      unfold W
      split_ifs
      · exact flatWeight_nonneg pC pZ c
      · exact le_rfl)

end RecordPacket
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
