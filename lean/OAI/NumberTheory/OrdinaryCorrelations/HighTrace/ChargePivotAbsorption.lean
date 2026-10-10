import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Support
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RecordPacket
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.UntaggedReferenceWeight
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GeometryGoodEdges

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

lemma charge_pivot_absorption (K q : ℝ) (hK : 0 < K) (hK1 : K ≤ 1)
    (hq : Real.exp (-q) ≤ K) (g N U k : ℕ) (hcover : g ≤ N+U+k) :
    Real.exp (-q*(U:ℝ)) ≤ K^(g-N) * (K^k)⁻¹ := by
  rw [← div_eq_mul_inv,le_div_iff₀ (pow_pos hK k)]
  have he : Real.exp (-q*(U:ℝ)) = (Real.exp (-q))^U := by rw [mul_comm,Real.exp_nat_mul]
  rw [he]
  calc
    _ ≤ K^U * K^k := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le hq U) (pow_nonneg hK.le k)
    _ = K^(U+k) := (pow_add ..).symm
    _ ≤ _ := pow_le_pow_of_le_one hK.le hK1 (by omega)

namespace RecordPacket
variable {w₀ : ClosedLine h ℓ} {hh : 0 < h} {r : ℕ}
variable {hr₀ : (returnSteps w₀).card=r} {n N : ℕ}

noncomputable def chargedWeight (q : ℝ) (x : RecordPacket D L w₀ hh r hr₀ n N) : ℝ :=
  Real.exp (-q*((recordU x.line x.record.1).card:ℝ)) * x.nativeWeight

noncomputable def chargedCodeWeight (K : ℝ) (pC pZ : S.Index)
    (c : FlatCode S w₀ C₀ B L n N) : ℝ :=
  if flatGate D.H τ c then (K^(flatPivots c))⁻¹ * flatWeight pC pZ c else 0

lemma chargedCodeWeight_nonneg (K : ℝ) (hK : 0 ≤ K) (pC pZ : S.Index)
    (c : FlatCode S w₀ C₀ B L n N) : 0 ≤ chargedCodeWeight (D := D) K pC pZ c := by
  unfold chargedCodeWeight
  split_ifs
  · exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hK _)) (flatWeight_nonneg pC pZ c)
  · exact le_rfl

lemma chargedWeight_le_code (K q : ℝ) (hK : 0 < K) (hK1 : K ≤ 1)
    (hq : Real.exp (-q) ≤ K) (pC pZ : S.Index) (hpC : S.IsCore pC) (hpZ : ¬S.IsCore pZ)
    (x : RecordPacket D L w₀ hh r hr₀ n N) :
    chargedWeight q x ≤ K^((goodEdges w₀).card-N) * chargedCodeWeight (D := D) K pC pZ x.flatCode := by
  have hab := charge_pivot_absorption K q hK hK1 hq (goodEdges w₀).card N
    (recordU x.line x.record.1).card (flatPivots x.flatCode) x.flatCode_good_cover
  unfold chargedWeight chargedCodeWeight
  rw [ite_eq_left x.flatCode_gate,← flatWeight_code pC pZ hpC hpZ x]
  exact (mul_le_mul_of_nonneg_right hab (flatWeight_nonneg pC pZ x.flatCode)).trans_eq (mul_assoc ..)

theorem charged_record_sum_le_codes (K q : ℝ) (hK : 0 < K) (hK1 : K ≤ 1)
    (hq : Real.exp (-q) ≤ K) (pC pZ : S.Index) (hpC : S.IsCore pC) (hpZ : ¬S.IsCore pZ) :
    (∑ x : RecordPacket D L w₀ hh r hr₀ n N, chargedWeight q x) ≤
      K^((goodEdges w₀).card-N) *
        ∑ c : FlatCode S w₀ C₀ B L n N, chargedCodeWeight (D := D) K pC pZ c := by
  have hsum : (∑ x : RecordPacket D L w₀ hh r hr₀ n N, chargedCodeWeight (D := D) K pC pZ x.flatCode) ≤
      ∑ c : FlatCode S w₀ C₀ B L n N, chargedCodeWeight (D := D) K pC pZ c := by
    calc
      _ = ∑ c ∈ univ.image flatCode, chargedCodeWeight (D := D) K pC pZ c :=
        (sum_image (fun x _ y _ he => flatCode_injective he)).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun c _ _ => chargedCodeWeight_nonneg K hK.le pC pZ c)
  calc
    _ ≤ ∑ x : RecordPacket D L w₀ hh r hr₀ n N,
        K^((goodEdges w₀).card-N) * chargedCodeWeight (D := D) K pC pZ x.flatCode :=
      sum_le_sum (fun x _ => chargedWeight_le_code K q hK hK1 hq pC pZ hpC hpZ x)
    _ = _ := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (pow_nonneg hK.le _)

end RecordPacket
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
