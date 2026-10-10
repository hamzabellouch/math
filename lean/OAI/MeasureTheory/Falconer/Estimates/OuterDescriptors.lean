import OAI.MeasureTheory.Falconer.Graphs.PolicyGraphAt

namespace OAI

/-! # The single additional parallel descriptor at the assembly entry -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)
attribute [local instance] Classical.propDecidable

namespace PolicyJetData
variable {m : ℕ}

noncomputable def outerList (P : PolicyJetData m) (c : ℕ) : Finset PolicyDescriptor :=
  insert (.parallel 0 c) P.list

noncomputable def outerLongest (P : PolicyJetData m) (c : ℕ) : ℕ :=
  (P.outerList c).sup descriptorLength

theorem outerList_card (P : PolicyJetData m) (c : ℕ) :
    (P.outerList c).card ≤ (P.N+1)^4 := by
  have hN := P.N_pos
  have hbase := P.list_card
  have hcard := Finset.card_insert_le (.parallel 0 c) P.list
  have hone : 1 ≤ (P.N+1)^3 := one_le_pow₀ (by omega)
  have hpow : (P.N+1)^3+1 ≤ (P.N+1)^4 := by
    calc
      _ ≤ (P.N+1)^3+(P.N+1)^3 := by omega
      _ ≤ (P.N+1)^3*(P.N+1) := by nlinarith
      _ = _ := by ring
  exact hcard.trans ((Nat.add_le_add_right hbase 1).trans hpow)

theorem outerLongest_half (P : PolicyJetData m) {c : ℕ} (hc : 2*c ≤ P.N) :
    2*P.outerLongest c ≤ P.N := by
  have hlength (b) (hb : b ∈ P.outerList c) : descriptorLength b ≤ P.N/2 := by
    obtain rfl | hb := Finset.mem_insert.mp hb
    · simp only [descriptorLength,Nat.sub_zero]
      omega
    · have hp := PlanarFalconer.policyDescriptor_twice_length P.policy P.q_pos
        (Finset.mem_filter.mp hb).1
      have hN := P.base_N
      omega
  have hsup : P.outerLongest c ≤ P.N/2 := Finset.sup_le hlength
  omega

theorem outerList_drop (P : PolicyJetData m) {c : ℕ} (hc : P.a ≤ c) :
    (P.outerList c).filter (fun b => c < descriptorAnchor b) =
      PlanarFalconer.remainingPolicyDescriptors P.policy P.N P.q P.a₀ P.t₀ c := by
  rw [outerList,Finset.filter_insert]
  simp only [descriptorAnchor,lt_self_iff_false,ite_false]
  exact PlanarFalconer.remainingPolicyDescriptors_drop P.policy P.N P.q P.a₀ P.t₀ hc

theorem outer_geometry (P : PolicyJetData m) {c : ℕ} (ha : P.a = 0) (ht : P.t = P.N)
    (hc : 4*c ≤ P.N) (hσ : 0 ≤ P.σ) (hσsmall : P.σ ≤ 1/100) :
    (c:ℝ)-P.a ≤ (P.t:ℝ)-c+2*P.σ*P.N ∧
    (P.outerLongest c:ℝ) ≤ (P.t:ℝ)-c+2*P.σ*P.N ∧
    10*P.σ*P.N ≤ (P.t:ℝ)-c := by
  have hcr : 4*(c:ℝ) ≤ P.N := by exact_mod_cast hc
  have hlong : 2*(P.outerLongest c:ℝ) ≤ P.N := by
    exact_mod_cast P.outerLongest_half (by omega : 2*c ≤ P.N)
  have hσN := mul_nonneg hσ (Nat.cast_nonneg P.N)
  have hsmall := mul_le_mul_of_nonneg_right hσsmall (Nat.cast_nonneg P.N : (0:ℝ) ≤ P.N)
  rw [ha,ht]
  push_cast
  constructor
  · nlinarith
  constructor <;> nlinarith

end PolicyJetData
end Falconer

end OAI
