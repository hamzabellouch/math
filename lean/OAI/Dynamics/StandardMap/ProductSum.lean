import OAI.Dynamics.StandardMap.BridgeExist

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open scoped BigOperators
namespace StandardMapEntropy
lemma sum_product_error (s : Finset ℕ) (A B E : ℕ → ℝ) (C ε T : ℝ)
    (hC : 0≤ C) (hε : 0≤ ε)
    (hA : ∀j∈s,0≤ A j) (hB : ∀j∈s,0≤ B j) (hE : ∀j∈s,0≤ E j)
    (hAC : ∀j∈s,A j≤ C*ε) (hBC : ∀j∈s,B j≤ C*ε)
    (hT : (∑j∈s,A j)≤ T*ε ∨ (∑j∈s,B j)≤ T*ε) :
    (∑j∈s,(A j+E j)*B j)≤ C*ε*(T*ε+∑j∈s,E j) := by
  have hp : (∑j∈s,A j*B j)≤ C*ε*(T*ε) := by
    rcases hT with hT|hT
    · calc
        _ ≤ ∑j∈s,A j*(C*ε) := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hBC j hj) (hA j hj))
        _ = (∑j∈s,A j)*(C*ε) := by rw [Finset.sum_mul]
        _ ≤ (T*ε)*(C*ε) := mul_le_mul_of_nonneg_right hT (mul_nonneg hC hε)
        _ = _ := mul_comm _ _
    · calc
        _ ≤ ∑j∈s,(C*ε)*B j := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (hAC j hj) (hB j hj))
        _ = C*ε*(∑j∈s,B j) := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left hT (mul_nonneg hC hε)
  have he : (∑j∈s,E j*B j)≤ C*ε*(∑j∈s,E j) := by
    calc
      _ ≤ ∑j∈s,E j*(C*ε) := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hBC j hj) (hE j hj))
      _ = _ := by rw [←Finset.sum_mul]; ring
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib,mul_add]
  exact add_le_add hp he
end StandardMapEntropy

end OAI
