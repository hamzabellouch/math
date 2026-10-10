import OAI.Probability.GammaPassage.GridMeshes
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge
open Filter Finset
open scoped Topology

noncomputable def endpointErrorTerm (j : ℕ) : ℝ := (j : ℝ)^2*(1/2 : ℝ)^j
noncomputable def endpointErrorTail (J : ℕ) : ℝ := ∑' n : ℕ,endpointErrorTerm (n+J)

lemma endpointErrorTerm_nonneg (j : ℕ) : 0 ≤ endpointErrorTerm j := by
  unfold endpointErrorTerm
  positivity

lemma summable_endpointErrorTerm : Summable endpointErrorTerm := by
  exact summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num : ‖(1/2 : ℝ)‖ < 1)

lemma endpointErrorTail_tendsto : Tendsto endpointErrorTail atTop (𝓝 0) :=
  tendsto_sum_nat_add endpointErrorTerm

lemma endpointErrorTail_nonneg (J : ℕ) : 0 ≤ endpointErrorTail J :=
  tsum_nonneg (fun _ => endpointErrorTerm_nonneg _)

lemma endpointErrorTerm_le_two (j : ℕ) : endpointErrorTerm j ≤ 2 := by
  have h (n : ℕ) : (n : ℝ)^2 ≤ 2*(2 : ℝ)^n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < 4
      · interval_cases n <;> norm_num
      · obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ n by omega)
        have ha : (3 : ℝ) ≤ a := by exact_mod_cast (show 3 ≤ a by omega)
        have hb := ih a (by omega)
        simp only [Nat.cast_add,Nat.cast_one,pow_add,pow_one]
        nlinarith
  have hp := mul_le_mul_of_nonneg_right (h j) (show 0 ≤ (1/2 : ℝ)^j by positivity)
  have he : (2 : ℝ)^j*(1/2 : ℝ)^j=1 := by rw [← mul_pow]; norm_num
  unfold endpointErrorTerm
  nlinarith

lemma gridWidth_endpointError (k j : ℕ) (hj : j ≤ k) :
    (j : ℝ)^2*(gridWidth k j : ℝ)=(2 : ℝ)^k*endpointErrorTerm j := by
  have he : (2 : ℝ)^k=(2 : ℝ)^(k-j)*(2 : ℝ)^j := by rw [← pow_add,Nat.sub_add_cancel hj]
  have hc : (2 : ℝ)^j*(1/2 : ℝ)^j=1 := by rw [← mul_pow]; norm_num
  simp only [endpointErrorTerm,gridWidth,Int.cast_pow,Int.cast_ofNat]
  rw [he]
  calc
    _ = (2 : ℝ)^(k-j)*(j : ℝ)^2*((2 : ℝ)^j*(1/2 : ℝ)^j) := by rw [hc]; ring
    _ = _ := by ring

lemma endpointError_sum_le_tail (J n : ℕ) :
    (∑ i ∈ range n,endpointErrorTerm (J+i)) ≤ endpointErrorTail J := by
  have hs : Summable (fun i : ℕ => endpointErrorTerm (i+J)) := summable_endpointErrorTerm.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  simpa [endpointErrorTail,Nat.add_comm] using
    hs.sum_le_tsum (range n) (fun i _ => endpointErrorTerm_nonneg (i+J))

end GammaFPP.CrossingBridge

end OAI
