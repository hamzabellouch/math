import OAI.NumberTheory.TotientAsymptotic.FinitePowerTail
import OAI.NumberTheory.TotientAsymptotic.FiniteDyadicLogTail

namespace OAI

/-! Reciprocal mass of a finite set with a logarithmic power saving in its count. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma finite_dyadic_power_mass (Q : Finset ℕ) (K L : ℕ) (hK : 1 ≤ K)
    {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ)
    (hn : ∀ q ∈ Q,Nat.clog 2 q ∈ Finset.Icc K L)
    (hlo : ∀ q ∈ Q,(2:ℝ)^(Nat.clog 2 q)/4 ≤ q)
    (hcount : ∀ j ∈ Finset.Icc K L,((Q.filter (fun q => Nat.clog 2 q=j)).card:ℝ) ≤
      A*(2:ℝ)^j*(j:ℝ)^(-1-δ)) :
    (∑ q ∈ Q,(q:ℝ)⁻¹) ≤ 4*A*(1+δ⁻¹)*(K:ℝ)^(-δ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hn]
  have hf (j : ℕ) (hj : j ∈ Finset.Icc K L) :
      (∑ q ∈ Q.filter (fun q => Nat.clog 2 q=j),(q:ℝ)⁻¹) ≤ 4*A*(j:ℝ)^(-1-δ) := by
    have hy : (0:ℝ) < 2^j := by positivity
    calc
      _ ≤ ∑ _q ∈ Q.filter (fun q => Nat.clog 2 q=j),4/(2:ℝ)^j := by
        apply Finset.sum_le_sum
        intro q hq
        obtain ⟨hq,he⟩ := Finset.mem_filter.mp hq
        have hh := hlo q hq
        rw [he] at hh
        simpa only [inv_div] using inv_anti₀ (div_pos hy (by norm_num)) hh
      _ = ((Q.filter (fun q => Nat.clog 2 q=j)).card:ℝ)*(4/(2:ℝ)^j) := by simp
      _ ≤ (A*(2:ℝ)^j*(j:ℝ)^(-1-δ))*(4/(2:ℝ)^j) :=
        mul_le_mul_of_nonneg_right (hcount j hj) (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ j ∈ Finset.Icc K L,4*A*(j:ℝ)^(-1-δ) := Finset.sum_le_sum hf
    _ = 4*A*(∑ j ∈ Finset.Icc K L,(j:ℝ)^(-1-δ)) := (Finset.mul_sum ..).symm
    _ ≤ 4*A*((1+δ⁻¹)*(K:ℝ)^(-δ)) :=
      mul_le_mul_of_nonneg_left (finite_power_tail K L hK hδ) (by positivity)
    _ = _ := by ring

lemma finite_dyadic_log_power_tail (Q : Finset ℕ) {U A δ : ℝ}
    (hU : 1 < U) (hA : 0 ≤ A) (hδ : 0 < δ) (hlo : ∀ q ∈ Q,U ≤ q)
    (hc : ∀ j : ℕ,1 ≤ j → ((Q.filter (fun q => Nat.clog 2 q=j)).card:ℝ) ≤
      A*(2:ℝ)^j*(j:ℝ)^(-1-δ)) :
    (∑ q ∈ Q,(q:ℝ)⁻¹) ≤ 4*A*(1+δ⁻¹)*(Real.log U)^(-δ) := by
  classical
  by_cases hQ : Q.Nonempty
  · obtain ⟨K,L,hK,hlog,hn,hv⟩ := finite_dyadic_log_range Q hQ hU hlo
    have hh := finite_dyadic_power_mass Q K L hK hA hδ hn hv
      (fun j hj => hc j (hK.trans (Finset.mem_Icc.mp hj).1))
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hlogU : 0 < Real.log U := Real.log_pos hU
    have hlog2 : Real.log (2:ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hK0 : 0 ≤ (K:ℝ) := Nat.cast_nonneg _
    have hk : Real.log U ≤ K := by nlinarith only [hlog,mul_le_mul_of_nonneg_left hlog2 hK0]
    exact Real.rpow_le_rpow_of_nonpos hlogU hk (by linarith)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hQ,Finset.sum_empty]
    have hlogU : 0 < Real.log U := Real.log_pos hU
    positivity

end TotientAsymptotic

end

end OAI
