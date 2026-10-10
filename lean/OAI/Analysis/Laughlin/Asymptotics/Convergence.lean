import Mathlib.Analysis.Normed.Group.Tannery
import OAI.Analysis.Laughlin.Asymptotics.Limit

namespace OAI

namespace Laughlin
open scoped BigOperators Topology
open Filter
noncomputable section

def deltaTerm (Q m : ℕ) : ℝ :=
  if 17+2*m ≤ Q then tailWeight Q (17+2*m) else 0

def deltaFormula (Q : ℕ) : ℝ := ∑' m, deltaTerm Q m

theorem odd_tail_index_iff (z : ℕ) : (17 ≤ z ∧ Odd z) ↔ ∃ m : ℕ, z = 17+2*m := by
  constructor
  · rintro ⟨hz, k, hk⟩
    exact ⟨k-8, by omega⟩
  · rintro ⟨m, rfl⟩
    exact ⟨by omega, ⟨8+m, by omega⟩⟩

theorem deltaFormula_eq_finite_sum (Q : ℕ) :
    deltaFormula Q = ∑ m ∈ Finset.range (Q+1), deltaTerm Q m := by
  apply tsum_eq_sum
  intro m hm
  have hn : ¬ 17+2*m ≤ Q := by
    simp only [Finset.mem_range] at hm
    omega
  simp [deltaTerm, hn]

theorem tailWeight_nonneg {Q z : ℕ} (hQ : 4 ≤ Q) (hz : z ≤ Q) :
    0 ≤ tailWeight Q z := by
  have hQr : (4 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hzQr : (z : ℝ) ≤ Q := by exact_mod_cast hz
  unfold tailWeight
  apply mul_nonneg
  · apply mul_nonneg
    · exact div_nonneg (by linarith) (by linarith)
    · exact abs_nonneg _
  · positivity

theorem tailWeight_tendsto (z : ℕ) (hz : 16 ≤ z) :
    Tendsto (fun Q : ℕ => tailWeight Q z) atTop
      (𝓝 ((3/2 : ℝ)*(3*(z : ℝ)-1)*(1/2 : ℝ)^z*((z : ℝ)+1))) := by
  have hd := tendsto_add_mul_div_add_mul_atTop_nhds
    (-1-2*(z : ℝ)) (-1 : ℝ) 3 (d := 2) (by norm_num)
  have hh := (hd.mul (gramEigenvalueFormula_tendsto z).abs).mul_const ((z : ℝ)+1)
  have hzR : (16 : ℝ) ≤ z := by exact_mod_cast hz
  have he : (3/2 : ℝ)*|(3*(z : ℝ)-1)*(-1/2 : ℝ)^z| *((z : ℝ)+1) =
      (3/2 : ℝ)*(3*(z : ℝ)-1)*(1/2 : ℝ)^z*((z : ℝ)+1) := by
    rw [abs_mul, abs_pow, abs_of_nonneg (by linarith : 0 ≤ 3*(z : ℝ)-1)]
    norm_num only [abs_div, abs_neg, abs_one]
    ring
  rw [he] at hh
  convert! hh using 1
  ext Q
  unfold tailWeight
  congr 2
  ring

theorem deltaTerm_tendsto (m : ℕ) :
    Tendsto (fun Q : ℕ => deltaTerm Q m) atTop
      (𝓝 ((3/2 : ℝ)*(3*(17+2*(m : ℝ))-1)*(18+2*(m : ℝ))*
        (1/2 : ℝ)^(17+2*m))) := by
  have hh := tailWeight_tendsto (17+2*m) (by omega)
  have he : (fun Q => tailWeight Q (17+2*m)) =ᶠ[atTop]
      (fun Q => deltaTerm Q m) := by
    filter_upwards [eventually_ge_atTop (17+2*m)] with Q hQ
    simp [deltaTerm, hQ]
  have ht := hh.congr' he
  have hval : (3/2 : ℝ)*(3*((17+2*m : ℕ) : ℝ)-1)*(1/2 : ℝ)^(17+2*m)*
      (((17+2*m : ℕ) : ℝ)+1) =
      (3/2 : ℝ)*(3*(17+2*(m : ℝ))-1)*(18+2*(m : ℝ))*(1/2 : ℝ)^(17+2*m) := by
    push_cast
    ring
  simpa only [hval] using ht

theorem deltaFormula_tendsto :
    Tendsto deltaFormula atTop (𝓝 (61/4096 : ℝ)) := by
  let bound : ℕ → ℝ := fun m =>
    6*((17+2*m : ℕ) : ℝ)*(((17+2*m : ℕ) : ℝ)+1)*(2/3 : ℝ)^(17+2*m)
  have hinj : Function.Injective (fun m : ℕ => 17+2*m) := by
    intro a b hab
    change 17+2*a = 17+2*b at hab
    omega
  have hb : Summable bound := tail_majorant_summable.comp_injective hinj
  have hbound : ∀ Q m, ‖deltaTerm Q m‖ ≤ bound m := by
    intro Q m
    unfold deltaTerm
    split_ifs with hQ
    · rw [Real.norm_eq_abs, abs_of_nonneg (tailWeight_nonneg (by omega) hQ)]
      exact tailWeight_le (by omega) (by omega) hQ
    · simp only [norm_zero]
      dsimp [bound]
      positivity
  have hh := tendsto_tsum_of_dominated_convergence hb deltaTerm_tendsto
    (Eventually.of_forall hbound)
  rw [tail_series_value.tsum_eq] at hh
  exact hh

end
end Laughlin

end OAI
