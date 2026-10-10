import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteLaplaceDensity

namespace OAI

/-! # Rapid Mellin decay summed against an ordinary zero count -/

namespace Ostmann
open scoped Classical BigOperators

theorem zero_height_log_count {ι : Type*} (S : Finset ι) (h : ι → ℝ)
    (Q K : ℝ) (hQ : 1 ≤ Q) (hK : 0 ≤ K) (hh : ∀ i ∈ S, 0 ≤ h i)
    (hcount : ∀ t : ℝ, 0 ≤ t →
      ((S.filter (fun i => h i ≤ t)).card : ℝ) ≤ K * (t + 1) * Real.log (Q * (t + 2))) :
    ∀ s : ℝ, 0 ≤ s →
      ((S.filter (fun i => Real.log (1 + h i) ≤ s)).card : ℝ) ≤
        (2 * K * (Real.log Q + 3)) * Real.exp (2 * s) := by
  intro s hs
  have hQp : 0 < Q := by linarith
  have he : 1 ≤ Real.exp s := Real.one_le_exp hs
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hsub : S.filter (fun i => Real.log (1 + h i) ≤ s) ⊆
      S.filter (fun i => h i ≤ Real.exp s) := by
    intro i hi
    obtain ⟨hiS, hi⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨hiS, ?_⟩
    have hpos : 0 < 1 + h i := by linarith [hh i hiS]
    have hex := (Real.log_le_iff_le_exp hpos).mp hi
    linarith
  have hlog : Real.log (Q * (Real.exp s + 2)) ≤ (Real.log Q + 3) * Real.exp s := by
    rw [Real.log_mul hQp.ne' (by positivity : Real.exp s + 2 ≠ 0)]
    have he2 : 3 ≤ Real.exp (2 : ℝ) := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have hinside : Real.exp s + 2 ≤ Real.exp (s + 2) := by
      rw [Real.exp_add]
      nlinarith
    have hl := Real.log_le_log (by positivity : 0 < Real.exp s + 2) hinside
    rw [Real.log_exp] at hl
    have hq := mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ Real.log Q + 2)
    have hs' := Real.add_one_le_exp s
    nlinarith
  have hlog0 : 0 ≤ Real.log (Q * (Real.exp s + 2)) :=
    Real.log_nonneg (by nlinarith)
  calc
    _ ≤ ((S.filter (fun i => h i ≤ Real.exp s)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ K * (Real.exp s + 1) * Real.log (Q * (Real.exp s + 2)) :=
      hcount (Real.exp s) (Real.exp_nonneg _)
    _ ≤ (K * (2 * Real.exp s)) * ((Real.log Q + 3) * Real.exp s) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (by linarith) hK
      · exact hlog
      · exact hlog0
      · positivity
    _ = (2 * K * (Real.log Q + 3)) * Real.exp (2 * s) := by
      rw [show 2 * s = s + s by ring, Real.exp_add]
      ring

theorem finite_high_zero_tail_bound {ι : Type*} (S : Finset ι) (h : ι → ℝ)
    (Q K T : ℝ) (hQ : 1 ≤ Q) (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hh : ∀ i ∈ S, T ≤ h i)
    (hcount : ∀ t : ℝ, 0 ≤ t →
      ((S.filter (fun i => h i ≤ t)).card : ℝ) ≤ K * (t + 1) * Real.log (Q * (t + 2))) :
    (∑ i ∈ S, Real.exp (-8 * Real.log (1 + h i))) ≤
      2 * (2 * K * (Real.log Q + 3)) ^ 2 * Real.exp (-4 * Real.log (1 + T)) := by
  have hh0 (i) (hi : i ∈ S) : 0 ≤ h i := hT.trans (hh i hi)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hu : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
  have hh' := finite_laplace_density_bound S (fun i => Real.log (1 + h i)) 2
    (2 * K * (Real.log Q + 3)) 8 (Real.log (1 + T)) (by norm_num) (by positivity)
    (by norm_num) hu
    (fun i hi => Real.log_le_log (by linarith : 0 < 1 + T) (by linarith [hh i hi]))
    (zero_height_log_count S h Q K hQ hK hh0 hcount)
  rw [show -(8 * Real.log (1 + T)) / 2 = -4 * Real.log (1 + T) by ring] at hh'
  exact hh'

end Ostmann

end OAI
