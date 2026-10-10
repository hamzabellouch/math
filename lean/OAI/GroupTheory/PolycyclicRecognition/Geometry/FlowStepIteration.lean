import OAI.GroupTheory.PolycyclicRecognition.Geometry.ContinuousFlowAffinity
import Mathlib.Algebra.Order.Archimedean.Basic

namespace OAI

/-! # Small constant flow increments imply constancy on an entire segment -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G V W : Type*} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem eq_on_positive_flow_of_small_steps
    (f : G → W) (U : Set G) (Exp : V → G) (hExp0 : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) {T : ℝ} (hT : 0 < T)
    (hstep : ∀ g ∈ U, ∀ s ∈ Icc 0 T, f (g * Exp (s • v)) = f g)
    {g : G} {t : ℝ} (ht : 0 ≤ t)
    (hstay : g ∈ flowLineBase U Exp (t • v) 1) : f (g * Exp (t • v)) = f g := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (t / T) 0)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (le_max_right _ _) hn
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  have hδ : t / n ∈ Icc (0 : ℝ) T := by
    refine ⟨div_nonneg ht hnpos.le, (div_le_iff₀ hnpos).mpr ?_⟩
    have hlt : t / T < n := lt_of_le_of_lt (le_max_left _ _) hn
    exact (le_of_lt ((div_lt_iff₀ hT).mp hlt)).trans_eq (mul_comm _ _)
  have he (k : ℕ) (hk : k ≤ n) : f (g * Exp (((k : ℝ) * (t / n)) • v)) = f g := by
    induction k with
    | zero => simp [hExp0]
    | succ k ih =>
      have hk' : k ≤ n := (Nat.le_succ k).trans hk
      have hbase : g * Exp (((k : ℝ) * (t / n)) • v) ∈ U := by
        have hr : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 := by
          refine ⟨div_nonneg (Nat.cast_nonneg k) hnpos.le, ?_⟩
          exact (div_le_one hnpos).mpr (by exact_mod_cast hk')
        have h := hstay ((k : ℝ) / n) hr
        simpa only [smul_smul, div_mul_eq_mul_div, mul_div_assoc] using h
      have hs := hstep _ hbase _ hδ
      rw [mul_assoc, ← hadd] at hs
      have hnum : (k : ℝ) * (t / n) + t / n = ((k + 1 : ℕ) : ℝ) * (t / n) := by
        push_cast
        ring
      rw [hnum] at hs
      exact hs.trans (ih hk')
  have h := he n le_rfl
  have hcancel : (n : ℝ) * (t / n) = t := by field_simp
  simpa only [hcancel] using h

theorem eq_on_flow_of_small_steps
    (f : G → W) (U : Set G) (Exp : V → G) (hExp0 : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) {T : ℝ} (hT : 0 < T)
    (hstep : ∀ g ∈ U, ∀ s ∈ Icc 0 T, f (g * Exp (s • v)) = f g)
    {g : G} {t : ℝ} (hstay : g ∈ flowLineBase U Exp (t • v) 1) :
    f (g * Exp (t • v)) = f g := by
  by_cases ht : 0 ≤ t
  · exact eq_on_positive_flow_of_small_steps f U Exp hExp0 hadd v hT hstep ht hstay
  · have ht' : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
    have hback : g * Exp (t • v) ∈ flowLineBase U Exp ((-t) • v) 1 := by
      intro r hr
      have h := hstay (1 - r) (show 1 - r ∈ Icc (0 : ℝ) 1 by
        constructor <;> linarith [hr.1, hr.2])
      have he : (g * Exp (t • v)) * Exp (r • ((-t) • v)) =
          g * Exp ((1 - r) • (t • v)) := by
        have hscalar : t + r * (-t) = (1 - r) * t := by ring
        rw [smul_smul, smul_smul, mul_assoc, ← hadd, hscalar]
      rwa [he]
    have h := eq_on_positive_flow_of_small_steps f U Exp hExp0 hadd v hT hstep ht' hback
    have he : (g * Exp (t • v)) * Exp ((-t) • v) = g := by
      rw [mul_assoc, ← hadd]
      simp [hExp0]
    rw [he] at h
    exact h.symm

end PolycyclicRecognition

end

end OAI
