import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCompactCutoff

namespace OAI

/-! # One finite support for every scale in the parameter grid -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadraticCompactCutoff_mono (q N : ℕ) (R Rmax v H : ℝ)
    (hR : R ≤ Rmax) (hv : 0 ≤ v) (hH : 0 ≤ H) :
    quadraticCompactCutoff q R v H N ⊆ quadraticCompactCutoff q Rmax v H N := by
  unfold quadraticCompactCutoff
  apply Finset.Ioc_subset_Ioc le_rfl
  apply Nat.floor_mono
  apply Real.sqrt_le_sqrt
  gcongr

theorem positiveQuadraticSum_eq_upper_cutoff {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R Rmax v H : ℝ) (s : ℕ) (hR : 0 < R) (hRmax : R ≤ Rmax)
    (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    positiveQuadraticSum g a θ Φ R v s =
      quadraticDensitySum g (quadraticCompactCutoff q Rmax v H s) a θ Φ R v s := by
  classical
  unfold positiveQuadraticSum quadraticDensitySum
  congr 1
  calc
    _ = ∑ w ∈ quadraticCompactCutoff q Rmax v H s,
        if 0 < w then quadraticDensityTerm g a θ Φ R v s w else 0 := by
      apply tsum_eq_sum
      intro w hw
      by_cases hw0 : 0 < w
      · simp only [ite_eq_left hw0]
        by_contra hn
        exact hw (quadraticCompactCutoff_mono q s R Rmax v H hRmax hv.le hH
          (quadraticDensityTerm_mem_cutoff g a θ Φ R v H s s w hR hv hs le_rfl hw0 hΦ hn))
      · simp only [ite_eq_right hw0]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      exact ite_eq_left (Finset.mem_Ioc.mp hw).1

end Ostmann

end OAI
