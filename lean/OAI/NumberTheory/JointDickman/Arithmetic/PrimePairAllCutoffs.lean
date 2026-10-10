import OAI.NumberTheory.JointDickman.Arithmetic.PrimePairUpperBound

namespace OAI

/-! # Extending the prime-pair sieve estimate to every cutoff -/
namespace JointDickman
open Filter Finset

theorem primePair_count_le (Q h : ℕ) : primePairCount Q h ≤ Q+1 := by
  classical
  exact (card_filter_le _ _).trans_eq (by simp)

/-- The uniform prime-pair upper sieve, at every integer cutoff at least two. -/
theorem primePair_upper_sieve : ∃ C : ℝ, 0 < C ∧
    ∀ Q h : ℕ, 2 ≤ Q → 0 < h →
      (primePairCount Q h:ℝ) ≤ C*((h:ℝ)/h.totient)*(Q:ℝ)/(Real.log Q)^2 := by
  obtain ⟨C,hC,hbound⟩ := primePair_count_log_bound
  obtain ⟨Q₀,hQ₀⟩ := eventually_atTop.mp hbound
  let K : ℕ := max 2 Q₀
  let D : ℝ := C+2*(Real.log K)^2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro Q h hQ hh
  have hφ : (0:ℝ) < h.totient := by exact_mod_cast Nat.totient_pos.mpr hh
  have hw : 1 ≤ (h:ℝ)/h.totient := (one_le_div hφ).mpr (by exact_mod_cast Nat.totient_le h)
  have hlogQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hQR : (0:ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  by_cases hlarge : K ≤ Q
  · have hb := hQ₀ Q ((le_max_right _ _).trans hlarge) h hh
    apply hb.trans
    have hCD : C ≤ D := by
      dsimp [D]
      exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (sq_nonneg _))
    gcongr
  · have hQK : (Q:ℝ) ≤ K := by exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hlarge))
    have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast (show 1 ≤ K by dsimp [K]; omega))
    have hlogle := Real.log_le_log hQR hQK
    have hsq : 2*(Real.log Q)^2 ≤ D := by dsimp [D]; nlinarith
    have hcoef : 2*(Real.log Q)^2 ≤ D*((h:ℝ)/h.totient) :=
      hsq.trans (le_mul_of_one_le_right hD.le hw)
    calc
      (primePairCount Q h:ℝ) ≤ Q+1 := by exact_mod_cast primePair_count_le Q h
      _ ≤ 2*(Q:ℝ) := by
        have hQr : (2:ℝ) ≤ Q := by exact_mod_cast hQ
        linarith
      _ ≤ _ := by
        apply (le_div_iff₀ (sq_pos_of_pos hlogQ)).mpr
        nlinarith [mul_le_mul_of_nonneg_right hcoef hQR.le]

end JointDickman

end OAI
