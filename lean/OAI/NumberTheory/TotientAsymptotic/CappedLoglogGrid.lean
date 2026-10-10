import OAI.NumberTheory.TotientAsymptotic.LoglogGrid

namespace OAI

/-! Cap the log-log grid at the upper sieve endpoint. -/
noncomputable section
namespace TotientAsymptotic

def cappedLoglogIndex (K : ℕ) (t : ℝ) : ℕ := min (⌊t⌋₊-1) K

lemma cappedLoglogIndex_mono (K : ℕ) : Monotone (cappedLoglogIndex K) := by
  intro t u htu
  exact min_le_min (Nat.sub_le_sub_right (Nat.floor_mono htu) 1) le_rfl

lemma cappedLoglogIndex_bounds {K : ℕ} {t U : ℝ} (hK : 2 ≤ K) (hKU : (K:ℝ) ≤ U)
    (ht : 4 ≤ t) (hU : t ≤ U) :
    2 ≤ cappedLoglogIndex K t ∧ cappedLoglogIndex K t ≤ K ∧
      (cappedLoglogIndex K t:ℝ) < t ∧ t-U+K-2 ≤ cappedLoglogIndex K t := by
  have hj := loglog_grid_index_bounds ht
  refine ⟨le_min hj.1 hK,min_le_right _ _,?_,?_⟩
  · exact (by exact_mod_cast (min_le_left (⌊t⌋₊-1) K) :
      (cappedLoglogIndex K t:ℝ) ≤ (⌊t⌋₊-1:ℕ)).trans_lt hj.2.1
  · by_cases hk : K ≤ ⌊t⌋₊-1
    · rw [cappedLoglogIndex,min_eq_right hk]
      linarith
    · have hk' : ⌊t⌋₊-1 ≤ K := by omega
      rw [cappedLoglogIndex,min_eq_left hk']
      linarith [hj.2.2]

lemma capped_loglog_prime {K p : ℕ} {U : ℝ} (hK : 2 ≤ K)
    (hKU : (K:ℝ) ≤ U) (hp : 1 < p) (ht : 4 ≤ B p) (hU : B p ≤ U) :
    let j := cappedLoglogIndex K (B p)
    2 ≤ j ∧ j ≤ K ∧ loglogCutoff j < p ∧
      B p-U+K-3 ≤ B (loglogCutoff j) ∧ B (loglogCutoff j) ≤ K ∧
      Real.log (loglogCutoff j) ≤ Real.exp K := by
  have hj := cappedLoglogIndex_bounds hK hKU ht hU
  have hb := loglogCutoff_bounds (by exact_mod_cast hj.1 : (2:ℝ) ≤ cappedLoglogIndex K (B p))
  dsimp only
  refine ⟨hj.1,hj.2.1,loglogCutoff_lt_of_lt_B hp hj.2.2.1,?_,?_,?_⟩
  · linarith only [hj.2.2.2,hb.2.1]
  · exact hb.2.2.1.trans (by exact_mod_cast hj.2.1)
  · exact hb.2.2.2.trans (Real.exp_le_exp.mpr (by exact_mod_cast hj.2.1))

lemma cappedLoglogIndex_lower {K L : ℕ} {t : ℝ} (hLK : L ≤ K)
    (hLt : (L:ℝ)+1 ≤ t) : L ≤ cappedLoglogIndex K t := by
  apply le_min _ hLK
  have hfloor : L+1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast hLt)
  omega

end TotientAsymptotic

end

end OAI
