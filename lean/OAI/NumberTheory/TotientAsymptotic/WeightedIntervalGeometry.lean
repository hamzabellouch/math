import OAI.NumberTheory.TotientAsymptotic.WeightPerturbation

namespace OAI

noncomputable section
namespace TotientAsymptotic

lemma intervalLength_lipschitz {l u v : ℝ} (huv : v ≤ u) (hvu : u ≤ v+1) :
    |(u-min l u)-(v-min l v)| ≤ 1 := by
  by_cases hlv : l ≤ v
  · rw [min_eq_left hlv,min_eq_left (hlv.trans huv)]
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hvl := (not_le.mp hlv).le
    rw [min_eq_right hvl]
    by_cases hlu : l ≤ u
    · rw [min_eq_left hlu,abs_of_nonneg (by linarith)]
      linarith
    · rw [min_eq_right (not_le.mp hlu).le]
      norm_num

lemma shifted_interval_length {T U r : ℝ} (hT : 0 < T) (hU : 0 ≤ U)
    (_hr : 0 < r) (he : U=T/r) (k : ℕ) :
    |(min (T+1) ((k+1 : ℝ)*U)-min ((k : ℝ)*U) (min (T+1) ((k+1 : ℝ)*U)))-
      T*fk k r| ≤ 1 := by
  have hlc : (k : ℝ)*U ≤ (k+1 : ℝ)*U := by nlinarith
  have hm : min ((k : ℝ)*U) (min T ((k+1 : ℝ)*U)) = min T ((k : ℝ)*U) := by
    rw [← min_assoc,min_comm ((k : ℝ)*U) T,min_assoc,min_eq_left hlc]
  have hf : T*fk k r=min T ((k+1 : ℝ)*U)-min T ((k : ℝ)*U) := by
    rw [fk,mul_sub,mul_min_of_nonneg _ _ hT.le,mul_min_of_nonneg _ _ hT.le]
    rw [mul_one]
    rw [he]
    congr 2 <;> ring
  have hlow : min T ((k+1 : ℝ)*U) ≤ min (T+1) ((k+1 : ℝ)*U) :=
    min_le_min_right _ (by linarith)
  have hhigh : min (T+1) ((k+1 : ℝ)*U) ≤ min T ((k+1 : ℝ)*U)+1 := by
    by_cases hc : T ≤ (k+1 : ℝ)*U
    · rw [min_eq_left hc]
      exact min_le_left _ _
    · rw [min_eq_right (not_le.mp hc).le]
      exact (min_le_right _ _).trans (by linarith)
  rw [hf,← hm]
  exact intervalLength_lipschitz hlow hhigh

end TotientAsymptotic

end

end OAI
