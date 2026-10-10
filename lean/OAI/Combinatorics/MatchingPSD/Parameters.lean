import OAI.Combinatorics.MatchingPSD.Padding

namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing MatchingInterpolation Matrix Filter Asymptotics
open scoped BigOperators MatrixOrder

def blockSize (d t : ℕ) : ℕ := 4*(d+1)*t^4
def vertexSize (d t : ℕ) : ℕ := 2*blockSize d t*(t+2)+2

lemma index_le_vertexSize (d t : ℕ) : t ≤ vertexSize d t := by
  have ht : t ≤ t^4 := Nat.le_pow (by decide)
  have hc : 1 ≤ 8*(d+1)*(t+2) := by
    have : 0 < 8*(d+1)*(t+2) := by positivity
    omega
  calc
    t ≤ t^4 := ht
    _ ≤ (8*(d+1)*(t+2))*t^4 := by simpa only [one_mul] using Nat.mul_le_mul_right (t^4) hc
    _ ≤ vertexSize d t := by dsimp [vertexSize, blockSize]; nlinarith

lemma vertexSize_succ_bound (d t : ℕ) (ht : 1 ≤ t) :
    vertexSize d (t+1) ≤ 1024*(d+1)*t^5 := by
  have hp : 1 ≤ (d+1)*t^5 := by
    have : 0 < (d+1)*t^5 := by positivity
    omega
  calc
    _ = 8*(d+1)*(t+1)^4*(t+3)+2 := by dsimp [vertexSize, blockSize]; ring
    _ ≤ 8*(d+1)*(2*t)^4*(4*t)+2 := by gcongr <;> omega
    _ = 512*(d+1)*t^5+2 := by ring
    _ ≤ _ := by nlinarith

lemma vertexSize_succ_le_pow6 (d t : ℕ) (ht : 1 ≤ t) (hd : 1024*(d+1) ≤ t) :
    vertexSize d (t+1) ≤ t^6 := by
  calc
    _ ≤ 1024*(d+1)*t^5 := vertexSize_succ_bound d t ht
    _ ≤ t*t^5 := Nat.mul_le_mul_right _ hd
    _ = _ := by ring

lemma bracket_vertexSize (d T n : ℕ) (hn : vertexSize d T ≤ n) :
    ∃ t : ℕ, T ≤ t ∧ vertexSize d t ≤ n ∧ n < vertexSize d (t+1) := by
  classical
  let P := fun t => vertexSize d t ≤ n
  let t := Nat.findGreatest P n
  have hT : T ≤ n := (index_le_vertexSize d T).trans hn
  refine ⟨t, Nat.le_findGreatest (P := P) hT hn, Nat.findGreatest_spec (P := P) hT hn, ?_⟩
  by_contra h
  have hnext : P (t+1) := le_of_not_gt h
  have htn : t+1 ≤ n := (index_le_vertexSize d (t+1)).trans hnext
  exact (Nat.findGreatest_eq_iff.mp (show Nat.findGreatest P n=t from rfl)).2.2
    (Nat.lt_succ_self t) htn hnext

lemma exists_padded_global_equiv {n s q : ℕ} (hn : Even n) (hle : 2*s*(q+2)+2 ≤ n) :
    ∃ k : ℕ, Nonempty ((GlobalVertices s q ⊕ (Fin k × Bool)) ≃ Fin n) := by
  have hg : Even (2*s*(q+2)+2) := ⟨s*(q+2)+1, by ring⟩
  have hd : Even (n-(2*s*(q+2)+2)) := (Nat.even_sub hle).mpr ⟨fun _ => hg, fun _ => hn⟩
  obtain ⟨k,hk⟩ := hd
  refine ⟨k, ⟨Fintype.equivOfCardEq ?_⟩⟩
  rw [Fintype.card_sum, globalVertices_card]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  omega

lemma eventually_pow_lt_half_exp (p : ℕ) :
    ∀ᶠ t : ℕ in atTop, (t:ℝ)^p < (2:ℝ)^t/2 := by
  have ho := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) p (by norm_num : 1 < (2:ℝ))
  have hb := ho.bound (by norm_num : (0:ℝ) < 1/4)
  filter_upwards [hb] with t ht
  have ht' : (t:ℝ)^p ≤ (1/4)*(2:ℝ)^t := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ (t:ℝ)^p by positivity),
      abs_of_pos (pow_pos (by norm_num : (0:ℝ)<2) _)] using ht
  calc
    _ ≤ (1/4)*(2:ℝ)^t := ht'
    _ < _ := by nlinarith [pow_pos (by norm_num : (0:ℝ)<2) t]

end PerfectMatchingPSD

end OAI
