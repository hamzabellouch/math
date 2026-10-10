import OAI.Probability.InvariantIsing.Cavity.CavitySpinSplitOverlap

namespace OAI

/-! A fixed initial remainder changes the overlap by at most twice its fraction. -/
noncomputable section
open IsingPerceptron
namespace InvariantIsing

lemma cavity_spin_split_right_overlap_error {r N : ℕ} (hN : 0<N) (σ τ : Spin (r+N)) :
    |cavityTotalSpinOverlap (σ,τ)-
      cavityTotalSpinOverlap ((cavitySpinSplit r N σ).2,(cavitySpinSplit r N τ).2)|≤
      2*(r:ℝ)/(r+N) := by
  let a := cavityTotalSpinOverlap ((cavitySpinSplit r N σ).1,(cavitySpinSplit r N τ).1)
  let b := cavityTotalSpinOverlap ((cavitySpinSplit r N σ).2,(cavitySpinSplit r N τ).2)
  let c := cavityTotalSpinOverlap (σ,τ)
  have hp : (0:ℝ)<r+N := by exact_mod_cast Nat.add_pos_right r hN
  have hs : ((r:ℝ)+N)*c=r*a+N*b := by
    simpa only [Nat.cast_add] using cavity_spin_split_overlap σ τ
  have he : c-b=(r:ℝ)*(a-b)/(r+N) := by
    apply (eq_div_iff hp.ne').mpr
    nlinarith [hs]
  change |c-b|≤_
  rw [he,abs_div,abs_of_pos hp,abs_mul,abs_of_nonneg (Nat.cast_nonneg r)]
  apply div_le_div_of_nonneg_right _ hp.le
  have ha : |a|≤1 := abs_cavityTotalSpinOverlap_le _
  have hb : |b|≤1 := abs_cavityTotalSpinOverlap_le _
  have hab : |a-b|≤2 := (abs_sub a b).trans (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg r)]

end InvariantIsing

end

end OAI
