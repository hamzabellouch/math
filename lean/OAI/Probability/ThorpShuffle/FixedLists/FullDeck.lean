import OAI.Probability.ThorpShuffle.Main

namespace OAI


noncomputable section
open scoped BigOperators
open Filter
namespace Thorp

lemma distance_add_le (d s t : ℕ) : distance d (s + t) ≤ distance d s := by
  unfold distance
  rw [law_add]
  have h := FiniteLaw.tv_conv_contract (law d t) (law d s)
    (law_sum d t) (law_sum d s) 0 (law_nonneg d t)
  change tv (FiniteLaw.conv (law d t) (law d s))
    (fun _ => (1 : ℝ) / Fintype.card (State d)) ≤
    tv (law d s) (fun _ => (1 : ℝ) / Fintype.card (State d))
  simpa only [mul_zero, sub_zero, one_mul] using h

theorem full_mixing_2048 :
    Tendsto (fun d : ℕ => distance d (2048 * d)) atTop (nhds 0) := by
  apply squeeze_zero (fun d => by unfold distance tv; positivity) _ full_mixing
  intro d
  rw [show 2048 * d = 1600 * d + 448 * d by omega]
  exact distance_add_le d (1600 * d) (448 * d)

end Thorp

end

end OAI
