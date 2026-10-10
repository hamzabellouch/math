import OAI.Probability.DilutedSpin.CavityRateLimits
import OAI.Probability.DilutedSpin.FullRegularSelection
import OAI.Probability.DilutedSpin.ScoreIncrement

namespace OAI

section
namespace DilutedSpinGlass
open Filter
open scoped Topology

lemma scoreScale_div_succ_tendsto :
    Tendsto (fun N => scoreScale N/(N+1)) atTop (𝓝 0) := by
  have he := (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop)
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp he
  apply squeeze_zero' (Eventually.of_forall (fun N => by unfold scoreScale; positivity))
    (eventually_atTop.2 ⟨1,fun N hN => ?_⟩) ht
  change scoreScale N/(N+1) ≤ (N:ℝ)^(-(1/4:ℝ))
  rw [← neg_div,← SizeCoupling.scoreScale_div (show 0 < N by omega)]
  apply div_le_div_of_nonneg_left
  · unfold scoreScale; positivity
  · exact_mod_cast (show 0 < N by omega)
  · linarith

namespace UniversalDictionary
lemma gridExponents_exponents (L : ℕ) :
    Exponents (fun i : Fin L => gridExponents L i.castSucc) := by
  constructor
  · intro i j hij
    simp only [gridExponents,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
    apply (div_lt_div_iff_of_pos_right (by positivity : (0:ℝ)<L+1)).mpr
    exact_mod_cast (show i.val+1<j.val+1 by exact Nat.add_lt_add_right hij 1)
  · intro i
    refine ⟨gridExponents_pos L i.castSucc,?_⟩
    simp only [gridExponents,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
    apply (div_lt_one (by positivity : (0:ℝ)<L+1)).mpr
    exact_mod_cast (show i.val+1<L+1 by omega)
end UniversalDictionary
end DilutedSpinGlass

end

end OAI
