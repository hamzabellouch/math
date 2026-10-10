import Mathlib
import OAI.Computability.VertexCover.Reduction.DecodingUpperThreeHalves
import OAI.Computability.VertexCover.Analysis.SignAtom
import OAI.Computability.VertexCover.Analysis.GridCentralCard

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.FiniteAntiConcentration
noncomputable section
open AntiConcentration

def gridTailDensity (d n t : ℕ) : ℝ :=
  ((Finset.univ.filter (fun x : Fin n → Fin (2*d+1) =>
    (t : ℝ) < ∑ i, grid d (x i))).card : ℝ) / ((2*d+1 : ℕ)^n : ℝ)

theorem gridTailDensity_lower (d k t : ℕ) (hk : 0 < k) (ht : t < d) :
    1/2 - Real.sqrt 2 * ((t : ℝ)+1) / Real.sqrt (2*(k : ℝ)) <
      gridTailDensity d (2*k) t := by
  classical
  let C : ℝ := ((Finset.univ.filter (fun x : Fin (2*k) → Fin (2*d+1) =>
    -(t : ℝ) ≤ ∑ i, grid d (x i) ∧ (∑ i, grid d (x i)) ≤ t)).card : ℝ)
  let Q : ℝ := ((2*d+1 : ℕ)^(2*k) : ℝ)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hP : 0 < (2:ℝ)^(2*k) := by positivity
  have hsqrt : 0 < Real.sqrt (2*(k:ℝ)) := by positivity
  have hc : C / Q ≤ (2*(t:ℝ)+1) * centralProbability k := by
    have h := grid_central_card d (2*k) t ht
    have hatom := sign_atom_le k (2*k/2)
    have hfirst : C/Q ≤ (2*(t:ℝ)+1) * (((2*k).choose (2*k/2) : ℝ)/(2:ℝ)^(2*k)) := by
      rw [mul_div, div_le_div_iff₀ hQ hP]
      dsimp [C, Q] at *
      nlinarith [h]
    exact hfirst.trans (mul_le_mul_of_nonneg_left hatom (by positivity))
  have hstrict : C / Q < (2*(t:ℝ)+2) * (Real.sqrt 2 / Real.sqrt (2*(k:ℝ))) := by
    have hstep := mul_lt_mul_of_pos_left (centralProbability_lt k hk)
      (by positivity : (0:ℝ) < 2*t+1)
    have hnonneg : 0 ≤ Real.sqrt 2 / Real.sqrt (2*(k:ℝ)) := by positivity
    exact lt_of_le_of_lt hc (hstep.trans_le (mul_le_mul_of_nonneg_right (by linarith) hnonneg))
  have htail : 2 * gridTailDensity d (2*k) t + C / Q = 1 := by
    have h := grid_tail_count d (2*k) t
    unfold gridTailDensity
    apply (div_eq_one_iff_eq (ne_of_gt hQ)).mpr at h
    dsimp [C, Q] at *
    convert h using 1 ; ring
  have he : (2*(t:ℝ)+2) * (Real.sqrt 2 / Real.sqrt (2*(k:ℝ))) =
      2 * (Real.sqrt 2 * ((t:ℝ)+1) / Real.sqrt (2*(k:ℝ))) := by ring
  rw [he] at hstrict
  linarith

end
end VertexCover.FiniteAntiConcentration

namespace VertexCover.Parameters
noncomputable section

 theorem t_lt_d (m : ℕ) (hm : 4 ≤ m) : t m < d m := by
  have hm1 : 1 ≤ m := by omega
  have hpow : m^4 ≤ m^10 := Nat.pow_le_pow_right hm1 (by decide)
  have hp : 1 ≤ m^4 := one_le_pow₀ hm1
  unfold t d
  norm_num only [Nat.reducePow]
  omega

 theorem tail_error_lt (m : ℕ) (hm : 4 ≤ m) :
    Real.sqrt 2 * (a m + 1/Real.sqrt (d m)) < 1/(m:ℝ) := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have ha : 0 < a m := by unfold a; positivity
  have hinv : (1:ℝ)/Real.sqrt (d m) < a m := by
    exact one_div_lt_one_div_of_lt (by positivity) (sqrt_d_gt m hm)
  have hsq : Real.sqrt (2:ℝ) < 3/2 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hp := Real.sqrt_nonneg (2:ℝ)
    nlinarith
  have hmul : Real.sqrt 2 * (a m + 1/Real.sqrt (d m)) < 3*a m := by
    have h1 := mul_lt_mul_of_pos_left hinv (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))
    have h2 := mul_lt_mul_of_pos_right hsq (by linarith : 0 < 2*a m)
    nlinarith
  have he : 3*a m < 1/(m:ℝ) := by
    unfold a
    rw [mul_one_div]
    apply (div_lt_div_iff₀ (by positivity : (0:ℝ)<4*m) hmpos).mpr
    nlinarith
  exact hmul.trans he

 theorem midpoint_grid_tail (m : ℕ) (hm : 4 ≤ m) :
    1/2 - Real.sqrt 2 * (a m + 1/Real.sqrt (d m)) <
      FiniteAntiConcentration.gridTailDensity (d m) (d m) (t m) ∧
    1/2 - 1/(m:ℝ) <
      1/2 - Real.sqrt 2 * (a m + 1/Real.sqrt (d m)) := by
  obtain ⟨k, hk⟩ := (dimensions m hm).2.2.2
  have hd : d m = 2*k := by omega
  have hkpos : 0 < k := by have := (dimensions m hm).1; omega
  have ht := FiniteAntiConcentration.gridTailDensity_lower (d m) k (t m) hkpos (t_lt_d m hm)
  have hs : Real.sqrt (2*(k:ℝ)) = Real.sqrt (d m) := by rw [hd]; push_cast; rfl
  rw [← hd, hs] at ht
  have hnonzero : Real.sqrt (d m) ≠ 0 := ne_of_gt (lt_trans (by positivity) (sqrt_d_gt m hm))
  have he : Real.sqrt 2 * ((t m : ℝ)+1) / Real.sqrt (d m) =
      Real.sqrt 2 * (a m + 1/Real.sqrt (d m)) := by
    rw [t_eq m (by omega)]
    field_simp
  exact ⟨by simpa only [he] using ht, by linarith [tail_error_lt m hm]⟩

end
end VertexCover.Parameters


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
