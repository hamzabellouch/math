import Mathlib
import OAI.Computability.VertexCover.Reduction.HighVectorsSeparated
import OAI.Computability.VertexCover.Reduction.GridBudget

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
namespace VertexCover.Parameters

 theorem pair_budget (m : ℕ) (hm : 4 ≤ m) :
    (((h m).choose 2 : ℕ) : ℝ)*(ell m : ℝ)^2*σ m = ((h m : ℝ)-1)/(2*(h m : ℝ)) := by
  have hpos := positive m (by omega : 0 < m)
  have hh : (h m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos.2.2.2.1)
  have hl : (ell m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos.2.2.1)
  rw [Nat.cast_choose_two, σ_eq]
  field_simp

 theorem pair_budget_lt (m : ℕ) (hm : 4 ≤ m) :
    (((h m).choose 2 : ℕ) : ℝ)*(ell m : ℝ)^2*σ m < (1:ℝ)/2 := by
  rw [pair_budget m hm]
  have hh : (0:ℝ) < h m := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<2) (dimensions m hm).2.1)
  apply (div_lt_iff₀ (by positivity : (0:ℝ) < 2*(h m : ℝ))).mpr
  linarith

 theorem σ_between (m : ℕ) (hm : 4 ≤ m) : 0 < σ m ∧ σ m < 1 := by
  refine ⟨(positive m (by omega)).2.2.2.2.2, ?_⟩
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hp : (1:ℝ) ≤ (m:ℝ)^12 := one_le_pow₀ hm1
  unfold σ
  apply (div_lt_one (by positivity)).mpr
  norm_num only [Nat.reducePow]
  nlinarith

 theorem sqrt_d_gt (m : ℕ) (hm : 4 ≤ m) : 4*(m:ℝ) < Real.sqrt (d m) := by
  rw [sqrt_d]
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hp : (m:ℝ)^1 ≤ (m:ℝ)^5 := pow_le_pow_right₀ hm1 (by decide)
  simp only [pow_one] at hp
  norm_num only [Nat.reducePow]
  nlinarith

 theorem gap_ratio (m : ℕ) (hm : 0 < m) :
    (1-1/(m:ℝ))/(1/2+1/(m:ℝ)) = 2-6/((m:ℝ)+2) := by
  have hp : (m:ℝ) ≠ 0 := by positivity
  have hm2 : (m:ℝ)+2 ≠ 0 := by positivity
  have hh : (1:ℝ)/2+1/(m:ℝ) ≠ 0 := by positivity
  field_simp
  ring

end VertexCover.Parameters

namespace VertexCover.LabelCover

theorem decoding_upper_lt_three_halves (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (hval : Φ.value ≤ Parameters.σ m) (L : Φ.PrivateLists (Parameters.d m))
    (hlen : ∀ i, (L i).length ≤ Parameters.ell m)
    (J : Finset (Fin (Parameters.d m))) (hJ : J.card = Parameters.h m)
    (frozen : Φ.Seeds (Parameters.d m)) :
    finiteMean (fun hidden : Φ.HiddenSeeds J =>
      (Φ.listHitMaximum L (Φ.spliceSeeds J frozen hidden) J : ℝ)) < 3/2 := by
  have hu := Φ.decoding_upper_bound hval L hlen J frozen
  rw [hJ] at hu
  have hp := Parameters.pair_budget_lt m hm
  linarith

end VertexCover.LabelCover


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
