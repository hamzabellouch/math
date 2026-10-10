import Mathlib
import OAI.Computability.VertexCover.Analysis.RestrictionSum

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
namespace VertexCover.Restriction

theorem choose_step (d h : ℕ) (hd : 0 < d) (hh : 0 < h) :
    (d:ℝ)*((d-1).choose (h-1):ℝ) = (h:ℝ)*(d.choose h:ℝ) := by
  have he := Nat.add_one_mul_choose_eq (d-1) (h-1)
  rw [Nat.sub_add_cancel hd, Nat.sub_add_cancel hh] at he
  exact_mod_cast he.trans (Nat.mul_comm _ _)

theorem batch_pair_scale (d h : ℕ) (hd : 4 ≤ d) (hh : 3 ≤ h) :
    (d:ℝ)*((d-2).choose (h-2):ℝ) ≤ 2*(h:ℝ)*((d-1).choose (h-1):ℝ) := by
  have he := choose_step (d-1) (h-1) (by omega) (by omega)
  have hed : d-1-1 = d-2 := by omega
  have heh : h-1-1 = h-2 := by omega
  rw [hed, heh, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_sub (by omega : 1 ≤ h)] at he
  norm_num only [Nat.cast_one] at he
  have hdR : (4:ℝ) ≤ d := by exact_mod_cast hd
  have hC1 : (0:ℝ) ≤ (d-1).choose (h-1) := Nat.cast_nonneg _
  have hC2 : (0:ℝ) ≤ (d-2).choose (h-2) := Nat.cast_nonneg _
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ d-2) hC2]

theorem batch_triple_scale (d h : ℕ) (hd : 4 ≤ d) (hh : 3 ≤ h) :
    (d:ℝ)^2*((d-3).choose (h-3):ℝ) ≤ 4*(h:ℝ)^2*((d-1).choose (h-1):ℝ) := by
  have he := choose_step (d-2) (h-2) (by omega) (by omega)
  have hed : d-2-1 = d-3 := by omega
  have heh : h-2-1 = h-3 := by omega
  rw [hed, heh, Nat.cast_sub (by omega : 2 ≤ d), Nat.cast_sub (by omega : 2 ≤ h)] at he
  norm_num only [Nat.cast_ofNat] at he
  have hdR : (4:ℝ) ≤ d := by exact_mod_cast hd
  have hhR : (0:ℝ) ≤ h := Nat.cast_nonneg _
  have hC2 : (0:ℝ) ≤ (d-2).choose (h-2) := Nat.cast_nonneg _
  have hC3 : (0:ℝ) ≤ (d-3).choose (h-3) := Nat.cast_nonneg _
  have hl : (d:ℝ)*((d-3).choose (h-3):ℝ) ≤ 2*(h:ℝ)*((d-2).choose (h-2):ℝ) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ d-4) hC3]
  have hl' := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg d : (0:ℝ) ≤ d)
  have hp := mul_le_mul_of_nonneg_left (batch_pair_scale d h hd hh) (by positivity : (0:ℝ) ≤ 2*h)
  nlinarith

end VertexCover.Restriction

namespace VertexCover.LabelCover
open VertexCover.Restriction
open EnergyForm.Projection
open scoped BigOperators

theorem privateProjection_batch_lower (Φ : LabelCover) {d h : ℕ}
    (hd : 4 ≤ d) (hh : 3 ≤ h) (ν : ℝ)
    (hscale : 16*(h:ℝ)+32*(h:ℝ)^2 ≤ ν*d/2)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (henergy : ν*d ≤ (Φ.restrictionForm d).energy (Φ.restrictionFunction A hA)) :
    (d.choose h:ℝ)*ν*h/2 ≤
      ∑ J ∈ batches d h, ∑ j ∈ J,
        (Φ.restrictionForm d).energy (Φ.privateProjection J j (Φ.restrictionFunction A hA)) := by
  have hb := Φ.privateProjection_batch_bound hh A hA
  have hC1 : (0:ℝ) ≤ (d-1).choose (h-1) := Nat.cast_nonneg _
  have hl := mul_le_mul_of_nonneg_left henergy hC1
  have hs := mul_le_mul_of_nonneg_left hscale hC1
  have hp := batch_pair_scale d h hd hh
  have ht := batch_triple_scale d h hd hh
  have he := choose_step d h (by omega) (by omega)
  have he' : ((d-1).choose (h-1):ℝ)*ν*d = (d.choose h:ℝ)*ν*h := by
    calc
      _ = ν*((d:ℝ)*((d-1).choose (h-1):ℝ)) := by ring
      _ = _ := by rw [he]; ring
  nlinarith

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
