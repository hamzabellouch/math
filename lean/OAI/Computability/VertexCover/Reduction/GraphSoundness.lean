import Mathlib
import OAI.Computability.VertexCover.Analysis.DenseSeparatorData
import OAI.Computability.VertexCover.Reduction.RestrictionFrozen

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

theorem h_ge_three (m : ℕ) (hm : 0 < m) : 3 ≤ h m := by
  have hpow : 1 ≤ m^3 := one_le_pow₀ hm
  unfold h
  norm_num only [Nat.reducePow]
  omega

theorem private_variance_threshold (m : ℕ) (hm : 0 < m) : ν m*(h m:ℝ)/4 = 8 := by
  have hn : (m:ℝ) ≠ 0 := by positivity
  simp only [ν, h, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  norm_num

end VertexCover.Parameters

namespace VertexCover.LabelCover
open VertexCover.Restriction

theorem dense_privateVariance_lower (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (A : Finset (Φ.Vertex (Parameters.d m)))
    (hA : (Φ.graph (Parameters.d m) (Parameters.t m)).IsIndepSet
      (A : Set (Φ.Vertex (Parameters.d m))))
    (hdense : (Fintype.card (Φ.Vertex (Parameters.d m)):ℝ)/(m:ℝ) ≤ A.card) :
    ∃ hV : (Φ.highVectors (Parameters.t m) A).Nonempty,
      ∃ J : Finset (Fin (Parameters.d m)), J.card = Parameters.h m ∧
      ∃ frozen : Φ.Seeds (Parameters.d m),
      ∃ weights : Fin (Parameters.d m) → Fin (Φ.WeightDimension (Parameters.d m)) → ℝ,
        Φ.InWeightCube weights ∧
        8 ≤ Φ.ownTotalVariance J frozen (Φ.outsideSum J frozen weights)
          (Φ.highVectors (Parameters.t m) A) hV := by
  obtain ⟨hV, _hzero, henergy⟩ := Φ.dense_separator_data m hm A hA hdense
  rw [← Φ.restrictionFunction_energy_variance] at henergy
  have hdim := Parameters.dimensions m hm
  obtain ⟨J, hJ, frozen, s, hs⟩ := Φ.restriction_frozen_exists
    hdim.1 (Parameters.h_ge_three m (by omega)) hdim.2.2.1.le
    (Parameters.ν m) (Parameters.positive m (by omega)).1
    (Parameters.restriction_budget m hm) _ hV henergy
  refine ⟨hV, J, hJ, frozen, CompactCube.realWeights s, ?_, ?_⟩
  · intro j k
    exact abs_le.mpr (s j k).2
  · simpa only [Parameters.private_variance_threshold m (by omega)] using hs

theorem graph_soundness_independent (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (hval : Φ.value ≤ Parameters.σ m)
    (A : Finset (Φ.Vertex (Parameters.d m)))
    (hA : (Φ.graph (Parameters.d m) (Parameters.t m)).IsIndepSet
      (A : Set (Φ.Vertex (Parameters.d m)))) :
    (A.card:ℝ) < (Fintype.card (Φ.Vertex (Parameters.d m)):ℝ)/(m:ℝ) := by
  by_contra hn
  obtain ⟨hV, J, hJ, frozen, weights, _hw, hlow⟩ :=
    Φ.dense_privateVariance_lower m hm A hA (le_of_not_gt hn)
  have hu := Φ.ownTotalVariance_no_upper m hm hval J hJ frozen
    (Φ.outsideSum J frozen weights) _ hV
  linarith

theorem graph_soundness_cover (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (hval : Φ.value ≤ Parameters.σ m)
    (C : Finset (Φ.Vertex (Parameters.d m)))
    (hC : (Φ.graph (Parameters.d m) (Parameters.t m)).IsVertexCover
      (C : Set (Φ.Vertex (Parameters.d m)))) :
    (1-1/(m:ℝ)) * Fintype.card (Φ.Vertex (Parameters.d m)) < (C.card:ℝ) := by
  classical
  have hI : (Φ.graph (Parameters.d m) (Parameters.t m)).IsIndepSet
      (↑(Cᶜ) : Set (Φ.Vertex (Parameters.d m))) := by
    simpa only [Finset.coe_compl] using SimpleGraph.isIndepSet_compl_iff_isVertexCover.mpr hC
  have hi := Φ.graph_soundness_independent m hm hval Cᶜ hI
  rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ C)] at hi
  simp only [div_eq_mul_inv, one_mul] at hi ⊢
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
