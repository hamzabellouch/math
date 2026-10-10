import OAI.Analysis.KadisonKastler.Intertwiner
import OAI.Analysis.KadisonKastler.CompleteCommutantDistance

namespace OAI

/-! # A controlled unitary conjugating two close projections

The construction takes place inside the chosen C-star algebra. Applying
it to a relative commutant therefore preserves the common subalgebra.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem polar_unitary_intertwines_selfAdjoint
    (p q T : A) (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q)
    (hunit : IsUnit T) (hT : T * p = q * T)
    (u : unitary A) (hu : (u : A) * CFC.abs T = T) :
    (u : A) * p = q * (u : A) := by
  have hs : star T * q = p * star T := by
    have h := congrArg star hT
    simpa only [star_mul, hp.star_eq, hq.star_eq] using h.symm
  have hc : Commute (star T * T) p := by
    change (star T * T) * p = p * (star T * T)
    calc
      _ = star T * (T * p) := mul_assoc _ _ _
      _ = star T * (q * T) := by rw [hT]
      _ = (star T * q) * T := (mul_assoc _ _ _).symm
      _ = p * (star T * T) := by rw [hs, mul_assoc]
  have habs : Commute (CFC.abs T) p := hc.cfcₙ_nnreal NNReal.sqrt
  have hi : IsUnit (CFC.abs T) := by
    obtain ⟨t, rfl⟩ := hunit
    exact isUnit_abs t
  apply hi.mul_right_cancel
  calc
    ((u : A) * p) * CFC.abs T = (u : A) * (p * CFC.abs T) := mul_assoc _ _ _
    _ = (u : A) * (CFC.abs T * p) := by rw [habs.eq]
    _ = T * p := by rw [← mul_assoc, hu]
    _ = q * T := hT
    _ = (q * (u : A)) * CFC.abs T := by rw [mul_assoc, hu]

theorem exists_unitary_conjugating_close_projections [Nontrivial A]
    (p q : A) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hclose : ‖q - p‖ < 1) :
    ∃ u : unitary A, (u : A) * p * star (u : A) = q ∧
      ‖(u : A) - 1‖ ≤ 2 * ‖q - p‖ := by
  let T : A := q * p + (1 - q) * (1 - p)
  have hpp := hp.isIdempotentElem.eq
  have hqq := hq.isIdempotentElem.eq
  have hcp : (1 - p) * p = 0 := by rw [sub_mul, one_mul, hpp, sub_self]
  have hcq : q * (1 - q) = 0 := by rw [mul_sub, mul_one, hqq, sub_self]
  have hTp : T * p = q * p := by
    calc
      T * p = q * (p * p) + (1 - q) * ((1 - p) * p) := by
        dsimp [T]
        rw [add_mul, mul_assoc, mul_assoc]
      _ = q * p := by rw [hpp, hcp, mul_zero, add_zero]
  have hqT : q * T = q * p := by
    calc
      q * T = (q * q) * p + (q * (1 - q)) * (1 - p) := by
        dsimp [T]
        rw [mul_add]
        simp only [mul_assoc]
      _ = q * p := by rw [hqq, hcq, zero_mul, add_zero]
  have hT : T * p = q * T := hTp.trans hqT.symm
  have he : T - 1 = (q - p) * (p + p - 1) := by dsimp [T]; noncomm_ring [hpp]
  have hn : ‖T - 1‖ ≤ ‖q - p‖ := by
    rw [he]
    have hs : ‖p + p - 1‖ ≤ 1 := by
      have h := projection_reflection_norm_le_one p hp
      have he : p + p - 1 = -(1 - p - p) := by abel
      rwa [he, norm_neg]
    exact (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hs)
  have htunit : IsUnit T := (Units.ofNearby 1 T (by simpa using hn.trans_lt hclose)).isUnit
  obtain ⟨u, hu, hnu⟩ := exists_polar_unitary_near_one T (hn.trans_lt hclose)
  have hip := polar_unitary_intertwines_selfAdjoint p q T hp.isSelfAdjoint
    hq.isSelfAdjoint htunit hT u hu
  refine ⟨u, ?_, hnu.trans (by linarith)⟩
  rw [hip, mul_assoc, Unitary.mul_star_self_of_mem u.property, mul_one]

end

end KadisonKastler

end OAI
