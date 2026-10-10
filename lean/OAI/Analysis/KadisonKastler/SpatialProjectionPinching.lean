import OAI.Analysis.KadisonKastler.TracialSpatialGeometry

namespace OAI

/-! # Pinching a spatial implementer by a commutant projection -/

namespace KadisonKastler

noncomputable section

open ContinuousLinearMapWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The average with the projection reflection preserves the derivation and
its norm bound, and reduces the chosen projection. -/
theorem exists_projection_reducing_implementer
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M)
    (p : H →L[ℂ] H) (hp : IsStarProjection p) (hpM : p ∈ M.commutant) :
    ∃ S : H →L[ℂ] H, IsSelfAdjoint S ∧ ‖S‖ ≤ ‖T‖ ∧
      S - T ∈ M.commutant ∧ Commute p S := by
  let u : unitary (H →L[ℂ] H) := ⟨2 * p - 1, hp.two_mul_sub_one_mem_unitary⟩
  have hu : u.val ∈ M.commutant := M.commutant.sub_mem
    (M.commutant.mul_mem (M.commutant.natCast_mem 2) hpM) M.commutant.one_mem
  have ht : ofCLM T ∈ boundedSelfAdjointImplementers M T :=
    ⟨hTsa, le_rfl, by simp⟩
  have hm := boundedSelfAdjointImplementers_midpoint M T ht
    (boundedSelfAdjointImplementers_conjugate M T hT u hu ht)
  let S := (1 / 2 : ℝ) • (T + unitaryConj u T)
  refine ⟨S, hm.1, hm.2.1, hm.2.2, ?_⟩
  have hus : star u.val = u.val := by
    dsimp [u]
    simp only [star_sub, star_mul, star_ofNat, star_one, hp.isSelfAdjoint.star_eq]
    noncomm_ring
  have hpu : p * u.val = p := by
    dsimp [u]
    have hi := hp.isIdempotentElem.eq
    calc
      p * (2 * p - 1) = 2 * (p * p) - p := by noncomm_ring
      _ = p := by rw [hi]; noncomm_ring
  have hup : u.val * p = p := by
    dsimp [u]
    have hi := hp.isIdempotentElem.eq
    calc
      (2 * p - 1) * p = 2 * (p * p) - p := by noncomm_ring
      _ = p := by rw [hi]; noncomm_ring
  change p * ((1 / 2 : ℝ) • (T + unitaryConj u T)) =
    ((1 / 2 : ℝ) • (T + unitaryConj u T)) * p
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  dsimp [unitaryConj]
  rw [hus, mul_add, add_mul, ← mul_assoc p (u.val * T), ← mul_assoc p u.val, hpu,
    mul_assoc (u.val * T) u.val p, hup]
  dsimp [u]
  noncomm_ring

end

end KadisonKastler

end OAI
