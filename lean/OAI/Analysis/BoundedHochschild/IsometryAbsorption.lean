import OAI.Analysis.BoundedHochschild.ProperlyInfiniteColumns

namespace OAI

/-!
# Absorbing a projection around an isometry

If a projection contains the range of an isometry, it is equivalent to the
unit. The countable shift proof is the particular projection comparison needed
for a unital infinite matrix system.
-/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The projection form of the countable shift argument: an isometry whose
range lies under `p` extends to an equivalence between one and `p`. -/
theorem isometry_onto_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {v p : M} (hv : star v * v = 1) (hp : IsStarProjection p) (hpv : p * v = v) :
    ∃ w : PartialIso M, w.initial = 1 ∧ w.final = p := by
  let r := 1 - p
  have hr : IsStarProjection r := hp.one_sub
  have hrv : r * v = 0 := by rw [sub_mul, one_mul, hpv, sub_self]
  let c := isometryColumn v hv r hr
  have hci (i) : (c i).initial = r := isometryColumn_initial ..
  have hco (i j) (hij : i ≠ j) : (c i).final * (c j).final = 0 :=
    isometryColumn_final_orthogonal hv hr hrv hij
  have hc0 : (c 0).final = r := by
    change (v ^ 0 * r) * star (v ^ 0 * r) = r
    rw [pow_zero, one_mul, hr.isSelfAdjoint.star_eq, hr.isIdempotentElem.eq]
  obtain ⟨q, hq, hcq, hqmin, _⟩ := exists_orthogonal_projection_sum e
    (fun i => (c i).final) (fun i => (c i).final_proj) hco
  let a (i : ℕ) := columnTransition (c (i + 1)) (c i) ((hci _).trans (hci _).symm)
  have hai (i) : (a i).initial = (c i).final := columnTransition_initial ..
  have haf (i) : (a i).final = (c (i + 1)).final := columnTransition_final ..
  obtain ⟨s, hsi, hsf, hsi_min, hsf_min⟩ := exists_countable_partialIso_sum e a
    (fun i j hij => by rw [hai, hai]; exact hco i j hij)
    (fun i j hij => by rw [haf, haf]; exact hco _ _ (by omega))
  have hsq : s.initial = q := le_antisymm
    (hsi_min q hq (fun i => by rw [hai]; exact hcq i))
    (hqmin _ s.initial_proj (fun i => by rw [← hai]; exact hsi i))
  have hstq : s.final ≤ q := hsf_min q hq (fun i => by rw [haf]; exact hcq _)
  have hrt : r * s.final = 0 := by
    have hb : s.final ≤ 1 - r := by
      apply hsf_min _ hr.one_sub
      intro i
      apply projection_le_complement_of_mul_zero (a i).final_proj hr
      rw [haf, ← hc0]
      exact hco _ _ (by omega)
    exact HochschildTypeII.projection_orthogonal_of_le_complement hr s.final_proj hb
  have hrq : r ≤ q := by rw [← hc0]; exact hcq 0
  have hrs : IsStarProjection (r + s.final) := hr.add s.final_proj hrt
  have hqrs : q = r + s.final := by
    apply le_antisymm
    · apply hqmin _ hrs
      intro i
      cases i with
      | zero => rw [hc0]; exact le_add_of_nonneg_right s.final_proj.nonneg
      | succ i =>
          calc
            (c (i + 1)).final = (a i).final := (haf i).symm
            _ ≤ s.final := hsf i
            _ ≤ r + s.final := le_add_of_nonneg_left hr.nonneg
    · apply (hrs.le_iff_mul_eq_right hq).mpr
      rw [mul_add, (hr.le_iff_mul_eq_right hq).mp hrq,
        (s.final_proj.le_iff_mul_eq_right hq).mp hstq]
  let t : PartialIso M := ⟨1 - q, by
    rw [hq.one_sub.isSelfAdjoint.star_eq, hq.one_sub.isIdempotentElem.eq,
      hq.one_sub.isIdempotentElem.eq]⟩
  have hti : t.initial = 1 - q := by
    change star (1 - q) * (1 - q) = _
    rw [hq.one_sub.isSelfAdjoint.star_eq, hq.one_sub.isIdempotentElem.eq]
  have htf : t.final = 1 - q := by
    change (1 - q) * star (1 - q) = _
    rw [hq.one_sub.isSelfAdjoint.star_eq, hq.one_sub.isIdempotentElem.eq]
  have hi : s.initial * t.initial = 0 := by rw [hsq, hti, hq.mul_one_sub_self]
  have hf : s.final * t.final = 0 := by
    rw [htf, mul_sub, mul_one, (s.final_proj.le_iff_mul_eq_left hq).mp hstq, sub_self]
  refine ⟨s.orthogonalSum t hi hf, ?_, ?_⟩
  · rw [PartialIso.orthogonalSum_initial, hsq, hti]
    abel
  · rw [PartialIso.orthogonalSum_final, htf, hqrs]
    change s.final + (1 - ((1 - p) + s.final)) = p
    abel

end BoundedHochschild.KadisonRingrose

end

end OAI
