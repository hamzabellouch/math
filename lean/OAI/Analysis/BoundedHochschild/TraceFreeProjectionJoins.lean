import OAI.Analysis.BoundedHochschild.FiniteIncreasingComparison

namespace OAI

/-!
# Projection joins before trace existence

The join of two projections is obtained by adding the range projection of
`(1 - p) * q` to `p`. Polar decomposition also embeds the added projection
into `q`. This is the projection comparison used in Ringrose's Lemma 5.2.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A trace-free join, with the part added to `p` equivalent to a subprojection
of `q`. The formula records the partial isometry needed in finite joins. -/
theorem exists_trace_free_projection_join (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p q : M) (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ v : PartialIso M, v.initial ≤ q ∧ p * v.final = 0 ∧
      IsStarProjection (p + v.final) ∧ p ≤ p + v.final ∧ q ≤ p + v.final ∧
      ∀ z : M, IsStarProjection z → p ≤ z → q ≤ z → p + v.final ≤ z := by
  let b := (1 - p) * q
  have hpb : (1 - p) * b = b := by
    dsimp [b]
    rw [← mul_assoc, hp.one_sub.isIdempotentElem.eq]
  have hbq : b * q = b := by
    dsimp [b]
    rw [mul_assoc, hq.isIdempotentElem.eq]
  obtain ⟨w, r, t, hr, hwi, hwf, ht, hb, hwr, htb⟩ :=
    HochschildPolar.exists_polar_partial_isometry e b
  have hwabs : star w * b = CFC.abs b := by
    calc
      star w * b = star w * (w * CFC.abs b) := congrArg (star w * ·) hb
      _ = CFC.abs b := by rw [← mul_assoc, hwi, hr.left]
  have hw_support {z : M} (hz : IsStarProjection z) (hzb : z * b = b) : z * w = w := by
    have hzero : ((1 - z) * w) * CFC.abs b = 0 := by
      rw [mul_assoc, ← hb, sub_mul, one_mul, hzb, sub_self]
    have hzero' := HochschildPolar.support_right_annihilate hr
      (CFC.abs_nonneg b).isSelfAdjoint hzero
    rw [mul_assoc, hwr, sub_mul, one_mul, sub_eq_zero] at hzero'
    exact hzero'.symm
  have hpw : (1 - p) * w = w := hw_support hp.one_sub hpb
  let v : PartialIso M := ⟨w, by rw [mul_assoc, hwi, hwr]⟩
  have hiv : v.initial = r := hwi
  have hfv : v.final = t := hwf
  have hiq : v.initial ≤ q := by
    rw [hiv]
    apply (hr.proj.le_iff_mul_eq_left hq).mpr
    have hzero : CFC.abs b * (1 - q) = 0 := by
      rw [← hwabs, mul_assoc, mul_sub, mul_one, hbq, sub_self, mul_zero]
    have hzero' := hr.annihilate (1 - q) hzero
    simpa only [mul_sub, mul_one, sub_eq_zero, eq_comm] using hzero'
  have hfp : v.final ≤ 1 - p := by
    apply (v.final_proj.le_iff_mul_eq_right hp.one_sub).mpr
    change (1 - p) * (w * star w) = w * star w
    rw [← mul_assoc, hpw]
  have horth : p * v.final = 0 :=
    HochschildTypeII.projection_orthogonal_of_le_complement hp v.final_proj hfp
  have horth' : v.final * p = 0 := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq,
      v.final_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star horth
  have hj : IsStarProjection (p + v.final) := hp.add v.final_proj horth
  have hvq : v.final * q = b := by
    have h : v.final * b = b := by rw [hfv]; exact htb
    dsimp [b] at h ⊢
    rwa [← mul_assoc, mul_sub, mul_one, horth', sub_zero] at h
  refine ⟨v, hiq, horth, hj, ?_, ?_, ?_⟩
  · exact le_add_of_nonneg_right v.final_proj.nonneg
  · apply (hq.le_iff_mul_eq_right hj).mpr
    rw [add_mul, hvq]
    dsimp [b]
    noncomm_ring
  · intro z hz hpz hqz
    have hzp : z * p = p := (hp.le_iff_mul_eq_right hz).mp hpz
    have hzq : z * q = q := (hq.le_iff_mul_eq_right hz).mp hqz
    have hzb : z * b = b := by
      dsimp [b]
      rw [← mul_assoc, mul_sub, mul_one, hzp, sub_mul, hzq, sub_mul, one_mul]
    have hzw : z * w = w := hw_support hz hzb
    apply (hj.le_iff_mul_eq_right hz).mpr
    change z * (p + w * star w) = p + w * star w
    rw [mul_add, hzp, ← mul_assoc, hzw]

end KadisonRingrose
end BoundedHochschild

end

end OAI
