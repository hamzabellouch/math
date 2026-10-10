import OAI.Analysis.BoundedHochschild.AbelianCentralSupport
import OAI.Analysis.BoundedHochschild.FiniteProjectionEquivalence

namespace OAI

/-! Abelian projections with the same central support are equivalent. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildComparison

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_initial_zero_iff_final_zero (v : PartialIso M)
    {c : M} (hc : ∀ a : M, c * a = a * c) :
    c * v.initial = 0 ↔ c * v.final = 0 := by
  have hf (w : PartialIso M) (hi : c * w.initial = 0) : c * w.final = 0 := by
    have hv : c * (w : M) = 0 := by
      calc
        _ = c * ((w : M) * w.initial) := by rw [w.mul_initial]
        _ = (w : M) * (c * w.initial) := by rw [← mul_assoc, hc, mul_assoc]
        _ = 0 := by rw [hi, mul_zero]
    change c * ((w : M) * star (w : M)) = 0
    rw [← mul_assoc, hv, zero_mul]
  exact ⟨hf v, fun h => by simpa using hf (adjointPartialIso v) (by simpa using h)⟩

lemma IsCentralSupport.partialIso (v : PartialIso M) {z : M}
    (h : IsCentralSupport v.initial z) : IsCentralSupport v.final z := by
  have hzv : z * (v : M) = v := by
    calc
      _ = z * ((v : M) * v.initial) := by rw [v.mul_initial]
      _ = (v : M) * (z * v.initial) := by rw [← mul_assoc, (h.1.2 (v : M)).eq, mul_assoc]
      _ = v := by rw [(v.initial_proj.le_iff_mul_eq_right h.1.1).mp h.2.1, v.mul_initial]
  refine ⟨h.1, (v.final_proj.le_iff_mul_eq_right h.1.1).mpr ?_, ?_⟩
  · change z * ((v : M) * star (v : M)) = _
    rw [← mul_assoc, hzv]
    rfl
  · intro c hc hc0
    exact h.2.2 c hc ((central_initial_zero_iff_final_zero v (fun a => (hc.2 a).eq)).mpr hc0)

/-- Each subprojection of an abelian projection is a central cut of it. -/
theorem abelian_subprojection_central_cut (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p q : M} (hp : AbelianProjection p) (hq : IsStarProjection q) (hqp : q ≤ p) :
    ∃ c : M, CentralProjection c ∧ c * p = q := by
  have hr := (hq.le_iff_sub hp.1).mp hqp
  have hqr : q * (p - q) = 0 := by
    rw [mul_sub, (hq.le_iff_mul_eq_left hp.1).mp hqp, hq.isIdempotentElem.eq, sub_self]
  obtain ⟨c, hc, hqc, hcr⟩ := exists_trace_free_central_separator e hq hr
    (HochschildTypeII.abelian_orthogonal_mul hp hq hr hqp
      (sub_le_self _ hq.nonneg) hqr)
  refine ⟨c, hc, ?_⟩
  have hcq := (hq.le_iff_mul_eq_right hc.1).mp hqc
  rw [mul_sub, hcq, sub_eq_zero] at hcr
  exact hcr

/-- Full abelian projections over the same central support are equivalent. -/
theorem abelian_equivalent_of_central_support (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p q z : M} (hp : AbelianProjection p) (hq : AbelianProjection q)
    (hpz : IsCentralSupport p z) (hqz : IsCentralSupport q z) :
    ∃ v : PartialIso M, v.initial = p ∧ v.final = q := by
  obtain ⟨v, hvp, hvq⟩ := trace_free_abelian_subequivalent e hp hq.1
    (fun r hr hrp hr0 => central_support_full e hq.1 hqz hr (hrp.trans hpz.2.1) hr0)
  have hvz : IsCentralSupport v.final z :=
    IsCentralSupport.partialIso v (by simpa only [hvp] using hpz)
  have hr := (v.final_proj.le_iff_sub hq.1).mp hvq
  have hrq : q - v.final ≤ q := sub_le_self _ v.final_proj.nonneg
  obtain ⟨c, hc, hcr⟩ := abelian_subprojection_central_cut e hq hr hrq
  have hcf : c * v.final = 0 := by
    have horth : (q - v.final) * v.final = 0 := by
      rw [sub_mul, (v.final_proj.le_iff_mul_eq_right hq.1).mp hvq,
        v.final_proj.isIdempotentElem.eq, sub_self]
    calc
      _ = (c * q) * v.final := by rw [mul_assoc,
        (v.final_proj.le_iff_mul_eq_right hq.1).mp hvq]
      _ = 0 := by rw [hcr, horth]
  have hcz := hvz.2.2 c hc hcf
  have hr0 : q - v.final = 0 := by
    calc
      _ = c * q := hcr.symm
      _ = c * (z * q) := by rw [(hq.1.le_iff_mul_eq_right hqz.1.1).mp hqz.2.1]
      _ = 0 := by rw [← mul_assoc, hcz, zero_mul]
  exact ⟨v, hvp, (sub_eq_zero.mp hr0).symm⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
