import OAI.Analysis.BoundedHochschild.AbelianSupportEquivalence

namespace OAI

/-! Central cuts of projection supports. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma IsCentralSupport.eq_zero_iff {p z : M} (hp : IsStarProjection p)
    (h : IsCentralSupport p z) : p = 0 ↔ z = 0 := by
  constructor
  · intro hp0
    have hz := h.2.2 1 ⟨IsStarProjection.one M, fun _ => Commute.one_left _⟩ (by simp [hp0])
    simpa only [one_mul] using hz
  · intro hz0
    exact le_antisymm (hz0 ▸ h.2.1) hp.nonneg

lemma IsCentralSupport.centralCut {p t z : M} (hp : IsStarProjection p)
    (h : IsCentralSupport p t) (hz : CentralProjection z) :
    IsCentralSupport (z * p) (z * t) := by
  have hzp := hz.1.mul hp (hz.2 p)
  have hzt : CentralProjection (z * t) :=
    ⟨hz.1.mul h.1.1 (hz.2 t), fun a => (hz.2 a).mul_left (h.1.2 a)⟩
  refine ⟨hzt, (hzp.le_iff_mul_eq_left hzt.1).mpr ?_, ?_⟩
  · calc
      z * p * (z * t) = z * (p * t) :=
        central_idempotent_mul z hz.1.isIdempotentElem.eq (fun a => (hz.2 a).eq) p t
      _ = z * p := by rw [(hp.le_iff_mul_eq_left h.1.1).mp h.2.1]
  · intro c hc hcp
    have hcz : CentralProjection (c * z) :=
      ⟨hc.1.mul hz.1 (hc.2 z), fun a => (hc.2 a).mul_left (hz.2 a)⟩
    have hh := h.2.2 (c * z) hcz (by simpa only [mul_assoc] using hcp)
    simpa only [mul_assoc] using hh

lemma IsCentralSupport.centralCut_one {p z : M} (hp : IsStarProjection p)
    (h : IsCentralSupport p 1) (hz : CentralProjection z) :
    IsCentralSupport (z * p) z := by
  simpa only [mul_one] using h.centralCut hp hz

lemma IsCentralSupport.central_cut_nonzero {p z : M} (hp : IsStarProjection p)
    (h : IsCentralSupport p 1) (hz : CentralProjection z) (hz0 : z ≠ 0) : z * p ≠ 0 :=
  fun hp0 => hz0 (((h.centralCut_one hp hz).eq_zero_iff (hz.1.mul hp (hz.2 p))).mp hp0)

end KadisonRingrose
end BoundedHochschild

end

end OAI
