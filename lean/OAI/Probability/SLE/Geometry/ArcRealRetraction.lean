import OAI.Probability.SLE.Geometry.ArcHeightExtension
import OAI.Probability.SLE.Stochastic.PlanarRetractComplement

namespace OAI

/-! A simple arc attached to the real axis is a retract together with
that axis. The explicit formula collapses the two coordinates onto the
three branches of the attached arc and real line. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

theorem simple_arc_real_retraction (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    ∃ r : C(ℂ,ℂ), (∀ z, r z ∈ range p ∪ {w : ℂ | w.im=0}) ∧
      ∀ z ∈ range p ∪ {w : ℂ | w.im=0}, r z=z := by
  obtain ⟨φ,hφ,hφp,hφR⟩ := simple_arc_height_extension p hi hH
  let v (z : ℂ) : unitInterval := ⟨φ z,hφ z⟩
  have hv : Continuous v := φ.continuous.subtype_mk _
  let b (z : ℂ) : ℝ := z.re-(p (v z)).re
  have hb : Continuous b := Complex.continuous_re.sub
    (Complex.continuous_re.comp (p.continuous.comp hv))
  let t (z : ℂ) : unitInterval := ⟨max (φ z-|b z|) 0,
    le_max_right _ _,max_le (by linarith [(hφ z).2,abs_nonneg (b z)]) zero_le_one⟩
  have ht : Continuous t := ((φ.continuous.sub hb.abs).max continuous_const).subtype_mk _
  let x (z : ℂ) : ℝ := max (b z-φ z) 0-max (-b z-φ z) 0
  have hx : Continuous x := ((hb.sub φ.continuous).max continuous_const).sub
    ((hb.neg.sub φ.continuous).max continuous_const)
  let r : C(ℂ,ℂ) := ⟨fun z => p (t z)+(x z : ℂ),
    (p.continuous.comp ht).add (Complex.continuous_ofReal.comp hx)⟩
  have ht0 (z : ℂ) (hz : φ z ≤ |b z|) : t z=0 := by
    apply Subtype.ext
    exact max_eq_right (sub_nonpos.mpr hz)
  have hx0 (z : ℂ) (hz : |b z| ≤ φ z) : x z=0 := by
    have hpos : b z-φ z ≤ 0 := sub_nonpos.mpr ((le_abs_self _).trans hz)
    have hneg : -b z-φ z ≤ 0 := sub_nonpos.mpr ((neg_le_abs _).trans hz)
    simp only [x,max_eq_right hpos,max_eq_right hneg,sub_self]
  refine ⟨r,?_,?_⟩
  · intro z
    by_cases hz : |b z| ≤ φ z
    · left
      exact ⟨t z,by simp [r,hx0 z hz]⟩
    · right
      simp [r,ht0 z (le_of_not_ge hz),h0]
  · intro z hz
    rcases hz with ⟨s,rfl⟩ | hz
    · have hvp : v (p s)=s := Subtype.ext (hφp s)
      have hbp : b (p s)=0 := by simp [b,hvp]
      have htp : t (p s)=s := by
        apply Subtype.ext
        simp only [t,hφp,hbp,abs_zero,sub_zero,max_eq_left s.property.1]
      have hxp : x (p s)=0 := by
        apply hx0
        simp only [hbp,abs_zero,hφp]
        exact s.property.1
      simp [r,htp,hxp]
    · change z.im=0 at hz
      have hez : z=(z.re : ℂ) := by apply Complex.ext <;> simp [hz]
      have hφz : φ z=0 := by rw [hez,hφR]
      have hvz : v z=0 := Subtype.ext hφz
      have hbz : b z=z.re := by simp [b,hvz,h0]
      have htz : t z=0 := ht0 z (by rw [hφz]; exact abs_nonneg _)
      have hxz : x z=z.re := by
        change max (b z-φ z) 0-max (-b z-φ z) 0=z.re
        rw [hbz,hφz,sub_zero,sub_zero]
        rcases le_total 0 z.re with h | h
        · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h),sub_zero]
        · rw [max_eq_right h,max_eq_left (neg_nonneg.mpr h),zero_sub,neg_neg]
      simpa only [r,ContinuousMap.coe_mk,htz,h0,zero_add,hxz] using hez.symm

end SLEExactGauge

end

end OAI
