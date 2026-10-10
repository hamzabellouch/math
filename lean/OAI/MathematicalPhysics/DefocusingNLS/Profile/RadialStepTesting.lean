import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPrimitiveTesting

namespace OAI

/-! The test-functional associated with the limiting primitive is the radial step pressure. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radial_step_test_identity (R l b : ℝ) (hl : 0 ≤ l) (hlR : l ≤ R)
    (φ ψ : ℝ → ℝ) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφD : ∀ r ∈ Ioo 0 R, HasDerivAt φ (ψ r) r) :
    φ R*(b/12*(min R l)^12)-φ 0*(b/12*(min 0 l)^12)-
      (∫ t in (0 : ℝ)..R, ψ t*(b/12*(min t l)^12))=
        ∫ t in (0 : ℝ)..l, φ t*(b*t^11) := by
  have hR : 0 ≤ R := hl.trans hlR
  have hcont : Continuous (fun t : ℝ => ψ t*(b/12*(min t l)^12)) := by fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 l) (hcont.intervalIntegrable (μ := volume) l R)
  have hleft : (∫ t in (0 : ℝ)..l, ψ t*(b/12*(min t l)^12))=
      ∫ t in (0 : ℝ)..l, ψ t*(b/12*t^12) := by
    apply intervalIntegral.integral_congr
    intro t ht
    change ψ t*(b/12*(min t l)^12)=ψ t*(b/12*t^12)
    rw [min_eq_left ((uIcc_of_le hl ▸ ht).2)]
  have hψint : (∫ t in l..R, ψ t)=φ R-φ l :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlR hφ.continuousOn
      (fun r hr => hφD r ⟨lt_of_le_of_lt hl hr.1,hr.2⟩) (hψ.intervalIntegrable l R)
  have hright : (∫ t in l..R, ψ t*(b/12*(min t l)^12))=
      (φ R-φ l)*(b/12*l^12) := by
    calc
      _ = ∫ t in l..R, ψ t*(b/12*l^12) := by
        apply intervalIntegral.integral_congr
        intro t ht
        change ψ t*(b/12*(min t l)^12)=ψ t*(b/12*l^12)
        rw [min_eq_right ((uIcc_of_le hlR ▸ ht).1)]
      _ = _ := by rw [intervalIntegral.integral_mul_const,hψint]
  have hpow (r : ℝ) : HasDerivAt (fun t : ℝ => b/12*t^12) (b*r^11) r := by
    convert ((hasDerivAt_id r).pow 12).const_mul (b/12) using 1
    · rfl
    · simp only [id_eq,Nat.cast_ofNat,Nat.reduceSub,mul_one]
      ring
  have hparts : (∫ t in (0 : ℝ)..l, φ t*(b*t^11))=
      φ l*(b/12*l^12)-φ 0*(b/12*(0:ℝ)^12)-∫ t in (0 : ℝ)..l, ψ t*(b/12*t^12) := by
    apply intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    · simpa only [uIcc_of_le hl] using hφ.continuousOn (s := Icc 0 l)
    · fun_prop
    · intro r hr
      have hr' : r ∈ Ioo 0 l := by simpa only [min_eq_left hl,max_eq_right hl] using hr
      exact hφD r ⟨hr'.1,hr'.2.trans_le hlR⟩
    · intro r _
      exact hpow r
    · exact hψ.intervalIntegrable 0 l
    · exact (continuous_const.mul (continuous_id.pow 11)).intervalIntegrable 0 l
  rw [← hsplit,hleft,hright,min_eq_right hlR,min_eq_left hl]
  rw [hparts]
  ring

end DefocusingNLS

end OAI
