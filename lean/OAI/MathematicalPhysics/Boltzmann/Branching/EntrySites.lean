import OAI.MathematicalPhysics.Boltzmann.Branching.LargeOutput
import OAI.MathematicalPhysics.Boltzmann.Branching.SmallFirstGain
import OAI.MathematicalPhysics.Boltzmann.Branching.ThreeCollisionTimes
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricPositiveCompact

namespace OAI

section

/-! # A short three-collision path stays in a bounded region outside the hole -/

noncomputable section

open Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem nearby_entry_cylinder {x y : V} {L X : ℝ}
    (hx : ‖x‖ ≤ X) (hr : L+1 < ‖transverse x‖) (hd : ‖y-x‖ ≤ 1) :
    L < ‖transverse y‖ ∧ ‖y‖ ≤ X+1 := by
  have ht := norm_sub_norm_le (transverse x) (transverse y)
  have he : ‖transverse x-transverse y‖ ≤ 1 := by
    rw [← PlaneChart.transverse_sub]
    exact (LargeOutput.transverse_norm_le (x-y)).trans (by rwa [norm_sub_rev])
  have hn := norm_sub_norm_le y x
  exact ⟨by linarith,by linarith⟩

theorem short_three_flights {R h s₀ s₁ s₂ : ℝ} {x v₀ v₁ v₂ : V}
    (hR : 0 ≤ R) (hsmall : (R+6)*h ≤ 1)
    (hs₀ : s₀ ∈ Icc 0 h) (hs₁ : s₁ ∈ Icc 0 h) (hs₂ : s₂ ∈ Icc 0 h)
    (hv₀ : ‖v₀‖ ≤ R) (hv₁ : ‖v₁‖ ≤ 3) (hv₂ : ‖v₂‖ ≤ 3) :
    ‖(x+s₀ • v₀+s₁ • v₁+s₂ • v₂)-x‖ ≤ 1 := by
  have ht₀ : ‖s₀ • v₀‖ ≤ h*R := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs₀.1]
    exact (mul_le_mul_of_nonneg_left hv₀ hs₀.1).trans
      (mul_le_mul_of_nonneg_right hs₀.2 hR)
  have ht₁ : ‖s₁ • v₁‖ ≤ h*3 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs₁.1]
    exact (mul_le_mul_of_nonneg_left hv₁ hs₁.1).trans
      (mul_le_mul_of_nonneg_right hs₁.2 (by norm_num))
  have ht₂ : ‖s₂ • v₂‖ ≤ h*3 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs₂.1]
    exact (mul_le_mul_of_nonneg_left hv₂ hs₂.1).trans
      (mul_le_mul_of_nonneg_right hs₂.2 (by norm_num))
  have he : (x+s₀ • v₀+s₁ • v₁+s₂ • v₂)-x =
      (s₀ • v₀+s₁ • v₁)+s₂ • v₂ := by module
  rw [he]
  have h₁ := norm_add_le (s₀ • v₀) (s₁ • v₁)
  have h₂ := norm_add_le (s₀ • v₀+s₁ • v₁) (s₂ • v₂)
  nlinarith

end BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem nearby_beamDensity_lower {θ η α γ L X T : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hL : 0 < L) (hX : 0 ≤ X) (hT : 0 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : Velocity), ‖x‖ ≤ X → L+1 < ‖transverse x‖ →
      ∀ (y : Velocity), ‖y-x‖ ≤ 1 → ∀ t ∈ Icc 0 T, ∀ σ : ℝ, |σ| = 1 →
        c ≤ beamDensity θ η α γ 1 σ (t,y) := by
  obtain ⟨c,hc,hbound⟩ := beamDensity_compact_lower hθ hη hα hγ hL
    (show 0 < X+1 by linarith) hT (show 0 ≤ X+1 by linarith)
  refine ⟨c,hc,?_⟩
  intro x hx hr y hxy t ht σ hσ
  obtain ⟨hyl,hyn⟩ := ReferenceGeometry.nearby_entry_cylinder hx hr hxy
  exact hbound (t,y) ht ⟨hyl.le,(LargeOutput.transverse_norm_le y).trans hyn⟩
    ((SmallInputGeometry.abs_axial_le_norm y).trans hyn) σ hσ

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The three physical collision sites in the entry path -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.ReferenceGeometry

def entrySite₀ (t : ℝ) (x v : V) (s : ThreeWaits) : ℝ × V :=
  (t+s.1,x+s.1 • v)

def entrySite₁ (t : ℝ) (x v : V) (s : ThreeWaits) (u : V) : ℝ × V :=
  (t+s.1+s.2.1,x+s.1 • v+s.2.1 • u)

def entrySite₂ (t : ℝ) (x v : V) (s : ThreeWaits) (u z : V) : ℝ × V :=
  (t+s.1+s.2.1+s.2.2,x+s.1 • v+s.2.1 • u+s.2.2 • z)

theorem entrySites_bounded {R h t T : ℝ} {x v u z : V} {s : ThreeWaits}
    (hR : 0 ≤ R) (hsmall : (R+6)*h ≤ 1) (ht : 0 ≤ t) (hT : t+3*h ≤ T)
    (hs₀ : s.1 ∈ Icc 0 h) (hs₁ : s.2.1 ∈ Icc 0 h) (hs₂ : s.2.2 ∈ Icc 0 h)
    (hv : ‖v‖ ≤ R) (hu : ‖u‖ ≤ 3) (hz : ‖z‖ ≤ 3) :
    ((entrySite₀ t x v s).1 ∈ Icc 0 T ∧ ‖(entrySite₀ t x v s).2-x‖ ≤ 1) ∧
    ((entrySite₁ t x v s u).1 ∈ Icc 0 T ∧ ‖(entrySite₁ t x v s u).2-x‖ ≤ 1) ∧
    ((entrySite₂ t x v s u z).1 ∈ Icc 0 T ∧ ‖(entrySite₂ t x v s u z).2-x‖ ≤ 1) := by
  have hh : 0 ≤ h := hs₀.1.trans hs₀.2
  have hs0 : (0:ℝ) ∈ Icc 0 h := ⟨le_rfl,hh⟩
  have hzero : ‖(0:V)‖ ≤ 3 := by norm_num
  have hd₀ := short_three_flights (x := x) hR hsmall hs₀ hs0 hs0 hv hzero hzero
  have hd₁ := short_three_flights (x := x) hR hsmall hs₀ hs₁ hs0 hv hu hzero
  have hd₂ := short_three_flights (x := x) hR hsmall hs₀ hs₁ hs₂ hv hu hz
  simp only [zero_smul,add_zero] at hd₀ hd₁
  refine ⟨⟨⟨?_,?_⟩,hd₀⟩,⟨⟨?_,?_⟩,hd₁⟩,⟨⟨?_,?_⟩,hd₂⟩⟩ <;>
    dsimp [entrySite₀,entrySite₁,entrySite₂] <;>
    linarith [hs₀.1,hs₀.2,hs₁.1,hs₁.2,hs₂.1,hs₂.2]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
