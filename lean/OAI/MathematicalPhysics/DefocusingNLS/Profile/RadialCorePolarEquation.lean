import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolarJet
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPlateauPhase
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolarBalance

namespace OAI

/-! The real limiting core equations reconstruct the actual complex free equation. -/

open Set Filter Topology
namespace DefocusingNLS

theorem radial_core_polar_free (R ρ b : ℝ) (hρ0 : 0 < ρ) (hρR : ρ < R)
    (A D : ℝ → ℝ) (hA : Continuous A) (hD : Continuous D)
    (hAP : ∀ r ∈ Icc 0 R, 0 < A r)
    (hcore : EqOn A (fun _ => 1) (Icc 0 ρ)) (hDρ : D ρ=0)
    (hAD : ∀ r ∈ Ioo ρ R, HasDerivAt A (D r) r)
    (hDE : ∀ r ∈ Ioo ρ R, HasDerivAt D
      (-11/r*D r-radialAmplitudePotential 6 b A r*A r) r) :
    let F := radialPolar (radialClampedAmplitude R A) (radialPhase 6 (radialClampedAmplitude R A))
    let G := radialPolarSlope (radialClampedAmplitude R A) D
      (fun r => (radialVelocity 6 (radialClampedAmplitude R A) r-r/2)/2)
      (radialPhase 6 (radialClampedAmplitude R A))
    Continuous F ∧ Continuous G ∧ F ρ=1 ∧ G ρ=0 ∧
      (∀ r ∈ Ioo ρ R, HasDerivAt F (G r) r ∧ HasDerivAt G
        (-radialFreeCoefficient r*G r-(b : ℂ)*F r) r) ∧
      (∀ r ∈ Icc ρ R, ‖F r‖=A r) := by
  let B := radialClampedAmplitude R A
  have hR : 0 ≤ R := by linarith
  have hB : Continuous B := radialClampedAmplitude_continuous R A hA
  have hBP : ∀ r, B r ≠ 0 := fun r => (hAP _ (radialClamp_mem R r hR)).ne'
  let v := fun r => (radialVelocity 6 B r-r/2)/2
  let φ := radialPhase 6 B
  have hv : Continuous v := ((continuous_radialVelocity 6 B hB hBP).sub
    (continuous_id.div_const 2)).div_const 2
  have hφ : Continuous φ := (radialPhase_differentiable 6 B hB hBP).continuous
  have hec : Continuous (fun r => Complex.exp (Complex.I*(φ r : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hφ))
  have hF : Continuous (radialPolar B φ) := (Complex.continuous_ofReal.comp hB).mul hec
  have hG : Continuous (radialPolarSlope B D v φ) :=
    ((Complex.continuous_ofReal.comp hD).add
      ((continuous_const.mul (Complex.continuous_ofReal.comp hB)).mul
        (Complex.continuous_ofReal.comp hv))).mul hec
  have hρI : ρ ∈ Icc 0 R := ⟨hρ0.le,hρR.le⟩
  have hBρ : B ρ=1 := (radialClampedAmplitude_eq R A ρ hρI).trans
    (hcore ⟨hρ0.le,le_rfl⟩)
  have hAv : radialAverage (fun t => (B t)^2) ρ=1/12 := by
    rw [radialAverage_congr _ (fun _ => (1 : ℝ)) ρ hρ0.le (by
      intro t ht
      have hBt : B t=1 := (radialClampedAmplitude_eq R A t ⟨ht.1,ht.2.trans hρR.le⟩).trans
        (hcore ht)
      simp only [hBt,one_pow]),radialAverage_const]
  have hvρ : v ρ=0 := by
    dsimp [v,radialVelocity,radialVelocityRatio]
    rw [hBρ,hAv]
    ring
  refine ⟨hF,hG,?_,?_,?_,?_⟩
  · change radialPolar B φ ρ=1
    have hφρ : φ ρ=0 := radial_phase_zero_on_plateau R ρ hρ0.le hρR.le A hcore ρ ⟨hρ0.le,le_rfl⟩
    simp [radialPolar,hφρ,hBρ]
  · change radialPolarSlope B D v φ ρ=0
    simp [radialPolarSlope,hDρ,hvρ]
  · intro r hr
    have hrI : r ∈ Ioo 0 R := ⟨hρ0.trans hr.1,hr.2⟩
    have hrC : r ∈ Icc 0 R := ⟨hrI.1.le,hrI.2.le⟩
    have hrne : r ≠ 0 := hrI.1.ne'
    have hBr : B r=A r := radialClampedAmplitude_eq R A r hrC
    have hAB : HasDerivAt B (D r) r := by
      apply (hAD r hr).congr_of_eventuallyEq
      filter_upwards [isOpen_Ioo.mem_nhds hrI] with t ht
      exact radialClampedAmplitude_eq R A t ⟨ht.1.le,ht.2.le⟩
    have hφr : HasDerivAt φ (v r) r := radialPhase_hasDerivAt 6 B hB hBP r
    let w := radialVelocity 6 B r
    let w₁ := 6-11*radialVelocityRatio 6 B r-2*w*D r/B r
    let d₁ := -11/r*D r-radialAmplitudePotential 6 b A r*A r
    have hvr : HasDerivAt v ((w₁-1/2)/2) r :=
      ((radialVelocity_hasDerivAt_local 6 (D r) B hB r hrne (hBP r) hAB).sub
        ((hasDerivAt_id r).div_const 2)).div_const 2
    have hw : w₁=6-2*0-11/r*w-2*w*D r/A r := by
      dsimp [w₁,w]
      rw [hBr]
      dsimp [radialVelocity]
      field_simp [hrne]
      ring
    have hV : radialAmplitudePotential 6 b A r=b+r^2/16-w^2/4 := by
      dsimp [w]
      rw [radialVelocity_clamped_eq 6 R A r hrC]
      dsimp [radialAmplitudePotential,radialVelocity]
      ring
    have hRe := radialPolar_real_balance (A r) (D r) d₁ w r b 0 (by
      dsimp [d₁]
      rw [hV]
      ring)
    have hIm := radialPolar_imag_balance (A r) (D r) w w₁ r 0 (hAP r hrC).ne' hrne hw
    refine ⟨radialPolarJet_hasDerivAt B D v φ r hAB hφr,?_⟩
    apply radialPolarJet_free B D v φ r b d₁ ((w₁-1/2)/2) hAB (hDE r hr) hφr hvr
    · simpa only [hBr,v,w,zero_mul] using hRe
    · simpa only [hBr,v,w,zero_mul,add_zero] using hIm
  · intro r hr
    rw [radialPolar_norm]
    rw [radialClampedAmplitude_eq R A r ⟨hρ0.le.trans hr.1,hr.2⟩,
      abs_of_pos (hAP r ⟨hρ0.le.trans hr.1,hr.2⟩)]

end DefocusingNLS

end OAI
