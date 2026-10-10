import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAngularScalar

namespace OAI

/-! The exact energy identity in each spherical-harmonic channel.

Four real functions encode the real and imaginary parts of the two independent
components. The imaginary spectral parameter cancels by Green symmetry.
-/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialAngularComplexSpectral_energy_boundary (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (η R σ τ : ℝ) (hR : 0 ≤ R)
    (q dq p dp : ℝ → ℝ) (hq : ContinuousOn q (Icc 0 R))
    (hdq : ContinuousOn dq (Icc 0 R)) (hp : ContinuousOn p (Icc 0 R))
    (hdp : ContinuousOn dp (Icc 0 R))
    (hq' : ∀ r ∈ Ioo 0 R, HasDerivAt q (dq r) r)
    (hp' : ∀ r ∈ Ioo 0 R, HasDerivAt p (dp r) r)
    (f : Fin 4 → ℝ → ℝ) (hf : ∀ j, ContDiff ℝ 2 (f j))
    (hsys : ∀ r ∈ Icc 0 R,
      radialAngularScalarAction n z η q (f 0) r+radialMassDensity n z r*
        radialSpectralTest n z σ (-τ) (f 2) (f 3) r=0 ∧
      radialAngularScalarAction n z η q (f 1) r+radialMassDensity n z r*
        radialSpectralTest n z σ τ (f 3) (f 2) r=0 ∧
      radialAngularScalarAction n z η p (f 2) r-radialMassDensity n z r*
        radialSpectralTest n z σ (-τ) (f 0) (f 1) r=0 ∧
      radialAngularScalarAction n z η p (f 3) r-radialMassDensity n z r*
        radialSpectralTest n z σ τ (f 1) (f 0) r=0) :
    (σ*radialAngularScalarForm n z η R q (f 0) (f 0)+radialAngularScalarVirial n z η R q dq (f 0)+
      radialAngularScalarBoundary n z η R σ (-τ) q (f 0) (f 1))+
    (σ*radialAngularScalarForm n z η R q (f 1) (f 1)+radialAngularScalarVirial n z η R q dq (f 1)+
      radialAngularScalarBoundary n z η R σ τ q (f 1) (f 0))+
    (σ*radialAngularScalarForm n z η R p (f 2) (f 2)+radialAngularScalarVirial n z η R p dp (f 2)+
      radialAngularScalarBoundary n z η R σ (-τ) p (f 2) (f 3))+
    (σ*radialAngularScalarForm n z η R p (f 3) (f 3)+radialAngularScalarVirial n z η R p dp (f 3)+
      radialAngularScalarBoundary n z η R σ τ p (f 3) (f 2))=0 := by
  let T0 := radialSpectralTest n z σ (-τ) (f 0) (f 1)
  let T1 := radialSpectralTest n z σ τ (f 1) (f 0)
  let T2 := radialSpectralTest n z σ (-τ) (f 2) (f 3)
  let T3 := radialSpectralTest n z σ τ (f 3) (f 2)
  let A0 := radialAngularScalarAction n z η q (f 0)
  let A1 := radialAngularScalarAction n z η q (f 1)
  let A2 := radialAngularScalarAction n z η p (f 2)
  let A3 := radialAngularScalarAction n z η p (f 3)
  have hTi (i j : Fin 4) (s t : ℝ) (u : ℝ → ℝ) (hu : ContinuousOn u (Icc 0 R)) :
      IntervalIntegrable (fun r => radialSpectralTest n z s t (f i) (f j) r*
        radialAngularScalarAction n z η u (f i) r) MeasureTheory.volume 0 R :=
    ((radialSpectralTest_continuousOn n z hX hz R s t (f i) (f j) (hf i)
      ((hf j).of_le (by norm_num))).mul
      (radialAngularScalarAction_continuousOn n z hX hz η R u (f i) hu (hf i))).intervalIntegrable_of_Icc hR
  have h0 := hTi 0 1 σ (-τ) q hq
  have h1 := hTi 1 0 σ τ q hq
  have h2 := hTi 2 3 σ (-τ) p hp
  have h3 := hTi 3 2 σ τ p hp
  have he : (∫ r in (0 : ℝ)..R,
      (T0 r*A0 r+T1 r*A1 r)+(T2 r*A2 r+T3 r*A3 r))=0 := by
    calc
      _ = ∫ _r in (0 : ℝ)..R, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le hR] at hr
        obtain ⟨hA,hB,hC,hD⟩ := hsys r hr
        exact radialSkewPair_cancellation _ _ _ _ _ _ _ _ _ hA hB hC hD
      _ = 0 := by simp
  rw [intervalIntegral.integral_add (h0.add h1) (h2.add h3),
    intervalIntegral.integral_add h0 h1,intervalIntegral.integral_add h2 h3] at he
  rw [radialAngularScalarForm_spectralTest_boundary n z hX hz η R σ (-τ) hR q dq (f 0) (f 1)
      hq hdq hq' (hf 0) ((hf 1).of_le (by norm_num)),
    radialAngularScalarForm_spectralTest_boundary n z hX hz η R σ τ hR q dq (f 1) (f 0)
      hq hdq hq' (hf 1) ((hf 0).of_le (by norm_num)),
    radialAngularScalarForm_spectralTest_boundary n z hX hz η R σ (-τ) hR p dp (f 2) (f 3)
      hp hdp hp' (hf 2) ((hf 3).of_le (by norm_num)),
    radialAngularScalarForm_spectralTest_boundary n z hX hz η R σ τ hR p dp (f 3) (f 2)
      hp hdp hp' (hf 3) ((hf 2).of_le (by norm_num)),
    radialAngularScalarForm_symm n z η R q (f 1) (f 0),
    radialAngularScalarForm_symm n z η R p (f 3) (f 2)] at he
  linear_combination he

end DefocusingNLS

end OAI
