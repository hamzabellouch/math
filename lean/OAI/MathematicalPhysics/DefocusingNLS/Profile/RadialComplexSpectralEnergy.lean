import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralTesting

namespace OAI

/-! The exact energy identity for complex spectral parameters.

Four real functions encode the real and imaginary parts of the two independent
components. The imaginary spectral parameter cancels by Green symmetry.
-/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialComplexSpectral_energy (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R σ τ : ℝ) (hR : 0 ≤ R)
    (q dq p dp : ℝ → ℝ) (hq : ContinuousOn q (Icc 0 R))
    (hdq : ContinuousOn dq (Icc 0 R)) (hp : ContinuousOn p (Icc 0 R))
    (hdp : ContinuousOn dp (Icc 0 R))
    (hq' : ∀ r ∈ Ioo 0 R, HasDerivAt q (dq r) r)
    (hp' : ∀ r ∈ Ioo 0 R, HasDerivAt p (dp r) r)
    (f : Fin 4 → ℝ → ℝ) (hf : ∀ j, ContDiff ℝ 2 (f j))
    (hfR : ∀ j, f j R=0) (hdfR : ∀ j, deriv (f j) R=0)
    (hsys : ∀ r ∈ Icc 0 R,
      radialScalarAction n z q (f 0) r+radialMassDensity n z r*
        radialSpectralTest n z σ (-τ) (f 2) (f 3) r=0 ∧
      radialScalarAction n z q (f 1) r+radialMassDensity n z r*
        radialSpectralTest n z σ τ (f 3) (f 2) r=0 ∧
      radialScalarAction n z p (f 2) r-radialMassDensity n z r*
        radialSpectralTest n z σ (-τ) (f 0) (f 1) r=0 ∧
      radialScalarAction n z p (f 3) r-radialMassDensity n z r*
        radialSpectralTest n z σ τ (f 1) (f 0) r=0) :
    (σ*radialScalarForm n z R q (f 0) (f 0)+radialScalarVirial n z R q dq (f 0))+
    (σ*radialScalarForm n z R q (f 1) (f 1)+radialScalarVirial n z R q dq (f 1))+
    (σ*radialScalarForm n z R p (f 2) (f 2)+radialScalarVirial n z R p dp (f 2))+
    (σ*radialScalarForm n z R p (f 3) (f 3)+radialScalarVirial n z R p dp (f 3))=0 := by
  let T0 := radialSpectralTest n z σ (-τ) (f 0) (f 1)
  let T1 := radialSpectralTest n z σ τ (f 1) (f 0)
  let T2 := radialSpectralTest n z σ (-τ) (f 2) (f 3)
  let T3 := radialSpectralTest n z σ τ (f 3) (f 2)
  let A0 := radialScalarAction n z q (f 0)
  let A1 := radialScalarAction n z q (f 1)
  let A2 := radialScalarAction n z p (f 2)
  let A3 := radialScalarAction n z p (f 3)
  have hTi (i j : Fin 4) (s t : ℝ) (u : ℝ → ℝ) (hu : ContinuousOn u (Icc 0 R)) :
      IntervalIntegrable (fun r => radialSpectralTest n z s t (f i) (f j) r*
        radialScalarAction n z u (f i) r) MeasureTheory.volume 0 R :=
    ((radialSpectralTest_continuousOn n z hX hz R s t (f i) (f j) (hf i)
      ((hf j).of_le (by norm_num))).mul
      (radialScalarAction_continuousOn n z hX hz R u (f i) hu (hf i))).intervalIntegrable_of_Icc hR
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
  rw [radialScalarForm_spectralTest n z hX hz R σ (-τ) hR q dq (f 0) (f 1)
      hq hdq hq' (hf 0) ((hf 1).of_le (by norm_num)) (hfR 0) (hdfR 0) (hfR 1),
    radialScalarForm_spectralTest n z hX hz R σ τ hR q dq (f 1) (f 0)
      hq hdq hq' (hf 1) ((hf 0).of_le (by norm_num)) (hfR 1) (hdfR 1) (hfR 0),
    radialScalarForm_spectralTest n z hX hz R σ (-τ) hR p dp (f 2) (f 3)
      hp hdp hp' (hf 2) ((hf 3).of_le (by norm_num)) (hfR 2) (hdfR 2) (hfR 3),
    radialScalarForm_spectralTest n z hX hz R σ τ hR p dp (f 3) (f 2)
      hp hdp hp' (hf 3) ((hf 2).of_le (by norm_num)) (hfR 3) (hdfR 3) (hfR 2),
    radialScalarForm_symm n z R q (f 1) (f 0),
    radialScalarForm_symm n z R p (f 3) (f 2)] at he
  linear_combination he

end DefocusingNLS

end OAI
