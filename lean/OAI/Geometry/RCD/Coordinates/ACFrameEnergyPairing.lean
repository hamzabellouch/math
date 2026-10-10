import OAI.Geometry.RCD.Coordinates.ACFrameEndpointPairing

namespace OAI

/-! # The affine-direction pairing from an integrated coefficient error -/

open Set Filter MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates

theorem ac_frame_pairing_energy {n : ℕ} (b : Fin n → ℝ → ℝ) (w : Euclidean n)
    (hb : ∀ i, AbsolutelyContinuousOnInterval (b i) 0 1) (L : ℝ) (N : ℝ → ℝ)
    (hN : ∀ t, 0≤N t) (hNI : IntegrableOn N (Icc (0:ℝ) 1))
    (hbN : ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1),
      ‖(WithLp.toLp 2 (fun i => b i t) : Euclidean n)‖^2≤L^2+N t) :
    |∫ t in Icc (0:ℝ) 1, ∑ i, b i t*w i|≤
      Real.sqrt (L^2+∫ t in Icc (0:ℝ) 1, N t)*‖w‖ := by
  let ν := volume.restrict (Icc (0:ℝ) 1)
  let A t := ∑ i, b i t*w i
  have hbc (i : Fin n) : ContinuousOn (b i) (Icc (0:ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using (hb i).continuousOn
  have hAc : ContinuousOn A (Icc (0:ℝ) 1) :=
    continuousOn_finsetSum _ (fun i _ => (hbc i).mul continuousOn_const)
  have hAI : Integrable A ν := hAc.integrableOn_Icc
  have hA2 : Integrable (fun t => (A t)^2) ν := (hAc.pow 2).integrableOn_Icc
  have hAml : MemLp A 2 ν := (memLp_two_iff_integrable_sq hAI.aestronglyMeasurable).mpr hA2
  have hcs := integral_mul_sq_le_integral_sq ν A (fun _ => 1) hAml (memLp_const (1:ℝ))
  have hmass : ν.real univ=1 := by
    simp only [ν,Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,sub_zero,
      ENNReal.ofReal_one,ENNReal.toReal_one]
  have hcs' : (∫ t, A t ∂ν)^2≤∫ t, (A t)^2 ∂ν := by
    simpa only [mul_one,one_pow,integral_const,smul_eq_mul,hmass,sq_abs] using hcs
  have hpoint : ∀ᵐ t ∂ν, (A t)^2≤(L^2+N t)*‖w‖^2 := by
    filter_upwards [hbN] with t ht
    let B : Euclidean n := WithLp.toLp 2 (fun i => b i t)
    have he : A t=⟪B,w⟫_ℝ := by
      simp only [A,B,PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
      congr 1
      ext i
      ring
    have hh := mul_self_le_mul_self (abs_nonneg ⟪B,w⟫_ℝ) (abs_real_inner_le_norm B w)
    have hh' : (A t)^2≤‖B‖^2*‖w‖^2 := by simpa only [he,← pow_two,sq_abs,mul_pow] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_right ht (sq_nonneg _))
  have hi := integral_mono_ae hA2 (((integrable_const (L^2)).add hNI).mul_const (‖w‖^2)) hpoint
  rw [integral_mul_const] at hi
  simp only [Pi.add_apply] at hi
  rw [integral_add (integrable_const (L^2)) hNI,integral_const] at hi
  simp only [smul_eq_mul] at hi
  change (∫ t, (A t)^2 ∂ν)≤(ν.real univ*L^2+∫ t, N t ∂ν)*‖w‖^2 at hi
  rw [hmass,one_mul] at hi
  have hq : |∫ t, A t ∂ν|^2≤(L^2+∫ t, N t ∂ν)*‖w‖^2 := by simpa only [sq_abs] using hcs'.trans hi
  have hh := Real.le_sqrt_of_sq_le hq
  rw [Real.sqrt_mul (add_nonneg (sq_nonneg _) (integral_nonneg hN)),Real.sqrt_sq (norm_nonneg w)] at hh
  exact hh

theorem ac_frame_endpoint_energy {n : ℕ} {f : ℝ → ℝ} {b z : Fin n → ℝ → ℝ}
    (w : Euclidean n) {L D η : ℝ}
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hb : ∀ i, AbsolutelyContinuousOnInterval (b i) 0 1)
    (hz : ∀ i, AbsolutelyContinuousOnInterval (z i) 0 1)
    (hz0 : ∀ i, z i 0=0) (hz1 : ∀ i, z i 1=0)
    (hη : ∀ i t, t∈Icc (0:ℝ) 1 → |z i t|≤η) (hD : 0≤D)
    (N : ℝ → ℝ) (hN : ∀ t, 0≤N t) (hNI : IntegrableOn N (Icc (0:ℝ) 1))
    (hbN : ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1),
      ‖(WithLp.toLp 2 (fun i => b i t) : Euclidean n)‖^2≤L^2+N t)
    (E : ℝ → ℝ) (hE : ∀ t, 0≤E t) (hEI : IntegrableOn E (Icc (0:ℝ) 1))
    (hderiv : ∀ᵐ t : ℝ, t∈Ioo (0:ℝ) 1 →
      (deriv f t-∑ i, b i t*(w i+deriv (z i) t))^2≤D^2*E t) :
    |f 1-f 0|≤Real.sqrt (L^2+∫ t in Icc (0:ℝ) 1, N t)*‖w‖+
      η*(∑ i, ∫ t in Icc (0:ℝ) 1, |deriv (b i) t|)+
      D*Real.sqrt (∫ t in Icc (0:ℝ) 1, E t) :=
  ac_frame_endpoint_error_of_pairing w hf hb hz hz0 hz1 hη hD
    (ac_frame_pairing_energy b w hb L N hN hNI hbN) E hE hEI hderiv

end RegularPointCoordinates

end

end OAI
