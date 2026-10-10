import OAI.Geometry.RCD.Harmonic.ACAffinePairing
import OAI.Geometry.RCD.Coordinates.CoordinatePathVelocity

namespace OAI

/-! # Endpoint control from the integrated affine-direction pairing -/

open Set Filter MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates

theorem ac_frame_endpoint_error_of_pairing {n : ℕ} {f : ℝ → ℝ} {b z : Fin n → ℝ → ℝ}
    (w : Euclidean n) {P D η : ℝ}
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hb : ∀ i, AbsolutelyContinuousOnInterval (b i) 0 1)
    (hz : ∀ i, AbsolutelyContinuousOnInterval (z i) 0 1)
    (hz0 : ∀ i, z i 0=0) (hz1 : ∀ i, z i 1=0)
    (hη : ∀ i t, t∈Icc (0:ℝ) 1 → |z i t|≤η)
    (hD : 0 ≤ D)
    (hpair : |∫ t in Icc (0:ℝ) 1, ∑ i, b i t*w i|≤P)
    (E : ℝ → ℝ) (hE : ∀ t, 0 ≤ E t) (hEI : IntegrableOn E (Icc (0:ℝ) 1))
    (hderiv : ∀ᵐ t : ℝ, t∈Ioo (0:ℝ) 1 →
      (deriv f t-∑ i, b i t*(w i+deriv (z i) t))^2≤D^2*E t) :
    |f 1-f 0| ≤ P+η*(∑ i, ∫ t in Icc (0:ℝ) 1, |deriv (b i) t|)+
      D*Real.sqrt (∫ t in Icc (0:ℝ) 1, E t) := by
  classical
  let ν := volume.restrict (Icc (0:ℝ) 1)
  let A t := ∑ i, b i t*w i
  let Z t := ∑ i, b i t*deriv (z i) t
  let H t := ∑ i, b i t*(w i+deriv (z i) t)
  have hbc (i : Fin n) : ContinuousOn (b i) (Icc (0:ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using (hb i).continuousOn
  have hAi (i : Fin n) : Integrable (fun t => b i t*w i) ν :=
    ((hbc i).mul continuousOn_const).integrableOn_Icc
  have hZi (i : Fin n) : Integrable (fun t => b i t*deriv (z i) t) ν := by
    have hh := (hz i).intervalIntegrable_deriv.continuousOn_mul (hb i).continuousOn
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hh
  have hA : Integrable A ν := integrable_finsetSum _ (fun i _ => hAi i)
  have hZ : Integrable Z ν := integrable_finsetSum _ (fun i _ => hZi i)
  have heq (t : ℝ) : H t=A t+Z t := by simp only [H,A,Z,mul_add,Finset.sum_add_distrib]
  have hH : Integrable H ν := (hA.add hZ).congr (Eventually.of_forall fun t => (heq t).symm)
  have hZnorm : |∫ t, Z t ∂ν| ≤ η*∑ i, ∫ t, |deriv (b i) t| ∂ν := by
    rw [show (∫ t, Z t ∂ν)=∑ i, ∫ t, b i t*deriv (z i) t ∂ν from
      integral_finsetSum _ (fun i _ => hZi i),Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
      ac_zero_endpoint_pairing_bound (hb i) (hz i) (hz0 i) (hz1 i) (hη i))
  have hHnorm : |∫ t, H t ∂ν| ≤ P+η*∑ i, ∫ t, |deriv (b i) t| ∂ν := by
    have hh : (∫ t, H t ∂ν)=(∫ t, A t ∂ν)+(∫ t, Z t ∂ν) := by
      simp_rw [heq]
      exact integral_add hA hZ
    rw [hh]
    exact (abs_add_le _ _).trans (add_le_add hpair hZnorm)
  have hs := ac_endpoint_L2_error hf hH hEI hderiv
  have hmass : 0 ≤ ∫ t in Icc (0:ℝ) 1, E t := integral_nonneg hE
  have hsq := Real.sq_sqrt hmass
  have hroot := Real.sqrt_nonneg (∫ t in Icc (0:ℝ) 1, E t)
  have herror : |f 1-f 0-(∫ t, H t ∂ν)|≤D*Real.sqrt (∫ t in Icc (0:ℝ) 1, E t) := by
    change (f 1-f 0-(∫ t, H t ∂ν))^2≤D^2*(∫ t in Icc (0:ℝ) 1, E t) at hs
    nlinarith [sq_abs (f 1-f 0-(∫ t, H t ∂ν)),mul_nonneg hD hroot]
  have ht := abs_add_le (f 1-f 0-(∫ t, H t ∂ν)) (∫ t, H t ∂ν)
  have he : f 1-f 0-(∫ t, H t ∂ν)+(∫ t, H t ∂ν)=f 1-f 0 := by ring
  rw [he] at ht
  exact ht.trans (by linarith)

end RegularPointCoordinates

end

end OAI
