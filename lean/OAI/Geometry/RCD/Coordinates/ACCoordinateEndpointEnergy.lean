import OAI.Geometry.RCD.Coordinates.ACFrameEnergyPairing

namespace OAI

/-! # Endpoint control from the integrated coefficient energy on actual coordinate paths -/

open Set Filter MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates

theorem ac_coordinate_endpoint_energy {n : ℕ} {f : ℝ → ℝ} {b c : Fin n → ℝ → ℝ}
    {L D η : ℝ} (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hb : ∀ i, AbsolutelyContinuousOnInterval (b i) 0 1)
    (hc : ∀ i, AbsolutelyContinuousOnInterval (c i) 0 1)
    (hη : ∀ i t, t∈Icc (0:ℝ) 1 → |c i t-((1-t)*c i 0+t*c i 1)|≤η)
    (hD : 0≤D)
    (N : ℝ → ℝ) (hN : ∀ t, 0≤N t) (hNI : IntegrableOn N (Icc (0:ℝ) 1))
    (hbN : ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1),
      ‖(WithLp.toLp 2 (fun i => b i t) : Euclidean n)‖^2≤L^2+N t)
    (E : ℝ → ℝ) (hE : ∀ t, 0≤E t) (hEI : IntegrableOn E (Icc (0:ℝ) 1))
    (hderiv : ∀ᵐ t : ℝ, t∈Ioo (0:ℝ) 1 →
      (deriv f t-∑ i, b i t*deriv (c i) t)^2≤D^2*E t) :
    |f 1-f 0| ≤ Real.sqrt (L^2+∫ t in Icc (0:ℝ) 1, N t)*‖(WithLp.toLp 2 (fun i => c i 1-c i 0) : Euclidean n)‖+
      η*(∑ i, ∫ t in Icc (0:ℝ) 1, |deriv (b i) t|)+
      D*Real.sqrt (∫ t in Icc (0:ℝ) 1, E t) := by
  classical
  let w : Euclidean n := WithLp.toLp 2 (fun i => c i 1-c i 0)
  let z (i : Fin n) (t : ℝ) := c i t-(c i 0+t*w i)
  have hz (i : Fin n) : AbsolutelyContinuousOnInterval (z i) 0 1 := by
    have ha : ContDiff ℝ 1 (fun t : ℝ => c i 0+t*w i) := by fun_prop
    exact (hc i).sub ha.contDiffOn.absolutelyContinuousOnInterval
  have hz0 (i : Fin n) : z i 0=0 := by simp only [z,zero_mul,add_zero,sub_self]
  have hz1 (i : Fin n) : z i 1=0 := by
    change c i 1-(c i 0+1*(c i 1-c i 0))=0
    ring
  have hzη (i : Fin n) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : |z i t|≤η := by
    convert hη i t ht using 1
    congr 1
    change c i t-(c i 0+t*(c i 1-c i 0))=c i t-((1-t)*c i 0+t*c i 1)
    ring
  apply ac_frame_endpoint_energy w hf hb hz hz0 hz1 hzη hD N hN hNI hbN E hE hEI
  filter_upwards [hderiv,ae_all_iff.mpr (fun i => (hc i).ae_differentiableAt)] with t ht hct htin
  have he (i : Fin n) : w i+deriv (z i) t=deriv (c i) t := by
    have hd : HasDerivAt (fun s : ℝ => c i 0+s*w i) (w i) t := by
      simpa only [one_mul] using! ((hasDerivAt_id t).mul_const (w i)).const_add (c i 0)
    have hcd : DifferentiableAt ℝ (c i) t := hct i (by
      simpa only [uIcc_of_le zero_le_one] using Ioo_subset_Icc_self htin)
    have hzderiv : deriv (z i) t=deriv (c i) t-w i := (hcd.hasDerivAt.sub hd).deriv
    rw [hzderiv]
    ring
  simp_rw [he]
  exact ht htin

end RegularPointCoordinates

end

end OAI
