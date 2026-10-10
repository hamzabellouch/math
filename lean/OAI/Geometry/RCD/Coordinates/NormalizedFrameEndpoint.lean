import OAI.Geometry.RCD.Coordinates.NormalizedFrameDerivative

namespace OAI

/-! # Radius-normalized endpoints with one spatial frame error -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem normalized_frame_endpoint {n : ℕ} {f : ℝ → ℝ} {b c : Fin n → ℝ → ℝ}
    {r L D η : ℝ} (hr : 0<r) (hD : 0≤D) (hDr : D≤r)
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hb : ∀ i, AbsolutelyContinuousOnInterval (b i) 0 1)
    (hc : ∀ i, AbsolutelyContinuousOnInterval (c i) 0 1)
    (haff : ∀ i t, t∈Icc (0:ℝ) 1 → |(c i t-((1-t)*c i 0+t*c i 1))/r|≤η)
    (E : ℝ → ℝ) (hE : ∀ t, 0≤E t) (hEI : IntegrableOn E (Icc (0:ℝ) 1))
    (hbN : ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1),
      ‖(WithLp.toLp 2 (fun i => b i t) : Euclidean n)‖^2≤L^2+E t)
    (hd : ∀ᵐ t : ℝ, t∈Ioo (0:ℝ) 1 →
      (deriv f t-∑ i, b i t*deriv (c i) t)^2≤D^2*E t) :
    |f 1-f 0|/r≤Real.sqrt (L^2+∫ t in Icc (0:ℝ) 1, E t)*
      ‖(WithLp.toLp 2 (fun i => (c i 1-c i 0)/r) : Euclidean n)‖+
      η*(∑ i, ∫ t in Icc (0:ℝ) 1, |deriv (b i) t|)+
      Real.sqrt (∫ t in Icc (0:ℝ) 1, E t) := by
  have hf' : AbsolutelyContinuousOnInterval (fun t => f t/r) 0 1 := by
    simpa only [div_eq_mul_inv,mul_comm] using hf.const_mul r⁻¹
  have hc' (i : Fin n) : AbsolutelyContinuousOnInterval (fun t => c i t/r) 0 1 := by
    simpa only [div_eq_mul_inv,mul_comm] using (hc i).const_mul r⁻¹
  have haff' (i : Fin n) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      |c i t/r-((1-t)*(c i 0/r)+t*(c i 1/r))|≤η := by
    convert haff i t ht using 1
    congr 1
    ring
  have hd' : ∀ᵐ t : ℝ, t∈Ioo (0:ℝ) 1 →
      (deriv (fun s => f s/r) t-∑ i, b i t*deriv (fun s => c i s/r) t)^2≤(1:ℝ)^2*E t := by
    filter_upwards [hd,hf.ae_differentiableAt,ae_all_iff.mpr (fun i => (hc i).ae_differentiableAt)]
      with t ht hf hc htin
    have hi : t∈uIcc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using Ioo_subset_Icc_self htin
    simpa only [one_pow,one_mul] using normalized_frame_derivative (fun i => b i t) hr hD hDr (hE t)
      (hf hi) (fun i => hc i hi) (ht htin)
  have hh := ac_coordinate_endpoint_energy hf' hb hc' haff' (by norm_num : (0:ℝ)≤1)
    E hE hEI hbN E hE hEI hd'
  simpa only [← sub_div,abs_div,abs_of_pos hr,one_mul] using hh

end RegularPointCoordinates

end

end OAI
