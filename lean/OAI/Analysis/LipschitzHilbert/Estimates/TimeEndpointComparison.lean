import OAI.Analysis.LipschitzHilbert.Fourier.SharpKernelComparison
import Mathlib.Algebra.Order.Archimedean.Basic

namespace OAI

/-! A factor-two change of the inner time endpoint costs a fixed L1
constant. Every positive inner endpoint has such a dyadic representative. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_close_lower (r s R t : ℝ) (hr : 0<r)
    (hrs : r≤s) (hsr : s≤2*r) :
    ‖sharpTimeKernel r R t-sharpTimeKernel s R t‖≤3*timeErrorEnvelope r t := by
  have hq := timeErrorEnvelope_nonneg r t hr
  by_cases hs : s< |t|
  · have hr' : r< |t| := hrs.trans_lt hs
    simp only [sharpTimeKernel,hr',hs,true_and,sub_self,norm_zero]
    positivity
  · by_cases hr' : r< |t|
    · by_cases hR : |t|<R
      · have ht : 0< |t| := hr.trans hr'
        have ht2 : |t|≤2*r := (le_of_not_gt hs).trans hsr
        have hd : 0<r^2+t^2 := by positivity
        have hpoly : r^2+t^2≤3*r*|t| := by
          nlinarith [sq_abs t,mul_nonneg (sub_nonneg.mpr hr'.le) (sub_nonneg.mpr ht2)]
        have hcond1 : r< |t| ∧ |t|<R := ⟨hr',hR⟩
        have hcond2 : ¬(s< |t| ∧ |t|<R) := fun h => hs h.1
        simp only [sharpTimeKernel,ite_eq_left hcond1,ite_eq_right hcond2,sub_zero,
          norm_inv,Complex.norm_real,Real.norm_eq_abs,timeErrorEnvelope]
        rw [←mul_div_assoc,inv_eq_one_div]
        apply (div_le_div_iff₀ ht hd).2
        nlinarith only [hpoly]
      · have hcond1 : ¬(r< |t| ∧ |t|<R) := fun h => hR h.2
        have hcond2 : ¬(s< |t| ∧ |t|<R) := fun h => hR h.2
        simp only [sharpTimeKernel,ite_eq_right hcond1,ite_eq_right hcond2,sub_self,norm_zero]
        positivity
    · have hcond1 : ¬(r< |t| ∧ |t|<R) := fun h => hr' h.1
      have hcond2 : ¬(s< |t| ∧ |t|<R) := fun h => hs h.1
      simp only [sharpTimeKernel,ite_eq_right hcond1,ite_eq_right hcond2,sub_self,norm_zero]
      positivity

theorem sharpTimeKernel_close_lower_integral (r s R : ℝ) (hr : 0<r)
    (hrs : r≤s) (hsr : s≤2*r) :
    Integrable (fun t => sharpTimeKernel r R t-sharpTimeKernel s R t) ∧
      (∫ t, ‖sharpTimeKernel r R t-sharpTimeKernel s R t‖)≤3*Real.pi := by
  have hm := (sharpTimeKernel_measurable r R).sub (sharpTimeKernel_measurable s R)
  have hi := (timeErrorEnvelope_integrable r hr).const_mul 3
  have hb (t) := sharpTimeKernel_close_lower r s R t hr hrs hsr
  have he := hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨he,?_⟩
  calc
    _ ≤ ∫ t, 3*timeErrorEnvelope r t := integral_mono he.norm hi hb
    _ = 3*Real.pi := by rw [integral_const_mul,timeErrorEnvelope_integral r hr]

theorem exists_dyadic_time_endpoint (epsilon R : ℝ) (he : 0<epsilon) (heR : epsilon≤R) :
    ∃ N : ℕ, epsilon≤R/(2:ℝ)^N ∧ R/(2:ℝ)^N<2*epsilon := by
  have hR : 0<R := he.trans_le heR
  obtain ⟨N,hlo,hhi⟩ := exists_nat_pow_near ((le_div_iff₀ he).2 (by simpa using heR))
    (by norm_num : (1:ℝ)<2)
  refine ⟨N,?_,?_⟩
  · apply (le_div_iff₀ (pow_pos (by norm_num) N)).2
    simpa only [mul_comm] using (le_div_iff₀ he).1 hlo
  · apply (div_lt_iff₀ (pow_pos (by norm_num) N)).2
    have h := (div_lt_iff₀ he).1 hhi
    rw [pow_succ] at h
    nlinarith only [h]

end LipschitzHilbert.PacketRepresentation

end

end OAI
