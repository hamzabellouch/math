import Mathlib
import OAI.Probability.SKGap.Localization.ScalarSmallNoiseTests

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal
namespace SKGap
lemma normalLogDensity_centered (d s x : ℝ) :
    normalLogDensity d s x = -log (sqrt (2*Real.pi*s))-(x-d)^2/(2*s) := by
  unfold normalLogDensity normalLogConst
  ring

lemma gaussian_pointwise_envelope {ι : Type*} [Fintype ι] (y : ι → ℝ)
    {d s j D smin smax ψ : ℝ} (hsmin : 0 < smin) (hsl : smin ≤ s) (hsu : s ≤ smax)
    (hd : d^2 ≤ D^2)
    (hψ : (Fintype.card ι:ℝ)*ψ ≤ 3/(8*s)*(∑ i, (y i-d)^2)+3*(Fintype.card ι:ℝ)*j/2) :
    exp ((Fintype.card ι:ℝ)*ψ)*productNormal d s y ≤
      exp ((Fintype.card ι:ℝ)*(|log (sqrt (2*Real.pi*smin))|+3*j/2+D^2/(8*smin))-
        (1/(16*smax))*∑ i, (y i)^2) := by
  have hs : 0 < s := hsmin.trans_le hsl
  have hmax : 0 < smax := hs.trans_le hsu
  have hn : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hQ : 0 ≤ ∑ i, (y i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hc := sum_centered_sq_lower y d
  have hnd := mul_le_mul_of_nonneg_left hd hn
  have h1 : -(∑ i, (y i-d)^2)/(8*s) ≤
      -(∑ i, (y i)^2)/(16*s)+(Fintype.card ι:ℝ)*D^2/(8*s) := by
    have he : -(∑ i, (y i)^2)/(16*s)+(Fintype.card ι:ℝ)*D^2/(8*s) =
        (-(∑ i, (y i)^2)/2+(Fintype.card ι:ℝ)*D^2)/(8*s) := by ring
    rw [he]
    apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 8*s)
    linarith
  have h2 : -(∑ i, (y i)^2)/(16*s) ≤ -(∑ i, (y i)^2)/(16*smax) := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    gcongr
  have h3 : (Fintype.card ι:ℝ)*D^2/(8*s) ≤ (Fintype.card ι:ℝ)*D^2/(8*smin) := by
    gcongr
  have hp : 0 < sqrt (2*Real.pi*smin) := sqrt_pos.mpr (by positivity)
  have hlog : log (sqrt (2*Real.pi*smin)) ≤ log (sqrt (2*Real.pi*s)) :=
    log_le_log hp (sqrt_le_sqrt (by nlinarith [Real.pi_pos]))
  have hlog' : -log (sqrt (2*Real.pi*s)) ≤ |log (sqrt (2*Real.pi*smin))| :=
    (neg_le_neg hlog).trans (neg_le_abs _)
  have hnlog := mul_le_mul_of_nonneg_left hlog' hn
  have he : (∑ i, normalLogDensity d s (y i)) =
      -(Fintype.card ι:ℝ)*log (sqrt (2*Real.pi*s))-(∑ i, (y i-d)^2)/(2*s) := by
    simp only [normalLogDensity_centered, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, Finset.sum_div]
    ring
  rw [productNormal_eq_exp _ hs, ← exp_add, he]
  apply exp_le_exp.mpr
  calc
    _ ≤ 3/(8*s)*(∑ i, (y i-d)^2)+3*(Fintype.card ι:ℝ)*j/2+
        (-(Fintype.card ι:ℝ)*log (sqrt (2*Real.pi*s))-(∑ i, (y i-d)^2)/(2*s)) :=
      by linarith only [hψ]
    _ = (Fintype.card ι:ℝ)*(-log (sqrt (2*Real.pi*s)))+3*(Fintype.card ι:ℝ)*j/2+
        (-(∑ i, (y i-d)^2)/(8*s)) := by ring
    _ ≤ (Fintype.card ι:ℝ)*|log (sqrt (2*Real.pi*smin))|+3*(Fintype.card ι:ℝ)*j/2+
        (-(∑ i, (y i)^2)/(16*smax)+(Fintype.card ι:ℝ)*D^2/(8*smin)) :=
      add_le_add (by linarith only [hnlog]) (h1.trans (add_le_add h2 h3))
    _ = _ := by ring

end SKGap

end
end
end
end
end
end
end
end

end OAI
