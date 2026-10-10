import OAI.Analysis.LipschitzHilbert.Estimates.MaskParameters
import OAI.Analysis.LipschitzHilbert.Estimates.TopWeightIntegral

namespace OAI

/-! The sinc mask in the manuscript's actual slope coordinates, with
parameters fixed uniformly before choosing the finite top family. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert
namespace SlopeBox

def mask (T : SlopeBox) (L A : ℝ) (z : ℝ × ℝ) : ℝ :=
  topSincMask L A (T.horizontal z) (T.transverse z)

theorem weight_eq_topShape (T : SlopeBox) (K D : ℝ) (z : ℝ × ℝ) :
    T.weight K D z = topShape K D (T.horizontal z) (T.transverse z) := rfl

theorem mask_continuous (T : SlopeBox) (L A : ℝ) : Continuous (T.mask L A) := by
  unfold mask topSincMask sincProductMask horizontal transverse
  apply Continuous.pow
  apply Continuous.mul
  · apply Real.continuous_sinc.comp
    fun_prop
  · apply Real.continuous_sinc.comp
    fun_prop

theorem weight_continuous (T : SlopeBox) (K D : ℝ) (hK : 0 < K) : Continuous (T.weight K D) := by
  unfold weight radius horizontal transverse
  apply Continuous.mul continuous_const
  apply Continuous.rpow_const
  · fun_prop
  · intro z
    left
    have h : 0 ≤ |(z.1-T.x)/T.length|+|((z.2-T.y)-T.slope*(z.1-T.x))/T.width| :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    positivity

end SlopeBox

theorem exists_uniform_top_mask_error (C H A1 D : ℝ) (hC : 0 ≤ C) (hH : 0 ≤ H) (hD : 0 < D) :
    ∃ A L0 : ℝ, 2 < A ∧ 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (ι E : Type) [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
        (T : ι → SlopeBox) (F : ι → E) (z : ℝ × ℝ),
      (∀ i, ‖F i‖ ≤ L^C*((T i).weight (L^A1) D z)^8) →
      ‖(∑ i, F i)-(∑ i, (T i).mask L A z • F i)‖ ≤
        L^(-H)*∑ i, (T i).weight (L^A1) D z := by
  obtain ⟨A,L0,hA,hL0,hmask⟩ := exists_mask_parameters C H A1 D hC hH hD
  refine ⟨A,L0,hA,hL0,?_⟩
  intro L hL ι E _ _ _ T F z hF
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith : 0 < L0) hL
  apply norm_sum_sub_mask_le F (fun i => (T i).mask L A z)
    (fun i => (T i).weight (L^A1) D z) (L^C) (L^(-H)) (by positivity) (by positivity)
    (fun i => (T i).weight_pos (Real.rpow_pos_of_pos hLpos _) D z |>.le) hF
  intro i
  exact hmask L hL ((T i).horizontal z) ((T i).transverse z)

end LipschitzHilbert

end

end OAI
