import OAI.Analysis.CircleDomains.Rigidity.TraceBalloonSystem
import OAI.Analysis.CircleDomains.Rigidity.TraceMaskRectangle
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace OAI

/-! The constructed physical balloon system in the real product
coordinates used by the rectangle Sobolev witnesses. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_trace_balloon_real_system (hmax : PlanarMaximalL2)
    (c : ℕ → ℂ) (r a : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (ha : ∀ j, 0 ≤ a j)
    (hdisj : Pairwise (Disjoint on fun j => Metric.ball (c j) (r j)))
    (hr2 : Summable (fun j => r j^2)) (ha2 : Summable (fun j => a j^2)) (m : ℕ) :
    ∃ (cutoff : ℕ → (ℝ × ℝ) → ℝ) (P : (ℝ × ℝ) → ℝ),
      (∀ j, ContDiff ℝ 1 (cutoff j)) ∧ (∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) ∧
      (∀ j x, ‖Complex.equivRealProdCLM.symm x-c j‖ ≤
        traceBalloonInnerRatio m*traceBalloonRadius r m j → cutoff j x = 0) ∧
      (∀ j x, traceBalloonRadius r m j ≤ ‖Complex.equivRealProdCLM.symm x-c j‖ → cutoff j x = 1) ∧
      Measurable P ∧ (∀ x, 0 ≤ P x) ∧ MemLp P 2 volume ∧
      (∀ᵐ x ∂volume, ∀ n, ∑ j ∈ Finset.range n, a j*‖fderiv ℝ (cutoff j) x‖ ≤ P x) := by
  obtain ⟨C,cut,P,_,hcut,hunit,hzero,hout,_,hPm,hP0,hP2,hdom⟩ :=
    exists_trace_balloon_system hmax c r a hr ha hdisj hr2 ha2 m
  let T := Complex.equivRealProdCLM.symm
  let L : ℝ := ‖T.toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  have hmp : MeasurePreserving T volume volume :=
    Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  refine ⟨(fun j x => cut j (T x)),(fun x => L*P (T x)),?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j
    exact ((hcut j).of_le (by simp)).comp T.contDiff
  · exact fun j x => hunit j (T x)
  · exact fun j x hx => hzero j (T x) hx
  · exact fun j x hx => hout j (T x) hx
  · exact measurable_const.mul (hPm.comp T.continuous.measurable)
  · exact fun x => mul_nonneg hL (hP0 _)
  · exact (hP2.comp_measurePreserving hmp).const_mul L
  · filter_upwards [hmp.quasiMeasurePreserving.ae hdom] with x hx
    intro n
    calc
      _ ≤ ∑ j ∈ Finset.range n, a j*(‖fderiv ℝ (cut j) (T x)‖*L) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (ha j)
        change ‖fderiv ℝ (cut j ∘ T) x‖ ≤ ‖fderiv ℝ (cut j) (T x)‖*L
        rw [fderiv_comp x ((hcut j).differentiable (by simp) _) T.differentiableAt,T.fderiv]
        exact ContinuousLinearMap.opNorm_comp_le _ _
      _ = L*(∑ j ∈ Finset.range n, a j*‖fderiv ℝ (cut j) (T x)‖) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ L*P (T x) := mul_le_mul_of_nonneg_left (hx n) hL

end CircleDomainRigidity

end

end OAI
