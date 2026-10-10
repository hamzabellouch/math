import Mathlib
import OAI.Probability.GaussianInformation.Kernel.Mixtures

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Projection

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace Support

lemma lintegral_pi_product {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (f : α → ℝ≥0∞) (hf : Measurable f) (m : ℕ) :
    (∫⁻ z : Fin m → α, ∏ i, f (z i) ∂Measure.pi (fun _ => μ)) = (∫⁻ z, f z ∂μ)^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [((measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => μ) 0).symm).lintegral_map_equiv]
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Fin.prod_univ_succ, Fin.zero_succAbove]
    change (∫⁻ z : α × (Fin m → α), f z.1 * ∏ i, f (z.2 i)
      ∂μ.prod (Measure.pi (fun _ => μ))) = _
    rw [lintegral_prod_mul (μ := μ) (ν := Measure.pi (fun _ : Fin m => μ))
      (g := fun z : Fin m → α => ∏ i, f (z i)) hf.aemeasurable (by
      exact (Finset.measurable_prod _ fun i _ => hf.comp (measurable_pi_apply i)).aemeasurable),
      ih, pow_succ']

noncomputable def closedBox {k : ℕ} (c : Fin k → ℝ) (η : ℝ) : Set (Fin k → ℝ) :=
  {u | ∀ i, |u i-c i| ≤ η}

lemma measurableSet_closedBox {k : ℕ} (c : Fin k → ℝ) (η : ℝ) :
    MeasurableSet (closedBox c η) := by
  simp only [closedBox, ofPred_forall]
  exact MeasurableSet.iInter fun i =>
    measurableSet_le ((measurable_pi_apply i).sub measurable_const).abs measurable_const

lemma volume_closedBox {k : ℕ} (c : Fin k → ℝ) (η : ℝ) (hη : 0 ≤ η) :
    volume (closedBox c η) = ENNReal.ofReal ((2*η)^k) := by
  have heq : closedBox c η = univ.pi (fun i => Icc (c i-η) (c i+η)) := by
    ext u
    simp only [closedBox, mem_ofPred_eq, Set.mem_pi, mem_univ, forall_true_left,
      mem_Icc, abs_le]
    congr! 1
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [heq, volume_pi, Measure.pi_pi]
  simp only [Real.volume_Icc, show ∀ i, c i+η-(c i-η)=2*η from fun i => by ring,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity)]

noncomputable def boxScale (k : ℕ) (η : ℝ) : ℝ≥0∞ := (ENNReal.ofReal ((2*η)^k))⁻¹

noncomputable def boxKernel {k : ℕ} (η : ℝ) (c u : Fin k → ℝ) : ℝ≥0∞ :=
  (closedBox c η).indicator (fun _ => boxScale k η) u

lemma measurable_boxKernel {k : ℕ} (η : ℝ) :
    Measurable (fun p : (Fin k → ℝ) × (Fin k → ℝ) => boxKernel η p.1 p.2) := by
  have hs : MeasurableSet {p : (Fin k → ℝ) × (Fin k → ℝ) | ∀ i, |p.2 i-p.1 i| ≤ η} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le
      (((measurable_pi_apply i).comp measurable_snd).sub
        ((measurable_pi_apply i).comp measurable_fst)).abs measurable_const
  exact measurable_const.indicator hs

lemma boxKernel_le {k : ℕ} (η : ℝ) (c u : Fin k → ℝ) :
    boxKernel η c u ≤ boxScale k η := Set.indicator_le_self (closedBox c η) (fun _ => boxScale k η) u

lemma boxKernel_ne_zero_mem {k : ℕ} {η : ℝ} {c u : Fin k → ℝ}
    (h : boxKernel η c u ≠ 0) : u ∈ closedBox c η := by
  by_contra hu
  exact h (Set.indicator_of_notMem hu _)

lemma lintegral_boxKernel {k : ℕ} (η : ℝ) (hη : 0 < η) (c : Fin k → ℝ) :
    (∫⁻ u, boxKernel η c u) = 1 := by
  change (∫⁻ u, (closedBox c η).indicator (fun _ => boxScale k η) u) = 1
  rw [lintegral_indicator (measurableSet_closedBox c η), lintegral_const,
    Measure.restrict_apply_univ, volume_closedBox c η hη.le]
  exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

lemma lintegral_boxKernel_product_le {k q : ℕ} (η : ℝ) (hη : 0 < η)
    (c : Fin (q+1) → Fin k → ℝ) :
    (∫⁻ u, ∏ i, boxKernel η (c i) u) ≤
      if ∀ (i : Fin q) r, |c i.succ r-c 0 r| ≤ 2*η then boxScale k η ^ q else 0 := by
  classical
  by_cases hd : ∀ (i : Fin q) r, |c i.succ r-c 0 r| ≤ 2*η
  · rw [ite_eq_left hd]
    calc
      _ ≤ ∫⁻ u, boxScale k η ^ q * boxKernel η (c 0) u := by
        apply lintegral_mono
        intro u
        dsimp only
        rw [Fin.prod_univ_succ, mul_comm]
        apply mul_le_mul_left
        simpa using Finset.prod_le_prod (s := (Finset.univ : Finset (Fin q)))
          (fun i _ => boxKernel_le η (c i.succ) u)
      _ = boxScale k η ^ q * ∫⁻ u, boxKernel η (c 0) u :=
        lintegral_const_mul _ ((measurable_boxKernel η).comp (measurable_const.prodMk measurable_id))
      _ = boxScale k η ^ q := by rw [lintegral_boxKernel η hη, mul_one]
  · rw [ite_eq_right hd]
    have hz : ∀ u, (∏ i, boxKernel η (c i) u) = 0 := by
      intro u
      by_contra hp
      have hall : ∀ i, u ∈ closedBox (c i) η := by
        intro i
        apply boxKernel_ne_zero_mem
        exact (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ _)
      apply hd
      intro i r
      have h0 := hall 0 r
      have hi := hall i.succ r
      have he := abs_sub_le (c i.succ r) (u r) (c 0 r)
      rw [abs_sub_comm (c i.succ r) (u r)] at he
      exact he.trans (by linarith)
    simp only [hz, lintegral_zero, le_refl]

end Support

open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

end Projection
end KernelPotential

end OAI
