import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.CascadeRecursion
import OAI.Probability.SKBarriers.Scalar.ThermalMoments

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section CascadeProbability
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in

theorem cascadeMoment_nonneg (n : ℕ) (m : Fin n → ℝ)
    (f g : CascadeSpace E n → ℝ) (hg : ∀ z, 0 ≤ g z) (x : E) :
    0 ≤ cascadeMoment n m f g x := by
  induction n with
  | zero => exact hg x
  | succ n ih =>
    apply ih
    intro z
    exact integral_nonneg (fun y => hg (z,y))

theorem cascadeMoment_const (n : ℕ) (m : Fin n → ℝ)
    (f : CascadeSpace E n → ℝ) (hf : BoundedDerivs f) (a : ℝ) :
    cascadeMoment n m f (fun _ => a) = fun _ => a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : gaussianAverage (m (Fin.last n)) f (fun _ => a) = fun _ => a := by
      funext z
      let := gaussianStepLaw_probability hf (m (Fin.last n)) z
      simp only [gaussianAverage,integral_const,probReal_univ,one_smul]
    rw [cascadeMoment,h]
    exact ih _ _ (hf.gaussianStep _)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem cascadeMoment_const_mul (n : ℕ) (m : Fin n → ℝ)
    (f g : CascadeSpace E n → ℝ) (a : ℝ) :
    cascadeMoment n m f (fun z => a*g z) = fun x => a*cascadeMoment n m f g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : gaussianAverage (m (Fin.last n)) f (fun z => a*g z) =
        fun z => a*gaussianAverage (m (Fin.last n)) f g z := by
      funext z; exact integral_const_mul a _
    rw [cascadeMoment,h,ih]
    rfl

theorem cascadeMoment_sum {T : Type} [Fintype T] (n : ℕ) (m : Fin n → ℝ)
    (f : CascadeSpace E n → ℝ) (hf : BoundedDerivs f)
    (g : T → CascadeSpace E n → ℝ) (hg : ∀ t, Continuous (g t))
    (C : T → ℝ) (hC : ∀ t, 0 ≤ C t) (hb : ∀ t z, ‖g t z‖ ≤ C t) :
    cascadeMoment n m f (fun z => ∑ t, g t z) =
      fun x => ∑ t, cascadeMoment n m f (g t) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : gaussianAverage (m (Fin.last n)) f (fun z => ∑ t, g t z) =
        fun z => ∑ t, gaussianAverage (m (Fin.last n)) f (g t) z := by
      funext z
      let := gaussianStepLaw_probability hf (m (Fin.last n)) z
      apply integral_finsetSum
      intro t _
      exact Integrable.of_bound ((hg t).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
        (C t) (ae_of_all _ (fun y => hb t (z,y)))
    rw [cascadeMoment,h]
    exact ih _ _ (hf.gaussianStep _) _
      (fun t => gaussianAverage_continuous hf _ (hg t) (hC t) (hb t))
      (fun t z => gaussianAverage_norm_le hf _ (hb t) z)

variable {S : Type} [Fintype S] [Nonempty S]

def cascadeSpinWeight (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace E n →L[ℝ] ℝ) (x : E) (s : S) : ℝ :=
  cascadeMoment n m (affineLogPartition c L) (fun z => affineGibbs c L z s) x

theorem affineGibbs_continuous (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (s : S) :
    Continuous (fun x => affineGibbs c L x s) := by
  exact (Real.continuous_exp.comp (continuous_const.add (L s).continuous)).div
    (continuous_finsetSum _ (fun t _ => Real.continuous_exp.comp (continuous_const.add (L t).continuous)))
    (fun x => (affinePartition_pos c L x).ne')

theorem affineGibbs_le_one (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x : E) (s : S) :
    affineGibbs c L x s ≤ 1 := by
  rw [← affineGibbs_sum c L x]
  exact Finset.single_le_sum (fun t _ => (affineGibbs_pos c L x t).le) (Finset.mem_univ s)

theorem affineGibbs_norm_le_one (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x : E) (s : S) :
    ‖affineGibbs c L x s‖ ≤ 1 := by
  rw [Real.norm_eq_abs,abs_of_pos (affineGibbs_pos c L x s)]
  exact affineGibbs_le_one c L x s

theorem cascadeSpinWeight_nonneg (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace E n →L[ℝ] ℝ) (x : E) (s : S) :
    0 ≤ cascadeSpinWeight n m c L x s :=
  cascadeMoment_nonneg n m _ _ (fun z => (affineGibbs_pos c L z s).le) x

theorem cascadeSpinWeight_sum (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace E n →L[ℝ] ℝ) (x : E) :
    ∑ s, cascadeSpinWeight n m c L x s = 1 := by
  have H := congrFun (cascadeMoment_sum n m (affineLogPartition c L)
    (affineLogPartition_boundedDerivs c L) (fun s z => affineGibbs c L z s)
    (affineGibbs_continuous c L) (fun _ => 1) (by intro; norm_num)
    (fun s z => affineGibbs_norm_le_one c L z s)) x
  simp_rw [affineGibbs_sum] at H
  rw [cascadeMoment_const n m _ (affineLogPartition_boundedDerivs c L)] at H
  exact H.symm

theorem cascadeMoment_affineMoment (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace E n →L[ℝ] ℝ) (g : S → ℝ) (x : E) :
    cascadeMoment n m (affineLogPartition c L) (affineMoment c L g) x =
      ∑ s, cascadeSpinWeight n m c L x s*g s := by
  have H := congrFun (cascadeMoment_sum n m (affineLogPartition c L)
    (affineLogPartition_boundedDerivs c L) (fun s z => g s*affineGibbs c L z s)
    (fun s => continuous_const.mul (affineGibbs_continuous c L s)) (fun s => ‖g s‖)
    (fun s => norm_nonneg _) (fun s z => by
      rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (affineGibbs_norm_le_one c L z s) (norm_nonneg _)).trans_eq (mul_one _))) x
  simp_rw [cascadeMoment_const_mul] at H
  change cascadeMoment n m (affineLogPartition c L) (fun z => ∑ s, affineGibbs c L z s*g s) x = _
  simpa only [cascadeSpinWeight,mul_comm] using H

theorem cascadeSpinWeight_regular (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace E n →L[ℝ] ℝ) (s : S) :
    Continuous (fun x => cascadeSpinWeight n m c L x s) ∧
      ∀ x, ‖cascadeSpinWeight n m c L x s‖ ≤ 1 :=
  cascadeMoment_bounded_continuous n m _ (affineLogPartition_boundedDerivs c L) _
    (affineGibbs_continuous c L s) (by norm_num) (fun x => affineGibbs_norm_le_one c L x s)
end CascadeProbability
end SK.Analytic

end
end

end

end OAI
