import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldGradient
import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldHeightHessian

namespace OAI

/-! Differentiability of the physical conditional square levels at fixed
magnetization, including the change in the optimizing bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter Classical
open scoped Topology BigOperators

namespace InvariantIsing

def magneticHeightLevel (h : FieldStep) (s : ℝ)
    (r : Fin (h.depth + 1) → ℝ) (i : Fin (h.depth + 1)) : ℝ :=
  if hr : r ∈ fieldStrictHeightCone h.depth then
    magneticFieldLevel (fieldStepOfStrictHeights h r hr) s i else 0

def magneticHeightSchur (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (s : ℝ) (r : Fin (h.depth + 1) → ℝ) (i j : Fin (h.depth + 1)) : ℝ :=
  F.PP i j (r, magneticHeightBias h s r) -
    F.PX i (r, magneticHeightBias h s r) * F.PX j (r, magneticHeightBias h s r) /
      F.XX (r, magneticHeightBias h s r)

lemma magneticHeightSchur_symmetric (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (s : ℝ) (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (i j : Fin (h.depth + 1)) :
    magneticHeightSchur h F s r i j = magneticHeightSchur h F s r j i := by
  unfold magneticHeightSchur
  rw [F.symmetric i j (r, magneticHeightBias h s r) hr, mul_comm (F.PX i _)]

lemma hasDerivAt_magneticHeightP_line (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r d : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hrs : r ∈ fieldStrictHeightCone h.depth) (i : Fin (h.depth + 1)) :
    HasDerivAt (fun t : ℝ => F.P i (r + t • d, magneticHeightBias h s (r + t • d)))
      (∑ j, magneticHeightSchur h F s r i j * d j) 0 := by
  have hb := hasDerivAt_magneticHeightBias_line h F hI hU hs r d hr hrs
  have hp := ((hasDerivAt_const (0 : ℝ) r).add
    ((hasDerivAt_id (0 : ℝ)).smul_const d)).prodMk hb
  have hF := F.derivativeP i (r + (0 : ℝ) • d, magneticHeightBias h s (r + (0 : ℝ) • d))
    (by simpa only [zero_smul, add_zero] using hr)
  have hd := hF.comp_hasDerivAt 0 hp
  convert hd using 1
  · rfl
  · simp only [fieldFiniteLinear_apply, zero_add, one_smul,
      zero_smul, add_zero, magneticHeightSchur, sub_mul, Finset.sum_sub_distrib]
    rw [show (∑ j, F.PX i (r, magneticHeightBias h s r) *
        F.PX j (r, magneticHeightBias h s r) / F.XX (r, magneticHeightBias h s r) * d j) =
        F.PX i (r, magneticHeightBias h s r) *
          (∑ j, F.PX j (r, magneticHeightBias h s r) * d j) /
          F.XX (r, magneticHeightBias h s r) by
      simp only [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring]
    ring

lemma hasDerivAt_magneticHeightLevel_line (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r d : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hrs : r ∈ fieldStrictHeightCone h.depth) (i : Fin (h.depth + 1)) :
    HasDerivAt (fun t : ℝ => magneticHeightLevel h s (r + t • d) i)
      ((-2 / (h.cut i.succ - h.cut i.castSucc)) *
        (∑ j, magneticHeightSchur h F s r i j * d j)) 0 := by
  let w := h.cut i.succ - h.cut i.castSucc
  have hw : w ≠ 0 := (sub_pos.mpr (h.ordered_cut i.castSucc_lt_succ)).ne'
  have hd := ((hasDerivAt_magneticHeightP_line h F hI hU hs r d hr hrs i).sub_const
    (if i = Fin.last h.depth then (1 / 2 : ℝ) else 0)).const_mul (-2 / w)
  have hn : ∀ᶠ t : ℝ in 𝓝 0, r + t • d ∈ I ∩ fieldStrictHeightCone h.depth := by
    have hp : ContinuousAt (fun t : ℝ => r + t • d) 0 := by fun_prop
    exact hp.eventually ((hI.inter (isOpen_fieldStrictHeightCone _)).mem_nhds
      (by simpa only [zero_smul, add_zero, Set.mem_inter_iff] using And.intro hr hrs))
  apply hd.congr_of_eventuallyEq
  filter_upwards [hn] with t ht
  rw [magneticHeightLevel, dite_eq_left ht.2]
  have he := magneticHeight_optimized_gradient h F hU hs (r + t • d) ht.1 ht.2 i
  rw [he]
  dsimp only [w] at hw ⊢
  field_simp [hw]

end InvariantIsing

end

end OAI
