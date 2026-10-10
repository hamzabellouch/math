import OAI.Analysis.LipschitzHilbert.Fourier.L1FrequencyMultiplier

namespace OAI

/-! Exact finite input and test reconstruction for frequency multipliers
with an integrable envelope. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem planarFourier_finset_sum_l1 {ι : Type*} (I : Finset ι)
    (f : ι → (ℝ×ℝ) → ℂ) (hf : ∀ i∈I, Integrable (f i) planeMeasure) (omega : ℝ×ℝ) :
    planarFourier (fun z => ∑ i∈I, f i z) omega=∑ i∈I, planarFourier (f i) omega := by
  have hi (i : ι) (hi : i∈I) : Integrable (fun z : ℝ×ℝ =>
      Real.fourierChar (-(z.1*omega.1+z.2*omega.2)) • f i z) planeMeasure := by
    apply (hf i hi).norm.mono'
      ((show Continuous (fun z : ℝ×ℝ => Real.fourierChar (-(z.1*omega.1+z.2*omega.2))) by
        fun_prop).aestronglyMeasurable.smul (hf i hi).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun z => le_of_eq (Circle.norm_smul _ _))
  unfold planarFourier
  simp_rw [Finset.smul_sum]
  exact integral_finsetSum I hi

theorem variableFrequencyMultiplier_finset_sum_l1 {ι : Type*} (I : Finset ι)
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : Measurable m)
    (q : ℝ×ℝ → ℝ) (hq : Integrable q planeMeasure)
    (hbound : ∀ z omega, ‖m (z,omega)‖≤q omega)
    (f : ι → (ℝ×ℝ) → ℂ) (hf : ∀ i∈I, Integrable (f i) planeMeasure) (z : ℝ×ℝ) :
    variableFrequencyMultiplierL1 m (fun x => ∑ i∈I, f i x) z=
      ∑ i∈I, variableFrequencyMultiplierL1 m (f i) z := by
  unfold variableFrequencyMultiplierL1
  simp_rw [planarFourier_finset_sum_l1 I f hf,Finset.mul_sum,Finset.smul_sum]
  exact integral_finsetSum I (fun i hi =>
    variableFrequencyMultiplier_integrand_integrable_l1 m hm q hq hbound (f i) (hf i hi) z)

theorem variableFrequencyMultiplier_pairing_finset_sum_l1 {ι ν : Type*}
    (I : Finset ι) (J : Finset ν)
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : Measurable m)
    (q : ℝ×ℝ → ℝ) (hq : Integrable q planeMeasure)
    (hbound : ∀ z omega, ‖m (z,omega)‖≤q omega)
    (f : ι → (ℝ×ℝ) → ℂ) (hf : ∀ i∈I, Integrable (f i) planeMeasure)
    (g : ν → (ℝ×ℝ) → ℂ) (hg : ∀ j∈J, Integrable (g j) planeMeasure) :
    (∫ z, variableFrequencyMultiplierL1 m (fun x => ∑ i∈I, f i x) z*
      star (∑ j∈J, g j z) ∂planeMeasure)=
      ∑ i∈I, ∑ j∈J, ∫ z, variableFrequencyMultiplierL1 m (f i) z*star (g j z) ∂planeMeasure := by
  simp_rw [variableFrequencyMultiplier_finset_sum_l1 I m hm q hq hbound f hf,star_sum,
    Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum I]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_finsetSum J (fun j hj =>
      variableFrequencyMultiplier_pairing_integrable_l1 m hm q hq hbound (f i) (hf i hi) (g j) (hg j hj))
  · intro i hi
    exact integrable_finsetSum J (fun j hj =>
      variableFrequencyMultiplier_pairing_integrable_l1 m hm q hq hbound (f i) (hf i hi) (g j) (hg j hj))

theorem planarFourier_real_smul_l1 (a : ℝ) (f : ℝ×ℝ → ℂ) (omega : ℝ×ℝ) :
    planarFourier (fun z => a • f z) omega=a • planarFourier f omega := by
  unfold planarFourier
  simp_rw [smul_comm (Real.fourierChar _) a]
  exact integral_smul a _

theorem variableFrequencyMultiplier_real_smul_l1 (a : ℝ)
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (f : ℝ×ℝ → ℂ) (z : ℝ×ℝ) :
    variableFrequencyMultiplierL1 m (fun x => a • f x) z=
      a • variableFrequencyMultiplierL1 m f z := by
  unfold variableFrequencyMultiplierL1
  simp_rw [planarFourier_real_smul_l1,mul_smul_comm,smul_comm (Real.fourierChar _) a]
  exact integral_smul a _

theorem variableFrequencyMultiplier_pairing_real_smul_l1 (a b : ℝ)
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (f g : ℝ×ℝ → ℂ) :
    (∫ z, variableFrequencyMultiplierL1 m (fun x => a • f x) z*
      star (b • g z) ∂planeMeasure)=
      (a*b) • ∫ z, variableFrequencyMultiplierL1 m f z*star (g z) ∂planeMeasure := by
  simp_rw [variableFrequencyMultiplier_real_smul_l1,star_smul,star_trivial,
    smul_mul_smul_comm]
  exact integral_smul (a*b) _

end LipschitzHilbert.PacketRepresentation

end

end OAI
