import OAI.Analysis.CircleDomains.Probability.MeasureFamilyNullRemoval
import OAI.Analysis.CircleDomains.Probability.MeasureFamilyExceptional
import OAI.Analysis.CircleDomains.Sobolev.L2DominatedAeSubsequence

namespace OAI

/-! Pointwise admissibility passes through an almost-everywhere dominated
limit after removing, and then repairing, a zero-modulus family. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma measureFamilyModulus_zero_of_cover_two
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) (K : A → FiniteMeasure Z)
    (S T : Set A) (hcover : ∀ a, a ∈ S ∨ a ∈ T)
    (hS : measureFamilyModulus S Z σ (fun a => K a.val) = 0)
    (hT : measureFamilyModulus T Z σ (fun a => K a.val) = 0) :
    measureFamilyModulus A Z σ K = 0 := by
  apply measureFamilyModulus_zero_of_countable_cover σ K
    (fun b : Bool => if b then T else S)
  · intro a
    rcases hcover a with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  · intro b
    cases b
    · exact hS
    · exact hT

lemma measureFamilyModulus_le_of_dominated_limit
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) (K : A → FiniteMeasure Z)
    (f : ℕ → Z → ℝ) (g P : Z → ℝ)
    (hf : ∀ n, Measurable (f n)) (hf0 : ∀ n z, 0 ≤ f n z)
    (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (hP : Measurable P) (hP0 : ∀ z, 0 ≤ P z) (hPL : MemLp P 2 σ)
    (hlim : ∀ᵐ z ∂σ, (∀ n, |f n z| ≤ P z) ∧
      Tendsto (fun n => f n z) atTop (𝓝 (g z)))
    (ha : ∀ a, ∀ᶠ n in atTop, 1 ≤ ∫⁻ z, ENNReal.ofReal (f n z) ∂(K a : Measure Z)) :
    measureFamilyModulus A Z σ K ≤ ∫⁻ z, ENNReal.ofReal (g z)^2 ∂σ := by
  classical
  obtain ⟨N,hbad,hNm,hN0⟩ := exists_measurable_superset_of_null
    (show σ {z | ¬ ((∀ n, |f n z| ≤ P z) ∧
      Tendsto (fun n => f n z) atTop (𝓝 (g z)))} = 0 from hlim)
  let S : Set A := {a | (K a : Measure Z) N ≠ 0 ∨
    (∫⁻ z, ENNReal.ofReal (P z) ∂(K a : Measure Z)) = ∞}
  have hS : measureFamilyModulus S Z σ (fun a => K a.val) = 0 := by
    apply measureFamilyModulus_zero_of_cover_two σ (fun a : S => K a.val)
      {a | (K a.val : Measure Z) N ≠ 0}
      {a | (∫⁻ z, ENNReal.ofReal (P z) ∂(K a.val : Measure Z)) = ∞}
    · intro a
      exact a.property
    · exact measureFamilyModulus_zero_of_charges_null_set σ _ hNm hN0
        (fun a => a.property)
    · apply measureFamilyModulus_zero_of_infinite_integral σ _ hP.ennreal_ofReal
      · have he : (∫⁻ z, ENNReal.ofReal (P z)^2 ∂σ) =
            ENNReal.ofReal (∫ z, P z^2 ∂σ) := by
          rw [ofReal_integral_eq_lintegral_ofReal hPL.integrable_sq
            (Eventually.of_forall (fun z => sq_nonneg (P z)))]
          apply lintegral_congr
          intro z
          exact (ENNReal.ofReal_pow (hP0 z) 2).symm
        rw [he]
        exact ENNReal.ofReal_ne_top
      · exact fun a => a.property
  apply measureFamilyModulus_le_admissible_off_null_family σ K S hS hg.ennreal_ofReal
  intro a has
  have hgood : (K a : Measure Z) N = 0 ∧
      (∫⁻ z, ENNReal.ofReal (P z) ∂(K a : Measure Z)) ≠ ∞ := by
    simpa only [S,mem_ofPred_eq,not_or,not_not] using has
  have hνgood : ∀ᵐ z ∂(K a : Measure Z), (∀ n, |f n z| ≤ P z) ∧
      Tendsto (fun n => f n z) atTop (𝓝 (g z)) := by
    have hN : ∀ᵐ z ∂(K a : Measure Z), z ∉ N :=
      (by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hgood.1)
    filter_upwards [hN] with z hz
    exact of_not_not (fun hn => hz (hbad hn))
  have hPi : Integrable P (K a : Measure Z) :=
    (lintegral_ofReal_ne_top_iff_integrable hP.aestronglyMeasurable
      (Eventually.of_forall hP0)).mp hgood.2
  have hfi (n : ℕ) : Integrable (f n) (K a : Measure Z) := by
    apply hPi.mono' (hf n).aestronglyMeasurable
    filter_upwards [hνgood] with z hz
    simpa only [Real.norm_eq_abs] using hz.1 n
  have hconv : Tendsto (fun n => ∫ z, f n z ∂(K a : Measure Z)) atTop
      (𝓝 (∫ z, g z ∂(K a : Measure Z))) := by
    apply tendsto_integral_of_dominated_convergence P (fun n => (hf n).aestronglyMeasurable)
      hPi
    · intro n
      filter_upwards [hνgood] with z hz
      simpa only [Real.norm_eq_abs] using hz.1 n
    · exact hνgood.mono (fun z hz => hz.2)
  have hgi : Integrable g (K a : Measure Z) := by
    apply hPi.mono' hg.aestronglyMeasurable
    filter_upwards [hνgood] with z hz
    rw [Real.norm_eq_abs]
    exact le_of_tendsto (continuous_abs.continuousAt.tendsto.comp hz.2)
      (Eventually.of_forall (fun n => hz.1 n))
  have hlower : (1 : ℝ) ≤ ∫ z, g z ∂(K a : Measure Z) := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hconv
    filter_upwards [ha a] with n hn
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi n)
      (Eventually.of_forall (hf0 n))] at hn
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hn
    simpa only [ENNReal.toReal_one,ENNReal.toReal_ofReal (integral_nonneg (hf0 n))] using h
  rw [← ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall hg0)]
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hlower


lemma measureFamilyModulus_le_of_L2_limit
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) (K : A → FiniteMeasure Z)
    (f : ℕ → Z → ℝ) (g : Z → ℝ)
    (hf : ∀ n, Measurable (f n)) (hf0 : ∀ n z, 0 ≤ f n z)
    (hfL : ∀ n, MemLp (f n) 2 σ)
    (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z) (hgL : MemLp g 2 σ)
    (hlim : Tendsto (fun n => eLpNorm (fun z => f n z-g z) 2 σ) atTop (𝓝 0))
    (ha : ∀ a, ∀ᶠ n in atTop, 1 ≤ ∫⁻ z, ENNReal.ofReal (f n z) ∂(K a : Measure Z)) :
    measureFamilyModulus A Z σ K ≤ ∫⁻ z, ENNReal.ofReal (g z)^2 ∂σ := by
  obtain ⟨ρ,P,hρ,hP,hP0,hPL,hpoint⟩ := exists_L2_dominated_ae_subsequence hfL hgL hlim
  exact measureFamilyModulus_le_of_dominated_limit σ K (fun n => f (ρ n)) g P
    (fun n => hf (ρ n)) (fun n => hf0 (ρ n)) hg hg0 hP hP0 hPL hpoint
    (fun a => hρ.eventually (ha a))

end CircleDomainRigidity

end

end OAI
