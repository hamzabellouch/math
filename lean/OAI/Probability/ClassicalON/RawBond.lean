import OAI.Probability.ClassicalON.BondMoments

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def amplitudeBondPrefactor (left right : E → V) (b : E → ℝ) (r : V → Amplitude) : ℝ :=
  (2:ℝ)⁻¹^Fintype.card V*Real.exp (-∑ e,amplitudeCoupling left right b (fun v => (r v:ℝ)) e)*
    planarAmplitudePartition left right b r

def amplitudeBondWeight (left right : E → V) (b : E → ℝ) (r : V → Amplitude) (η : E → Bool) : ℝ :=
  amplitudeBondPrefactor left right b r*bondWeight left right (amplitudeBondParam left right b r) η

theorem amplitudeBondPrefactor_pos (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    0<amplitudeBondPrefactor left right b r := by
  unfold amplitudeBondPrefactor
  exact mul_pos (mul_pos (by positivity) (Real.exp_pos _)) (planarAmplitudePartition_pos _ _ _ _)

theorem continuous_amplitudeBondPrefactor (left right : E → V) (b : E → ℝ) :
    Continuous (amplitudeBondPrefactor left right b) := by
  unfold amplitudeBondPrefactor
  apply Continuous.mul _ (continuous_planarAmplitudePartition _ _ _)
  unfold amplitudeCoupling
  fun_prop

theorem continuous_amplitudeBondWeight (left right : E → V) (b : E → ℝ) (η : E → Bool) :
    Continuous (fun r => amplitudeBondWeight left right b r η) := by
  apply (continuous_amplitudeBondPrefactor _ _ _).mul
  unfold bondWeight bondProduct
  apply Continuous.mul continuous_const
  apply continuous_finsetProd
  intro e _
  split
  · exact continuous_amplitudeBondParam left right b e
  · exact continuous_const

theorem amplitudeBondWeight_nonneg (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (r : V → Amplitude) (η : E → Bool) : 0≤amplitudeBondWeight left right b r η :=
  mul_nonneg (amplitudeBondPrefactor_pos _ _ _ _).le
    (bondWeight_nonneg _ _ (amplitudeBondParam_nonneg _ _ _ hb r) η)

theorem amplitudeBondWeight_sum (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    (∑ η,amplitudeBondWeight left right b r η)=amplitudeDensity left right b r := by
  unfold amplitudeBondWeight amplitudeDensity
  rw [isingAmplitudePartition_bond_sum]
  rw [← Finset.mul_sum]
  unfold amplitudeBondPrefactor
  ring

theorem amplitudeDensity_bondConditionalMean (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0≤b e) (f : (V → Amplitude) → (E → Bool) → ℝ) (r : V → Amplitude) :
    amplitudeDensity left right b r*bondConditionalMean left right b f r=
      ∑ η,amplitudeBondWeight left right b r η*f r η := by
  rw [← amplitudeBondWeight_sum left right b r]
  unfold amplitudeBondWeight bondConditionalMean finiteMean
  rw [← Finset.mul_sum]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  have hs := (bondWeight_sum_pos left right (amplitudeBondParam_nonneg left right b hb r)).ne'
  field_simp

theorem jointBondMean_raw (μ : Measure Amplitude) (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0≤b e) (f : (V → Amplitude) → (E → Bool) → ℝ) :
    jointBondMean μ left right b f=
      (∫ r,∑ η,amplitudeBondWeight left right b r η*f r η ∂Measure.pi (fun _ : V => μ))/
        (∫ r,∑ η,amplitudeBondWeight left right b r η ∂Measure.pi (fun _ : V => μ)) := by
  unfold jointBondMean weightedMean
  simp_rw [amplitudeDensity_bondConditionalMean _ _ _ hb,amplitudeBondWeight_sum]

end ClassicalON

end

end OAI
