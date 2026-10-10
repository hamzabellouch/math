import OAI.Probability.ClassicalON.SpinBondKernel

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def amplitudeBondParam (left right : E → V) (b : E → ℝ) (r : V → Amplitude) (e : E) : ℝ :=
  Real.exp (2*b e*(r (left e):ℝ)*(r (right e):ℝ))-1

omit [Fintype V] [Fintype E] in
theorem amplitudeBondParam_nonneg (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0 ≤ b e) (r : V → Amplitude) (e : E) :
    0 ≤ amplitudeBondParam left right b r e := by
  apply sub_nonneg.mpr
  apply Real.one_le_exp
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hb e)) (r (left e)).property.1) (r (right e)).property.1

omit [Fintype V] [Fintype E] in
theorem amplitudeBondParam_monotone (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0 ≤ b e) : Monotone (amplitudeBondParam left right b) := by
  intro r s hrs e
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (hrs (left e)) (mul_nonneg (by norm_num) (hb e))
  · exact hrs (right e)
  · exact (r (right e)).property.1
  · exact mul_nonneg (mul_nonneg (by norm_num) (hb e)) (s (left e)).property.1

omit [Fintype V] [Fintype E] in
theorem continuous_amplitudeBondParam (left right : E → V) (b : E → ℝ) (e : E) :
    Continuous (fun r => amplitudeBondParam left right b r e) := by
  unfold amplitudeBondParam; fun_prop

def bondConditionalMean (left right : E → V) (b : E → ℝ)
    (f : (V → Amplitude) → (E → Bool) → ℝ) (r : V → Amplitude) : ℝ :=
  finiteMean (bondWeight left right (amplitudeBondParam left right b r)) (f r)

omit [Fintype V] in
theorem continuous_bondConditionalMean (left right : E → V) (b : E → ℝ) (hb : ∀ e,0 ≤ b e)
    {f : (V → Amplitude) → (E → Bool) → ℝ} (hf : ∀ η,Continuous (fun r => f r η)) :
    Continuous (bondConditionalMean left right b f) := by
  have hw (η : E → Bool) : Continuous (fun r => bondWeight left right (amplitudeBondParam left right b r) η) := by
    unfold bondWeight bondProduct
    apply Continuous.mul continuous_const
    apply continuous_finsetProd
    intro e _
    split
    · exact continuous_amplitudeBondParam left right b e
    · exact continuous_const
  exact (continuous_finsetSum _ (fun η _ => (hw η).mul (hf η))).div
    (continuous_finsetSum _ (fun η _ => hw η))
    (fun r => (bondWeight_sum_pos left right (amplitudeBondParam_nonneg left right b hb r)).ne')

omit [Fintype V] in
theorem bondConditionalMean_nonneg (left right : E → V) (b : E → ℝ) (hb : ∀ e,0 ≤ b e)
    {f : (V → Amplitude) → (E → Bool) → ℝ} (hf : ∀ r η,0 ≤ f r η) (r : V → Amplitude) :
    0 ≤ bondConditionalMean left right b f r :=
  finiteMean_nonneg (bondWeight_nonneg left right (amplitudeBondParam_nonneg left right b hb r)) (hf r)

theorem bondConditionalMean_monotone (left right : E → V) (b : E → ℝ) (hb : ∀ e,0 ≤ b e)
    {f : (V → Amplitude) → (E → Bool) → ℝ} (hf : ∀ r η,0 ≤ f r η)
    (hmr : ∀ η,Monotone (fun r => f r η)) (hmη : ∀ r,Monotone (f r)) :
    Monotone (bondConditionalMean left right b f) := by
  intro r s hrs
  apply le_trans (bondMean_mono left right (amplitudeBondParam_nonneg left right b hb r)
    (amplitudeBondParam_monotone left right b hb hrs) (hf r) (hmη r))
  exact finiteMean_mono (bondWeight_nonneg left right (amplitudeBondParam_nonneg left right b hb s))
    (fun η => hmr η hrs)

def jointBondMean (μ : Measure Amplitude) (left right : E → V) (b : E → ℝ)
    (f : (V → Amplitude) → (E → Bool) → ℝ) : ℝ :=
  weightedMean (Measure.pi (fun _ : V => μ)) (amplitudeDensity left right b)
    (bondConditionalMean left right b f)

theorem jointBond_associated (μ : Measure Amplitude) [IsProbabilityMeasure μ]
    (left right : E → V) (b : E → ℝ) (hb : ∀ e,0 ≤ b e)
    {f g : (V → Amplitude) → (E → Bool) → ℝ}
    (hf : ∀ η,Continuous (fun r => f r η)) (hg : ∀ η,Continuous (fun r => g r η))
    (hfn : ∀ r η,0 ≤ f r η) (hgn : ∀ r η,0 ≤ g r η)
    (hfr : ∀ η,Monotone (fun r => f r η)) (hgr : ∀ η,Monotone (fun r => g r η))
    (hfη : ∀ r,Monotone (f r)) (hgη : ∀ r,Monotone (g r)) :
    jointBondMean μ left right b f*jointBondMean μ left right b g ≤
      jointBondMean μ left right b (fun r η => f r η*g r η) := by
  have hcf := continuous_bondConditionalMean left right b hb hf
  have hcg := continuous_bondConditionalMean left right b hb hg
  apply le_trans (amplitude_associated_any μ left right b hb
    _ _ hcf hcg (bondConditionalMean_nonneg left right b hb hfn)
    (bondConditionalMean_nonneg left right b hb hgn)
    (bondConditionalMean_monotone left right b hb hfn hfr hfη)
    (bondConditionalMean_monotone left right b hb hgn hgr hgη))
  apply weightedMean_mono (continuous_amplitudeDensity _ _ _) (amplitudeDensity_pos _ _ _)
    (hcf.mul hcg) (continuous_bondConditionalMean left right b hb (fun η => (hf η).mul (hg η)))
  intro r
  exact bondMean_associated left right (amplitudeBondParam_nonneg left right b hb r)
    (hfn r) (hgn r) (hfη r) (hgη r)

end ClassicalON

end

end OAI
