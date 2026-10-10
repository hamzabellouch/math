import Mathlib
import OAI.Probability.SKRatio.Calculus.SmallTemperature
import OAI.Probability.SKRatio.Gaussian.GaussianFunctional
import OAI.Probability.SKRatio.Entropy.AnnealedTransfer

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Planted
open Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma continuous_field (x : Spin n) (i : Fin n) :
    Continuous (fun g : Disorder n => field (coupling g) x i) := by
  unfold field
  exact continuous_finsetSum _ (fun j _ => (continuous_coupling i j).mul_const _)

lemma continuous_mean (x : Spin n) (i : Fin n) :
    Continuous (fun g : Disorder n => mean (coupling g) x i) :=
  (continuous_iff_continuousAt.mpr (fun y => (hasDerivAt_tanh y).continuousAt)).comp
    (continuous_field x i)

lemma continuous_conditionalVariance (x : Spin n) (i : Fin n) :
    Continuous (fun g : Disorder n => conditionalVariance (coupling g) x i) := by
  unfold conditionalVariance
  exact continuous_const.sub ((continuous_mean x i).pow 2)

lemma continuous_gradientWeight (x : Spin n) (i : Fin n) :
    Continuous (fun g : Disorder n => gradientWeight (coupling g) x i) := by
  unfold gradientWeight
  exact continuous_const.sub ((continuous_mean x i).const_mul _)

lemma continuous_gradientForm (p : Fin n → ℝ) :
    Continuous (fun g : Disorder n => gradientForm (coupling g) p) := by
  unfold gradientForm pairSum
  apply Continuous.add
  · apply Continuous.add
    · exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
        (((continuous_coupling i j).mul_const _).mul
          (continuous_conditionalVariance _ j)).mul_const _))
    · apply Continuous.const_mul
      exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
        (((((continuous_coupling i j).pow 2).mul_const _).mul
          (continuous_mean _ j)).mul (continuous_conditionalVariance _ j)).mul_const _))
  · apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    apply Continuous.div
    · exact ((continuous_coupling i j).pow 2).mul
        ((((continuous_conditionalVariance _ j).mul_const _).add
          ((continuous_conditionalVariance _ i).mul_const _)).pow 2)
    · exact (continuous_gradientWeight _ i).add (continuous_gradientWeight _ j)
    · intro g
      exact (add_pos (gradientWeight_pos _ _ _) (gradientWeight_pos _ _ _)).ne'

def formBad (ρ : ℝ) (n : ℕ) : Set (Disorder n) :=
  {g | ∃ p : Fin n → ℝ, (1-ρ)*(∑ i, p i^2) < gradientForm (coupling g) p}

lemma formBad_measurable (ρ : ℝ) (n : ℕ) : MeasurableSet (formBad ρ n) := by
  have he : formBad ρ n = ⋃ p : Fin n → ℝ,
      {g | (1-ρ)*(∑ i, p i^2) < gradientForm (coupling g) p} := by
    ext g
    simp [formBad]
  rw [he]
  exact (isOpen_iUnion (fun p => isOpen_lt continuous_const (continuous_gradientForm p))).measurableSet

lemma gradientForm_smul (J : Interaction n) (p : Fin n → ℝ) (a : ℝ) :
    gradientForm J (fun i => a*p i) = a^2*gradientForm J p := by
  unfold gradientForm pairSum
  simp only [mul_add,Finset.mul_sum,mul_div_assoc]
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

lemma gradientForm_zero (J : Interaction n) : gradientForm J 0 = 0 := by
  simp [gradientForm,pairSum]

lemma formBad_iff_unit (ρ : ℝ) (g : Disorder n) :
    g ∈ formBad ρ n ↔ ∃ p : Fin n → ℝ, (∑ i, p i^2) = 1 ∧
      1-ρ < gradientForm (coupling g) p := by
  constructor
  · rintro ⟨p,hp⟩
    have hnorm0 : 0 ≤ ∑ i, p i^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hnorm : 0 < ∑ i, p i^2 := by
      by_contra h
      have hz : ∑ i, p i^2 = 0 := le_antisymm (not_lt.mp h) hnorm0
      have hp0 : p = 0 := by
        funext i
        have hi : p i^2 ≤ 0 := by
          rw [←hz]
          exact Finset.single_le_sum (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i)
        have : p i = 0 := by nlinarith [sq_nonneg (p i)]
        exact this
      rw [hp0,gradientForm_zero] at hp
      simp at hp
    let a := (sqrt (∑ i, p i^2))⁻¹
    have ha : 0 < a := inv_pos.mpr (sqrt_pos.mpr hnorm)
    have ha2 : a^2*(∑ i, p i^2) = 1 := by
      dsimp [a]
      rw [inv_pow,sq_sqrt hnorm0,inv_mul_cancel₀ hnorm.ne']
    refine ⟨fun i => a*p i,?_,?_⟩
    · simp only [mul_pow,←Finset.mul_sum]
      exact ha2
    · rw [gradientForm_smul]
      have ht := mul_lt_mul_of_pos_left hp (sq_pos_of_pos ha)
      have he : a^2*((1-ρ)*(∑ i, p i^2)) = (1-ρ)*(a^2*(∑ i, p i^2)) := by ring
      rw [he,ha2,mul_one] at ht
      exact ht
  · rintro ⟨p,hp,h⟩
    exact ⟨p,by simpa only [hp,mul_one] using h⟩

lemma gradient_drift_of_form_good {ρ : ℝ} (g : Disorder n)
    (hsmall : ∀ i j, |coupling g i j| ≤ 1/10)
    (hR : 16*R3 (coupling g) ≤ ρ/2) (f : Observables n) (x : Spin n)
    (hx : gauge x g ∉ formBad ρ n) :
    (∑ i, 2*halfDiff i f x*halfDiff i (generator (coupling g) f) x) -
      generator (coupling g) (unweightedGradient f) x ≤ -ρ*unweightedGradient f x := by
  have hlocal := pointwise_gradient_local_bound (coupling g) (coupling_symm g)
    (coupling_diag g) hsmall f 0 x
  rw [(unweightedGradient_hasDerivAt (coupling g) f x 0).deriv] at hlocal
  simp only [semigroup_zero,one_apply_eq_self] at hlocal
  have hf : gradientForm (coupling (gauge x g)) (fun i => spin x i*halfDiff i f x) ≤
      (1-ρ)*(∑ i, (spin x i*halfDiff i f x)^2) := by
    by_contra h
    exact hx ⟨_,not_le.mp h⟩
  simp only [coupling_gauge,mul_pow,spin_sq,one_mul] at hf
  change gradientForm _ _ ≤ (1-ρ)*unweightedGradient f x at hf
  have hU : 0 ≤ unweightedGradient f x := unweightedGradient_nonneg f x
  have hRU := mul_le_mul_of_nonneg_right hR hU
  linarith only [hlocal,hf,hRU]

lemma gradient_drift_rough (g : Disorder n)
    (hsmall : ∀ i j, |coupling g i j| ≤ 1/10)
    (hnorm : euclideanOpNorm (coupling g) ≤ 2)
    (hR2 : R2 (coupling g) ≤ 1) (hR3 : 16*R3 (coupling g) ≤ 1)
    (f : Observables n) (x : Spin n) :
    (∑ i, 2*halfDiff i f x*halfDiff i (generator (coupling g) f) x) -
      generator (coupling g) (unweightedGradient f) x ≤ 8*unweightedGradient f x := by
  have hr := gradient_global_bound (coupling g) (coupling_symm g) (coupling_diag g) hsmall f 0 x
  rw [(unweightedGradient_hasDerivAt (coupling g) f x 0).deriv] at hr
  simp only [semigroup_zero,one_apply_eq_self] at hr
  have hc : 2*(-1+euclideanOpNorm (coupling g)+(4/(3*sqrt 3)+32/27)*R2 (coupling g)+
      16*R3 (coupling g)) ≤ 8 := by
    have hh := mul_le_mul_of_nonneg_right rough_coefficient_lt_two.le
      (rowControl_nonneg (coupling g) 2)
    linarith
  exact hr.trans (mul_le_mul_of_nonneg_right hc (unweightedGradient_nonneg f x))

theorem ratio_cutoff_of_planted_form (β ε η : ℝ)
    (hβ : 0 ≤ β) (hβhalf : β < 1/2)
    (hε : 0 < ε) (hεhalf : ε < 1/2) (hη : 0 < η)
    {ρ κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ)
    (hplant : ∀ᶠ n : ℕ in atTop,
      law β n (formBad ρ n) ≤ ENNReal.ofReal (exp (-κ*n))) :
    Tendsto (fun n : ℕ => disorderLaw β n
        {g : Disorder n | 1+η <
          (mixingTime g ε : ℝ)/(mixingTime g (1-ε) : ℝ)}) atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1-ε)) := by
  have hb2 : β^2 ≤ 1/4 := by nlinarith
  obtain ⟨H,hHm,hHp,hHs⟩ := annealed_transfer_events
    (show β^2 ≤ 1/2 by linarith) hκ (formBad ρ) (formBad_measurable ρ) hplant
  let δ := min (1/100:ℝ) (ρ/32)
  have hd : 0 < δ := lt_min (by norm_num) (by positivity)
  have hd1 : δ ≤ 1/100 := min_le_left _ _
  have hdρ : δ ≤ ρ/32 := min_le_right _ _
  let c := min ρ (κ/2)
  have hc : 0 < c := lt_min hρ (by positivity)
  have hcρ : c ≤ ρ := min_le_left _ _
  have hcκ : c ≤ κ/2 := min_le_right _ _
  let G : ∀ n : ℕ, Set (Disorder n) := fun n => H n ∩ Gaussian.matrixGood β δ n
  let bad : ∀ n : ℕ, Disorder n → Set (Spin n) := fun n g => {x | gauge x g ∈ formBad ρ n}
  have hGp : Tendsto (fun n => disorderLaw β n (G n)ᶜ) atTop (𝓝 0) := by
    have hb (n : ℕ) : disorderLaw β n (G n)ᶜ ≤ disorderLaw β n (H n)ᶜ +
        disorderLaw β n (Gaussian.matrixGood β δ n)ᶜ := by
      simp only [G,Set.compl_inter]
      exact measure_union_le _ _
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [add_zero] using hHp.add (Gaussian.matrixGood_probability hβ hd))
      (fun _ => bot_le) hb
  apply Gaussian.ratio_cutoff_of_typical_gradient β ε η hβ hβhalf hε hεhalf hη G bad hc
    (by linarith : 0 ≤ 8+c) hGp
  · intro n g hg
    change badMass (formBad ρ n) g ≤ exp (-c*n)
    exact (hHs n g hg.1).trans (exp_le_exp.mpr (by nlinarith [show (0:ℝ) ≤ n from Nat.cast_nonneg n]))
  · intro n g hg f x
    have hnorm : euclideanOpNorm (coupling g) ≤ 2 := hg.2.1.trans (by linarith)
    have hrow (i : Fin n) : ∑ j, coupling g i j^2 ≤ 1 := (hg.2.2.2 i).trans (by linarith)
    have hR2 : R2 (coupling g) ≤ 1 := rowControl_le _ 2 zero_le_one
      (by intro i; simpa only [sq_abs] using hrow i)
    have hR3 : R3 (coupling g) ≤ δ := by
      simpa only [mul_one] using R3_le_entry_times_row (coupling g) hd.le zero_le_one hg.2.2.1 hrow
    have hsmall : ∀ i j, |coupling g i j| ≤ 1/10 := fun i j => (hg.2.2.1 i j).trans (by linarith)
    by_cases hx : x ∈ bad n g
    · rw [ite_eq_left hx]
      have hr := gradient_drift_rough g hsmall hnorm hR2 (by linarith) f x
      convert hr using 1
      ring
    · rw [ite_eq_right hx,add_zero]
      exact (gradient_drift_of_form_good g hsmall (by linarith) f x hx).trans
        (mul_le_mul_of_nonneg_right (neg_le_neg hcρ) (unweightedGradient_nonneg f x))

end SKRatio.Planted

end
end

end OAI
