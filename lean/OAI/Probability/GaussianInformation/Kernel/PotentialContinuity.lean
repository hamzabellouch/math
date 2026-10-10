import Mathlib
import OAI.Probability.GaussianInformation.Kernel.NoisySums

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.Continuity
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
open Coercivity Sphere EntropySupport
noncomputable def densityLaw {d : ℕ} (f : Ambient d → ℝ) : Measure (Ambient d) :=
  (sphereProbability d).withDensity (fun x => ENNReal.ofReal (f x))

lemma tendsto_J {d : ℕ} (hd : 16 ≤ d) (f : ℕ → Ambient d → ℝ) (g : Ambient d → ℝ)
    (hf : ∀ n,Measurable (f n)) (hg : Measurable g) (_hf0 : ∀ n x,0 ≤ f n x) {H : ℝ} (_hH : 0 ≤ H)
    (hfH : ∀ n x,f n x ≤ H)
    (hlim : ∀ᵐ x ∂sphereProbability d,Filter.Tendsto (fun n => f n x) Filter.atTop (𝓝 (g x)))
    (s : Ambient d) :
    Filter.Tendsto (fun n => J (densityLaw (f n)) s) Filter.atTop (𝓝 (J (densityLaw g) s)) := by
  let K := fun u : Ambient d => (ENNReal.ofReal ‖u-s‖)⁻¹^(2*(d/16))
  have hK : Measurable K := ((measurable_id.sub_const s).norm.ennreal_ofReal.inv).pow_const _
  have hKI : (∫⁻ u,K u ∂sphereProbability d) ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact inverse_kernel_bound (sphereProbability d) (by positivity : 0 ≤ (9*3^d:ℝ))
      (by omega) (by omega) (fun z r hr => cap_bound (by omega) z hr) s
  have hl (h : Ambient d → ℝ) (hh : Measurable h) : J (densityLaw h) s =
      ∫⁻ u,ENNReal.ofReal (h u)*K u ∂sphereProbability d := by
    unfold J densityLaw
    exact lintegral_withDensity_eq_lintegral_mul _ hh.ennreal_ofReal hK
  rw [hl g hg]
  simp_rw [hl _ (hf _)]
  apply tendsto_lintegral_of_dominated_convergence (fun u => ENNReal.ofReal H*K u)
    (fun n => (hf n).ennreal_ofReal.mul hK)
    (fun n => ae_of_all _ (fun u => mul_le_mul_left (ENNReal.ofReal_le_ofReal (hfH n u)) _))
  · rw [lintegral_const_mul _ hK]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKI
  · filter_upwards [hlim,ae_lt_top hK hKI] with u hu hKu
    exact ENNReal.Tendsto.mul_const (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hu) (Or.inr hKu.ne)

lemma tendsto_Phi {d : ℕ} (hd : 16 ≤ d) (f : ℕ → Ambient d → ℝ) (g : Ambient d → ℝ)
    (hf : ∀ n,Measurable (f n)) (hg : Measurable g)
    (hf0 : ∀ n x,0 ≤ f n x) (hg0 : ∀ x,0 ≤ g x)
    {H : ℝ} (hH : 0 < H) (hfH : ∀ n x,f n x ≤ H) (hgH : ∀ x,g x ≤ H)
    (hfp : ∀ n,IsProbabilityMeasure (densityLaw (f n)))
    (hgp : IsProbabilityMeasure (densityLaw g))
    (hlim : ∀ᵐ x ∂sphereProbability d,Filter.Tendsto (fun n => f n x) Filter.atTop (𝓝 (g x))) :
    Filter.Tendsto (fun n => Phi (densityLaw (f n))) Filter.atTop (𝓝 (Phi (densityLaw g))) := by
  have (n : ℕ) : IsProbabilityMeasure (densityLaw (f n)) := hfp n
  have : IsProbabilityMeasure (densityLaw g) := hgp
  have hfB (n : ℕ) : BoundedDensity (densityLaw (f n)) := ⟨H,hH,density_bounded _ _ (hfH n)⟩
  have hgB : BoundedDensity (densityLaw g) := ⟨H,hH,density_bounded _ _ hgH⟩
  have hformula (n : ℕ) := Phi_density_formula hd (f n) (hf n) (hf0 n) (hfH n) _ (hfB n) rfl
  have hgformula := Phi_density_formula hd g hg hg0 hgH _ hgB rfl
  rw [hgformula]
  simp_rw [hformula]
  let a : ℝ := (1/2:ℝ)^(2*(d/16))
  let b : ℝ := H*(1+(9*3^d:ℝ)*2^((d-1)+2*(d/16)+1))
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨C,hC⟩ := ((isCompact_Icc (a := (0:ℝ)) (b := H)).image continuous_xlog).isBounded.exists_norm_le
  have hbound (n : ℕ) : ∀ᵐ s ∂sphereProbability d,
      ‖xlog (f n s)-f n s*Real.log (J (densityLaw (f n)) s).toReal‖ ≤
        C+H*(|Real.log a|+|Real.log b|) := by
    filter_upwards [ae_unit_norm (by omega : 0 < d)] with s hs
    have hj := J_real_bounds hd (densityLaw (f n)) hH (density_bounded _ _ (hfH n)) s hs
    change a ≤ _ ∧ _ ≤ b at hj
    have hll := Real.log_le_log ha hj.1
    have hlu := Real.log_le_log (ha.trans_le hj.1) hj.2
    have hab : |Real.log (J (densityLaw (f n)) s).toReal| ≤ |Real.log a|+|Real.log b| := by
      apply abs_le.mpr
      constructor
      · have h := neg_abs_le (Real.log a); have hh := abs_nonneg (Real.log b); linarith
      · have h := le_abs_self (Real.log b); have hh := abs_nonneg (Real.log a); linarith
    have hfx : ‖xlog (f n s)‖ ≤ C := hC _ (mem_image_of_mem _ ⟨hf0 n s,hfH n s⟩)
    calc
      _ ≤ ‖xlog (f n s)‖+‖f n s*Real.log (J (densityLaw (f n)) s).toReal‖ := norm_sub_le _ _
      _ ≤ C+H*(|Real.log a|+|Real.log b|) := by
        rw [norm_mul,Real.norm_eq_abs (f n s),abs_of_nonneg (hf0 n s),Real.norm_eq_abs]
        exact add_le_add hfx (mul_le_mul (hfH n s) hab (abs_nonneg _) hH.le)
  apply tendsto_integral_of_dominated_convergence (fun _ => C+H*(|Real.log a|+|Real.log b|))
    (fun n => ((continuous_xlog.measurable.comp (hf n)).sub ((hf n).mul (measurable_J _).ennreal_toReal.log)).aestronglyMeasurable)
    (integrable_const _) hbound
  filter_upwards [hlim,ae_unit_norm (by omega : 0 < d)] with s hs hsn
  have hJt := tendsto_J hd f g hf hg hf0 hH.le hfH hlim s
  have hJfin : J (densityLaw g) s ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (bounded_J hd (densityLaw g) hH (density_bounded _ _ hgH) s)
  have hJp : 0 < (J (densityLaw g) s).toReal := ha.trans_le (J_real_bounds hd (densityLaw g) hH (density_bounded _ _ hgH) s hsn).1
  have hjr := (ENNReal.continuousAt_toReal hJfin).tendsto.comp hJt
  exact (continuous_xlog.continuousAt.tendsto.comp hs).sub (hs.mul ((Real.continuousAt_log hJp.ne').tendsto.comp hjr))

end KernelPotential.Continuity

end OAI
