import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.Distributions.Bernoulli
import OAI.NumberTheory.Jacobsthal.Probability.HarmonicPrefixKernel

namespace OAI

namespace Erdos970

section

namespace ErdosPrimeInputs.HarmonicPrefixTilt

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
open WeightedKernelMass HarmonicPrefixKernel

noncomputable def squareBoundE (ell B : ℝ) : ℝ≥0∞ := ENNReal.ofReal (bound ell B ^ 2)

lemma squareBoundE_measurable (ell : ℝ) : Measurable (squareBoundE ell) := by
  unfold squareBoundE bound
  fun_prop

lemma linear_lintegral {ell B : ℝ} (hell : 0<ell) (hB : ell≤B) :
    (∫⁻ t in Ioc ell B, ENNReal.ofReal (t/ell^2)) =
      ENNReal.ofReal (((B^2-ell^2)/2)/ell^2) := by
  have hi : IntegrableOn (fun t : ℝ => t/ell^2) (Ioc ell B) :=
    ((continuous_id.div_const (ell^2)).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hn : ∀ᵐ t ∂volume.restrict (Ioc ell B), 0≤t/ell^2 := by
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro t ht
    exact div_nonneg (hell.le.trans ht.1.le) (sq_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,← intervalIntegral.integral_of_le hB]
  simp only [div_eq_mul_inv,intervalIntegral.integral_mul_const,_root_.integral_id]

lemma harmonic_square_integral {ell B : ℝ} (hell : 0<ell) (hB : ell≤B) :
    (∫⁻ t, squareBoundE ell t ∂kernel ell B) =
      ENNReal.ofReal (((B^2-ell^2)/2)/ell^2) := by
  rw [kernel_lintegral ell B (squareBoundE_measurable ell)]
  calc
    _ = ∫⁻ t in Ioc ell B, ENNReal.ofReal (t/ell^2) := by
      apply lintegral_congr_ae
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro t ht
      have ht0 : 0<t := hell.trans ht.1
      change ENNReal.ofReal (t⁻¹)*ENNReal.ofReal (bound ell t ^ 2) = _
      rw [bound_on hell ht.1.le,← ENNReal.ofReal_mul (inv_nonneg.mpr ht0.le)]
      congr 1
      field_simp
    _ = _ := linear_lintegral hell hB

theorem schur_two {ell : ℝ} (hell : 0<ell) (B : ℝ) :
    1+2*(∫⁻ t, squareBoundE ell t ∂kernel ell B) = squareBoundE ell B := by
  by_cases hB : ell≤B
  · rw [harmonic_square_integral hell hB,squareBoundE,bound_on hell hB]
    have hD : 0≤((B^2-ell^2)/2)/ell^2 := by
      apply div_nonneg
      · apply div_nonneg
        · nlinarith
        · norm_num
      · exact sq_nonneg _
    calc
      _ = ENNReal.ofReal (1+2*(((B^2-ell^2)/2)/ell^2)) := by
        rw [ENNReal.ofReal_add (by norm_num) (mul_nonneg (by norm_num) hD),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
        norm_num
      _ = _ := by
        congr 1
        field_simp
        ring
  · rw [kernel_eq_zero (le_of_not_ge hB),squareBoundE,bound_below hell (le_of_not_ge hB)]
    simp

theorem weighted_prefix_mass {ell B : ℝ} (hell : 0<ell) (hB : ell≤B) :
    (∑' n : ℕ, (2:ℝ≥0∞)^n * mass (kernel ell) n B) ≤ ENNReal.ofReal ((B/ell)^2) := by
  have h := weighted_total_bound (kernel ell) 2 (squareBoundE ell) (fun x => (schur_two hell x).le) B
  simpa only [squareBoundE,bound_on hell hB] using h

end ErdosPrimeInputs.HarmonicPrefixTilt

end

section

namespace ErdosPrimeInputs.HarmonicLongPrefixes

open scoped ENNReal
open WeightedKernelMass HarmonicPrefixKernel HarmonicPrefixTilt

noncomputable def tailMass (a : ℕ → ℝ≥0∞) (m : ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ, if m≤n then a n else 0

lemma half_power_antitone {m n : ℕ} (hmn : m≤n) :
    ((2:ℝ≥0∞)⁻¹)^n ≤ ((2:ℝ≥0∞)⁻¹)^m := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hp : ((2:ℝ≥0∞)⁻¹)^k ≤ 1 := pow_le_one₀ zero_le (by norm_num)
  calc
    _ = ((2:ℝ≥0∞)⁻¹)^m * ((2:ℝ≥0∞)⁻¹)^k := pow_add _ _ _
    _ ≤ ((2:ℝ≥0∞)⁻¹)^m * 1 := mul_le_mul le_rfl hp zero_le zero_le
    _ = _ := mul_one _

lemma unweight_two (a : ℝ≥0∞) (n : ℕ) :
    a = ((2:ℝ≥0∞)⁻¹)^n * ((2:ℝ≥0∞)^n*a) := by
  have hi : (2:ℝ≥0∞)⁻¹*2=1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  calc
    a = 1*a := (one_mul _).symm
    _ = ((2:ℝ≥0∞)⁻¹*2)^n*a := by rw [hi,one_pow]
    _ = _ := by rw [mul_pow,mul_assoc]

theorem weighted_tail_bound (a : ℕ → ℝ≥0∞) (m : ℕ) {W : ℝ≥0∞}
    (hW : (∑' n : ℕ, (2:ℝ≥0∞)^n*a n) ≤ W) :
    tailMass a m ≤ ((2:ℝ≥0∞)⁻¹)^m*W := by
  calc
    _ ≤ ∑' n : ℕ, ((2:ℝ≥0∞)⁻¹)^m*((2:ℝ≥0∞)^n*a n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      by_cases hn : m≤n
      · rw [ite_eq_left hn]
        exact (unweight_two (a n) n).trans_le (mul_le_mul (half_power_antitone hn) le_rfl zero_le zero_le)
      · rw [ite_eq_right hn]
        exact zero_le
    _ = ((2:ℝ≥0∞)⁻¹)^m*(∑' n : ℕ, (2:ℝ≥0∞)^n*a n) := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul le_rfl hW zero_le zero_le

noncomputable def longPrefixMass (ell B : ℝ) (m : ℕ) : ℝ≥0∞ :=
  tailMass (fun n => mass (kernel ell) n B) m

theorem long_prefix_mass {ell B : ℝ} (hell : 0<ell) (hB : ell≤B) (m : ℕ) :
    longPrefixMass ell B m ≤ ((2:ℝ≥0∞)⁻¹)^m*ENNReal.ofReal ((B/ell)^2) :=
  weighted_tail_bound _ m (weighted_prefix_mass hell hB)

end ErdosPrimeInputs.HarmonicLongPrefixes

end

section

namespace ErdosPrimeInputs.HighPrefixState

open Set MeasureTheory

abbrev State := ℝ × ℝ × Bool

noncomputable def initial (S B R : ℝ) : State :=
  (B,R,if S<R/B then true else false)

noncomputable def update (S : ℝ) (z : State) (t : ℝ) : State :=
  (t,z.2.1-t,if z.2.2=true ∨ S<(z.2.1-t)/t then true else false)

lemma update_measurable (S : ℝ) : Measurable (Function.uncurry (update S)) := by
  have hf : Measurable (fun x : State × ℝ => x.1.2.2) := by fun_prop
  have hr : Measurable (fun x : State × ℝ => (x.1.2.1-x.2)/x.2) := by fun_prop
  have hset : MeasurableSet {x : State × ℝ | x.1.2.2=true ∨ S<(x.1.2.1-x.2)/x.2} :=
    (hf (measurableSet_singleton true)).union (measurableSet_lt measurable_const hr)
  exact measurable_snd.prodMk ((by fun_prop : Measurable (fun x : State × ℝ => x.1.2.1-x.2)).prodMk
    (Measurable.ite hset measurable_const measurable_const))

lemma update_flag (S : ℝ) (z : State) (t : ℝ) :
    (update S z t).2.2=true ↔ z.2.2=true ∨ S<(z.2.1-t)/t := by
  by_cases h : z.2.2=true ∨ S<(z.2.1-t)/t <;> simp [update,h]

def Invariant (ell S : ℝ) (n : ℕ) (z : State) : Prop :=
  ell≤z.1 ∧ (z.2.2=true → (S-(n:ℝ))*z.1<z.2.1)

lemma invariant_measurable (ell S : ℝ) (n : ℕ) : MeasurableSet {z : State | Invariant ell S n z} := by
  have hf : Measurable (fun z : State => z.2.2) := measurable_snd.comp measurable_snd
  have hg : Measurable (fun z : State => z.2.1) := measurable_fst.comp measurable_snd
  have hb : MeasurableSet {z : State | ell≤z.1} := measurableSet_le measurable_const measurable_fst
  have hh : MeasurableSet {z : State | z.2.2=true} := hf (measurableSet_singleton true)
  have hr : MeasurableSet {z : State | (S-(n:ℝ))*z.1<z.2.1} :=
    measurableSet_lt (measurable_const.mul measurable_fst) hg
  simpa only [Invariant,imp_iff_not_or] using! hb.inter (hh.compl.union hr)

lemma initial_invariant {ell S B R : ℝ} (hell : 0<ell) (hB : ell≤B) :
    Invariant ell S 0 (initial S B R) := by
  have hB0 : 0<B := hell.trans_le hB
  refine ⟨hB,?_⟩
  intro hf
  have hhigh : S<R/B := by
    by_contra hn
    simp [initial,hn] at hf
  have h := (lt_div_iff₀ hB0).mp hhigh
  simpa only [Nat.cast_zero,sub_zero,initial] using! h

lemma update_invariant {ell S : ℝ} (hell : 0<ell) (n : ℕ) (z : State) (t : ℝ)
    (hz : Invariant ell S n z) (ht : ell<t ∧ t≤z.1) (hn : (n:ℝ)≤S) :
    Invariant ell S (n+1) (update S z t) := by
  have ht0 : 0<t := hell.trans ht.1
  refine ⟨ht.1.le,?_⟩
  intro hf
  have hcases := (update_flag S z t).mp hf
  change (S-((n+1:ℕ):ℝ))*t<z.2.1-t
  push_cast
  rcases hcases with hold | hnew
  · have hgap := hz.2 hold
    have hmul := mul_le_mul_of_nonneg_left ht.2 (sub_nonneg.mpr hn)
    nlinarith
  · have hgap := (lt_div_iff₀ ht0).mp hnew
    have hn0 : 0≤(n:ℝ)+1 := by positivity
    nlinarith [mul_nonneg hn0 ht0.le]

theorem short_high_gap {ell S : ℝ} (hell : 0<ell) (n : ℕ) (z : State)
    (hz : Invariant ell S n z) (hf : z.2.2=true) (hn : (n:ℝ)≤S/2) :
    S*ell/2<z.2.1 := by
  have hn0 : 0≤(n:ℝ) := Nat.cast_nonneg _
  have hS0 : 0≤S/2 := le_trans hn0 hn
  have hcoef : S/2≤S-(n:ℝ) := by linarith
  calc
    S*ell/2=(S/2)*ell := by ring
    _ ≤ (S-(n:ℝ))*z.1 := mul_le_mul hcoef hz.1 hell.le (hS0.trans hcoef)
    _ < z.2.1 := hz.2 hf

end ErdosPrimeInputs.HighPrefixState

end

end Erdos970

end OAI
