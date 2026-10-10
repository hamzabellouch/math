import Mathlib

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace EuclideanFiveColor.SmallArc
noncomputable section

def phaseSum (z : ℂ) (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, z ^ n

lemma pow_sub_one_bound (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    ‖z ^ n - 1‖ ≤ n * ‖z - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : z ^ (n+1) - 1 = z ^ n * (z - 1) + (z ^ n - 1) := by ring
    rw [he]
    calc
      _ ≤ ‖z ^ n * (z - 1)‖ + ‖z ^ n - 1‖ := norm_add_le _ _
      _ ≤ ‖z - 1‖ + n * ‖z - 1‖ := by
        simpa only [norm_mul, norm_pow, hz, one_pow, one_mul] using
          add_le_add_right ih ‖z - 1‖
      _ = _ := by push_cast; ring

lemma phaseSum_sub_bound (z : ℂ) (hz : ‖z‖ = 1) (N : ℕ) :
    ‖phaseSum z N - (N : ℂ)‖ ≤ (N : ℝ)^2 * ‖z-1‖ := by
  have he : phaseSum z N - (N : ℂ) = ∑ n ∈ Finset.range N, (z^n-1) := by
    simp [phaseSum, Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖z^n-1‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range N, (N : ℝ) * ‖z-1‖ := by
      apply Finset.sum_le_sum
      intro n hn
      exact (pow_sub_one_bound z hz n).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hn).le)
          (norm_nonneg _))
    _ = _ := by simp; ring

lemma phaseSum_lower (z : ℂ) (hz : ‖z‖ = 1) {N : ℕ} (hN : 0 < N)
    (hd : ‖z-1‖ ≤ 1 / (2 * (N : ℝ))) : (N : ℝ) / 2 ≤ ‖phaseSum z N‖ := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hb := phaseSum_sub_bound z hz N
  have he : (N : ℝ)^2 * ‖z-1‖ ≤ (N : ℝ)/2 := by
    have := mul_le_mul_of_nonneg_left hd (sq_nonneg (N : ℝ))
    calc
      _ ≤ (N : ℝ)^2 * (1 / (2 * (N : ℝ))) := this
      _ = _ := by field_simp
  have ht := norm_sub_norm_le (N : ℂ) (phaseSum z N)
  rw [norm_sub_rev] at ht
  have hn : ‖(N : ℂ)‖ = (N : ℝ) := by simp
  rw [hn] at ht
  linarith

lemma phase_energy (z : ℂ) (N : ℕ) :
    ‖phaseSum z N‖ ^ 2 = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (z^i * conj (z^j)).re := by
  calc
    _ = (phaseSum z N * conj (phaseSum z N)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    _ = _ := by
      simp only [phaseSum, map_sum, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      change Complex.reCLM (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, _) = _
      simp only [map_sum]
      rfl

lemma pow_mul_conj_pow (z : ℂ) (hz : ‖z‖ = 1) {i j : ℕ} (hji : j ≤ i) :
    z^i * conj (z^j) = z^(i-j) := by
  nth_rw 1 [← Nat.sub_add_cancel hji]
  rw [pow_add, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow,
    hz, one_pow, one_pow, Complex.ofReal_one, mul_one]

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
  (z : X → ℂ) (hz : Measurable z) (hu : ∀ x, ‖z x‖ = 1)

include hz hu
lemma integrable_pair (i j : ℕ) : Integrable (fun x => z x ^ i * conj (z x ^ j)) μ := by
  apply Integrable.of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall (fun x => by simp [hu])

omit hz in
lemma pair_moment_bound {N : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hm : ∀ n, 0 < n → n < N → ‖∫ x, z x ^ n ∂μ‖ ≤ c)
    {i j : ℕ} (hi : i < N) (hj : j < N) :
    (∫ x, z x^i * conj (z x^j) ∂μ).re ≤ (if i=j then 1 else 0) + c := by
  by_cases he : i = j
  · subst j
    have he : (fun x => z x^i * conj (z x^i)) = fun _ => (1 : ℂ) := by
      funext x
      simpa using pow_mul_conj_pow (z x) (hu x) (le_refl i)
    rw [he, integral_const]
    simp [hc]
  · simp only [he, ↓reduceIte, zero_add]
    by_cases hji : j ≤ i
    · have he : (fun x => z x^i * conj (z x^j)) = fun x => z x^(i-j) := by
        funext x
        exact pow_mul_conj_pow (z x) (hu x) hji
      rw [he]
      exact (Complex.re_le_norm _).trans (hm (i-j) (by omega) (by omega))
    · have he : (fun x => z x^i * conj (z x^j)) =
          fun x => conj (z x^(j-i)) := by
        funext x
        rw [← pow_mul_conj_pow (z x) (hu x) (by omega : i ≤ j)]
        simp only [map_mul, starRingEnd_self_apply]
        exact mul_comm _ _
      rw [he, integral_conj]
      exact (Complex.re_le_norm _).trans (by simpa using hm (j-i) (by omega) (by omega))

lemma phase_energy_integral_bound {N : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hm : ∀ n, 0 < n → n < N → ‖∫ x, z x ^ n ∂μ‖ ≤ c) :
    (∫ x, ‖phaseSum (z x) N‖ ^ 2 ∂μ) ≤ N + (N : ℝ)^2 * c := by
  simp_rw [phase_energy]
  rw [integral_finsetSum]
  · calc
      _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (∫ x, z x^i * conj (z x^j) ∂μ).re := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro j _
          exact (integral_re (integrable_pair μ z hz hu i j))
        · intro j _
          exact (integrable_pair μ z hz hu i j).re
      _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          ((if i=j then (1 : ℝ) else 0) + c) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact pair_moment_bound μ z hu hc hm (Finset.mem_range.mp hi)
          (Finset.mem_range.mp hj)
      _ = _ := by
        rw [Finset.sum_congr rfl (fun i hi => by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq, ite_eq_left hi])]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  · intro i _
    exact integrable_finsetSum _ (fun j _ => (integrable_pair μ z hz hu i j).re)

lemma integrable_energy (N : ℕ) : Integrable (fun x => ‖phaseSum (z x) N‖^2) μ := by
  have h : ∀ x, ‖phaseSum (z x) N‖ ≤ N := by
    intro x
    calc
      _ ≤ ∑ n ∈ Finset.range N, ‖z x ^ n‖ := norm_sum_le _ _
      _ = N := by simp [hu]
  apply Integrable.of_bound (by unfold phaseSum; fun_prop) ((N : ℝ)^2)
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (h x) 2)

/-- A quantitative finite-moment bound for the small arc about 1. -/
theorem small_arc_bound {N : ℕ} (hN : 0 < N) {c : ℝ} (hc : 0 ≤ c)
    (hm : ∀ n, 0 < n → n < N → ‖∫ x, z x ^ n ∂μ‖ ≤ c) :
    μ.real {x | ‖z x-1‖ ≤ 1 / (2 * (N : ℝ))} ≤ 4 / N + 4*c := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs : {x | ‖z x-1‖ ≤ 1 / (2 * (N : ℝ))} ⊆
      {x | (N : ℝ)^2 / 4 ≤ ‖phaseSum (z x) N‖ ^ 2} := by
    intro x hx
    have hh := phaseSum_lower (z x) (hu x) hN hx
    change (N : ℝ)^2 / 4 ≤ _
    nlinarith [norm_nonneg (phaseSum (z x) N)]
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖phaseSum (z x) N‖))
    (integrable_energy μ z hz hu N) ((N : ℝ)^2/4)
  have he := phase_energy_integral_bound μ z hz hu hc hm
  have hreal := measureReal_mono (μ := μ) hs
  have hm' : (N : ℝ)^2/4 * μ.real {x | ‖z x-1‖ ≤ 1 / (2 * (N : ℝ))} ≤
      N + (N : ℝ)^2*c :=
    (mul_le_mul_of_nonneg_left hreal (by positivity)).trans (hmark.trans he)
  calc
    _ ≤ (N + (N : ℝ)^2*c)/((N : ℝ)^2/4) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith [hm'])
    _ = _ := by field_simp

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

omit [MeasurableSpace X] hz hu in
/-- The source's qualitative choice, with explicit constants. -/
theorem exists_small_arc_constants (m : ℕ) (hm : 0 < m) :
    ∃ (ρ c : ℝ) (N : ℕ), 0 < ρ ∧ 0 < c ∧ 0 < N ∧
      ∀ (ω : Measure Circle) [IsProbabilityMeasure ω],
      (∀ n, 0 < n → n ≤ N → ‖∫ w, (w : ℂ)^n ∂ω‖ < c) →
      ω.real {w | ‖(w : ℂ)-1‖ ≤ 4*ρ} < 1/(4*(m : ℝ)^2) := by
  let N := 64*m^2
  have hN : 0 < N := by dsimp [N]; positivity
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hmp : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  refine ⟨1/(8*N), 1/N, N, by positivity, by positivity, hN, ?_⟩
  intro ω _ hω
  have hco : Continuous (fun w : Circle => (w : ℂ)) := continuous_subtype_val
  have hcm : Measurable (fun w : Circle => (w : ℂ)) := hco.measurable
  have hb := small_arc_bound ω (fun w : Circle => (w : ℂ))
    hcm Circle.norm_coe hN (by positivity : (0 : ℝ) ≤ 1/N)
    (fun n hn hnN => (hω n hn (le_of_lt hnN)).le)
  have hr : 4*(1/(8*(N : ℝ))) = 1/(2*N) := by ring
  rw [hr]
  apply hb.trans_lt
  have he : (N : ℝ) = 64*(m : ℝ)^2 := by dsimp [N]; push_cast; rfl
  rw [he]
  field_simp
  norm_num

end
end EuclideanFiveColor.SmallArc

/-! Fiberwise (possibly nonmeasurable) enumerations cause no measurability gap:
actual conditional samples lie in them by the measurable positive-atom event. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace EuclideanFiveColor.SampledAtoms
noncomputable section
variable {X Y G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace G] [MeasurableEq G]

lemma measurable_atom_mass (κ : Kernel Y G) [IsSFiniteKernel κ] :
    Measurable (fun p : Y × G => κ p.1 {p.2}) := by
  classical
  let η : Kernel (Y × G) G := κ.comap Prod.fst measurable_fst
  have hm : Measurable (fun p : (Y × G) × G =>
      if p.2 = p.1.2 then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_eq_fun measurable_snd (measurable_snd.comp measurable_fst))
      measurable_const measurable_const
  have h := hm.lintegral_kernel_prod_right' (κ := η)
  convert h using 1
  ext p
  change κ p.1 {p.2} = ∫⁻ d, (if d=p.2 then (1:ℝ≥0∞) else 0) ∂κ p.1
  simpa only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply] using
    (lintegral_indicator_one (μ := κ p.1) (measurableSet_singleton p.2)).symm

variable [StandardBorelSpace G] [Nonempty G]
lemma ae_sampled_positive_atom (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → Y) (b : X → G) (hp : Measurable p) (hb : Measurable b)
    (ha : ∀ᵐ y ∂μ.map p, ∀ᵐ d ∂condDistrib b p μ y, 0 < condDistrib b p μ y {d}) :
    ∀ᵐ x ∂μ, 0 < condDistrib b p μ (p x) {b x} := by
  have hm : MeasurableSet {z : Y × G | 0 < condDistrib b p μ z.1 {z.2}} :=
    measurableSet_lt measurable_const (measurable_atom_mass _)
  have he : ∀ᵐ z ∂μ.map p ⊗ₘ condDistrib b p μ,
      0 < condDistrib b p μ z.1 {z.2} := (Measure.ae_compProd_iff hm).mpr ha
  rw [compProd_map_condDistrib hp.aemeasurable hb.aemeasurable] at he
  exact ae_of_ae_map (hp.prodMk hb).aemeasurable he

omit [StandardBorelSpace G] [Nonempty G] in
lemma uniform_list_positive_atoms (μ : Measure G) {m : ℕ} (_hm : 0 < m)
    (g : Fin m → G) (hμ : μ = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i)) :
    ∀ᵐ d ∂μ, 0 < μ {d} := by
  classical
  have hi : (m : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (by simp)
  have hpt (i : Fin m) : 0 < μ {g i} := by
    rw [hμ, Measure.smul_apply, smul_eq_mul]
    apply ENNReal.mul_pos hi
    have hle : (1 : ℝ≥0∞) ≤ (∑ j, Measure.dirac (g j)) {g i} := by
      rw [Measure.finsetSum_apply]
      calc
        _ = Measure.dirac (g i) {g i} := by simp
        _ ≤ ∑ j, Measure.dirac (g j) {g i} :=
          Finset.single_le_sum (f := fun j : Fin m => Measure.dirac (g j) {g i})
            (fun j _ => bot_le) (Finset.mem_univ i)
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hle)
  rw [hμ] at hpt ⊢
  rw [Measure.ae_ennreal_smul_measure_iff hi, ae_finsetSum_measure_iff]
  intro i _
  simpa only [ae_dirac_eq, Filter.eventually_pure] using hpt i

omit [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace G] [Nonempty G] in
lemma in_list_of_positive_atom (μ : Measure G) {m : ℕ} (g : Fin m → G)
    (hμ : μ = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i))
    {d : G} (hd : 0 < μ {d}) : ∃ i, d = g i := by
  classical
  by_contra hn
  have hne (i : Fin m) : g i ≠ d := by intro hi; exact hn ⟨i, hi.symm⟩
  have hz : μ {d} = 0 := by
    rw [hμ, Measure.smul_apply, Measure.finsetSum_apply]
    simp [Measure.dirac_apply', hne]
  exact (ne_of_gt hd) hz

lemma ae_sampled_list (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → Y) (b : X → G) (hp : Measurable p) (hb : Measurable b)
    {m : ℕ} (hm : 0 < m) (g : Y → Fin m → G)
    (hg : ∀ᵐ y ∂μ.map p, condDistrib b p μ y =
      (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i)) :
    ∀ᵐ x ∂μ, ∃ i, b x = g (p x) i := by
  have hat := ae_sampled_positive_atom μ p b hp hb
    (hg.mono fun y hy => uniform_list_positive_atoms _ hm (g y) hy)
  filter_upwards [hat, ae_of_ae_map hp.aemeasurable hg] with x hx hxl
  exact in_list_of_positive_atom _ _ hxl hx

end
end EuclideanFiveColor.SampledAtoms

end
end
end
end

end OAI
