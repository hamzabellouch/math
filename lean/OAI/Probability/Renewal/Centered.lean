import OAI.Probability.Renewal.Moments

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace HoneycombLocal

def natMean (p : PMF ℕ) : ℝ := ∫ j : ℕ, (j : ℝ) ∂p.toMeasure

def natVariance (p : PMF ℕ) : ℝ := ∫ j : ℕ, ((j : ℝ) - natMean p) ^ 2 ∂p.toMeasure

def natThird (p : PMF ℕ) : ℝ := ∫ j : ℕ, |(j : ℝ) - natMean p| ^ 3 ∂p.toMeasure

lemma natMean_nonneg (p : PMF ℕ) : 0 ≤ natMean p := integral_nonneg (fun _ => Nat.cast_nonneg _)
lemma natVariance_nonneg (p : PMF ℕ) : 0 ≤ natVariance p := integral_nonneg (fun _ => sq_nonneg _)
lemma natThird_nonneg (p : PMF ℕ) : 0 ≤ natThird p := integral_nonneg (fun _ => by positivity)

lemma nat_memLp (p : PMF ℕ) {n : ℕ} (hn : n ≠ 0)
    (hi : Integrable (fun j : ℕ => (j : ℝ) ^ n) p.toMeasure) :
    MemLp (fun j : ℕ => (j : ℝ)) n p.toMeasure := by
  apply (integrable_norm_rpow_iff Measurable.of_discrete.aestronglyMeasurable (by exact_mod_cast hn) (by simp)).mp
  simpa only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_natCast] using hi

lemma natVariance_eq_sub (p : PMF ℕ)
    (hi : Integrable (fun j : ℕ => (j : ℝ) ^ 2) p.toMeasure) :
    natVariance p = (∫ j : ℕ, (j : ℝ) ^ 2 ∂p.toMeasure) - natMean p ^ 2 := by
  have hm := nat_memLp p (by norm_num : (2 : ℕ) ≠ 0) hi
  unfold natVariance natMean
  rw [← variance_eq_integral Measurable.of_discrete.aemeasurable, variance_eq_sub hm]
  rfl

lemma natVariance_le_second (p : PMF ℕ)
    (hi : Integrable (fun j : ℕ => (j : ℝ) ^ 2) p.toMeasure) :
    natVariance p ≤ ∫ j : ℕ, (j : ℝ) ^ 2 ∂p.toMeasure := by
  rw [natVariance_eq_sub p hi]
  exact sub_le_self _ (sq_nonneg _)

lemma integrable_pair_square (p : PMF ℕ)
    (h1 : Integrable (fun j : ℕ => (j : ℝ)) p.toMeasure)
    (h2 : Integrable (fun j : ℕ => (j : ℝ) ^ 2) p.toMeasure) :
    Integrable (fun z : ℕ × ℕ => ((z.1 : ℝ) - z.2) ^ 2) (p.toMeasure.prod p.toMeasure) := by
  have h := ((h2.comp_fst p.toMeasure).sub ((h1.mul_prod h1).const_mul 2)).add (h2.comp_snd p.toMeasure)
  apply h.congr
  filter_upwards [] with z
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

lemma two_copy_variance (p : PMF ℕ)
    (h1 : Integrable (fun j : ℕ => (j : ℝ)) p.toMeasure)
    (h2 : Integrable (fun j : ℕ => (j : ℝ) ^ 2) p.toMeasure) :
    (∫ z : ℕ × ℕ, ((z.1 : ℝ) - z.2) ^ 2 ∂(p.toMeasure.prod p.toMeasure)) = 2 * natVariance p := by
  have hid : (fun z : ℕ × ℕ => ((z.1 : ℝ) - z.2) ^ 2) =
      fun z => (z.1 : ℝ) ^ 2 - 2 * ((z.1 : ℝ) * z.2) + (z.2 : ℝ) ^ 2 := by ext z; ring
  have hf : Integrable (fun z : ℕ × ℕ => (z.1 : ℝ) ^ 2 - 2 * ((z.1 : ℝ) * z.2)) (p.toMeasure.prod p.toMeasure) := by
    exact (h2.comp_fst p.toMeasure).sub ((h1.mul_prod h1).const_mul 2)
  rw [hid, integral_add hf (h2.comp_snd p.toMeasure),
    integral_sub (h2.comp_fst p.toMeasure) ((h1.mul_prod h1).const_mul 2), integral_const_mul,
    integral_fun_fst (fun j : ℕ => (j : ℝ) ^ 2), integral_fun_snd (fun j : ℕ => (j : ℝ) ^ 2),
    integral_prod_mul (fun j : ℕ => (j : ℝ)) (fun j : ℕ => (j : ℝ)), natVariance_eq_sub p h2]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul, natMean]
  ring

lemma rectangle_variance_bound (p : PMF ℕ)
    (h1 : Integrable (fun j : ℕ => (j : ℝ)) p.toMeasure)
    (h2 : Integrable (fun j : ℕ => (j : ℝ) ^ 2) p.toMeasure)
    (s b : Set ℕ) (r : ℝ) (hlower : ∀ j ∈ s, ∀ l ∈ b, r ≤ ((j : ℝ) - l) ^ 2) :
    p.toMeasure.real s * p.toMeasure.real b * r ≤ 2 * natVariance p := by
  calc
    p.toMeasure.real s * p.toMeasure.real b * r = ∫ _ in s ×ˢ b, r ∂(p.toMeasure.prod p.toMeasure) := by
      simp [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
    _ ≤ ∫ z : ℕ × ℕ in s ×ˢ b, ((z.1 : ℝ) - z.2) ^ 2 ∂(p.toMeasure.prod p.toMeasure) := by
      apply setIntegral_mono_on (integrable_const _) (integrable_pair_square p h1 h2).integrableOn MeasurableSet.of_discrete
      intro z hz
      exact hlower z.1 hz.1 z.2 hz.2
    _ ≤ ∫ z : ℕ × ℕ, ((z.1 : ℝ) - z.2) ^ 2 ∂(p.toMeasure.prod p.toMeasure) :=
      setIntegral_le_integral (integrable_pair_square p h1 h2) (ae_of_all _ (fun _ => sq_nonneg _))
    _ = 2 * natVariance p := two_copy_variance p h1 h2

lemma natThird_le_raw (p : PMF ℕ)
    (h3 : Integrable (fun j : ℕ => (j : ℝ) ^ 3) p.toMeasure) :
    natThird p ≤ 4 * ((∫ j : ℕ, (j : ℝ) ^ 3 ∂p.toMeasure) + natMean p ^ 3) := by
  have hm := nat_memLp p (by norm_num : (3 : ℕ) ≠ 0) h3
  have hi : Integrable (fun j : ℕ => |(j : ℝ) - natMean p| ^ 3) p.toMeasure := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hm.sub (memLp_const (natMean p))).integrable_norm_pow' (p := 3)
  calc
    natThird p ≤ ∫ j : ℕ, 4 * ((j : ℝ) ^ 3 + natMean p ^ 3) ∂p.toMeasure := by
      apply integral_mono hi ((h3.add (integrable_const _)).const_mul 4)
      intro j
      calc
        |(j : ℝ) - natMean p| ^ 3 ≤ ((j : ℝ) + natMean p) ^ 3 := by
          gcongr
          exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (Nat.cast_nonneg j), abs_of_nonneg (natMean_nonneg p)])
        _ ≤ 4 * ((j : ℝ) ^ 3 + natMean p ^ 3) := by
          have hh := add_pow_le (Nat.cast_nonneg (α := ℝ) j) (natMean_nonneg p) 3
          norm_num at hh
          exact hh
    _ = _ := by rw [integral_const_mul, integral_add h3 (integrable_const _)]; simp

def centeredMeasure (p : PMF ℕ) : Measure ℝ := p.toMeasure.map (fun j : ℕ => (j : ℝ) - natMean p)

instance centeredMeasure_probability (p : PMF ℕ) : IsProbabilityMeasure (centeredMeasure p) := by
  unfold centeredMeasure
  infer_instance

lemma centered_integral (p : PMF ℕ) {F : ℝ → ℝ} (hF : AEStronglyMeasurable F (centeredMeasure p)) :
    (∫ x, F x ∂centeredMeasure p) = ∫ j : ℕ, F ((j : ℝ) - natMean p) ∂p.toMeasure :=
  integral_map Measurable.of_discrete.aemeasurable hF

lemma centered_mean (p : PMF ℕ) (h1 : Integrable (fun j : ℕ => (j : ℝ)) p.toMeasure) :
    (∫ x, x ∂centeredMeasure p) = 0 := by
  rw [centered_integral p (F := fun x => x) (by fun_prop),
    integral_sub h1 (integrable_const _)]
  simp [natMean]

lemma centered_variance (p : PMF ℕ) : (∫ x, x ^ 2 ∂centeredMeasure p) = natVariance p := by
  exact centered_integral p (by fun_prop)

lemma centered_third (p : PMF ℕ) : (∫ x, ‖x‖ ^ 3 ∂centeredMeasure p) = natThird p := by
  simpa only [Real.norm_eq_abs, natThird] using centered_integral p (F := fun x => ‖x‖ ^ 3) (by fun_prop)

lemma centered_memLp (p : PMF ℕ) {n : ℕ} (hn : n ≠ 0)
    (hi : Integrable (fun j : ℕ => (j : ℝ) ^ n) p.toMeasure) :
    MemLp id n (centeredMeasure p) := by
  apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable Measurable.of_discrete.aemeasurable).mpr
  exact (nat_memLp p hn hi).sub (memLp_const _)

lemma centered_char (p : PMF ℕ) (t : ℝ) :
    charFun (centeredMeasure p) t = Complex.exp (-((natMean p * t : ℝ) : ℂ) * Complex.I) * latticeChar p t := by
  rw [charFun_apply, centeredMeasure, integral_map Measurable.of_discrete.aemeasurable (by fun_prop)]
  simp only [RCLike.inner_apply, conj_trivial]
  have hid : (fun j : ℕ => Complex.exp (((j : ℝ) - natMean p) * t * Complex.I)) =
      fun j : ℕ => Complex.exp (-((natMean p * t : ℝ) : ℂ) * Complex.I) * Complex.exp (((j : ℝ) * t : ℝ) * Complex.I) := by
    ext j
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [mul_comm t]
  push_cast
  push_cast at hid
  rw [hid, integral_const_mul]
  simp [latticeChar]

end HoneycombLocal

end

end OAI
