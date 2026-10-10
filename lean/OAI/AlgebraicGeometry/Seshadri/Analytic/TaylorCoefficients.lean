import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Analytic.ConvergentSeries

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators NNReal ENNReal

def wordExponent {n : ℕ} (w : Fin n → Bool) : ℕ × ℕ :=
  ((Finset.univ.filter (fun i => w i = false)).card,
    (Finset.univ.filter (fun i => w i = true)).card)

lemma wordExponent_degree {n : ℕ} (w : Fin n → Bool) :
    (wordExponent w).1 + (wordExponent w).2 = n := by
  simpa [wordExponent] using
    (Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => w i = false))

def coordinateVector : Bool → ℂ × ℂ
  | false => (1, 0)
  | true => (0, 1)

@[simp] lemma norm_coordinateVector (b : Bool) : ‖coordinateVector b‖ = 1 := by
  cases b <;> simp [coordinateVector, Prod.norm_def]

lemma prod_coordinate_word {n : ℕ} (w : Fin n → Bool) (x z : ℂ) :
    (∏ i, if w i = false then x else z) = x ^ (wordExponent w).1 * z ^ (wordExponent w).2 := by
  simp [Finset.prod_ite, wordExponent]

theorem multilinear_coordinate_expansion {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => ℂ × ℂ) ℂ) (x z : ℂ) :
    p (fun _ => (x, z)) =
      ∑ w : Fin n → Bool,
        p (fun i => coordinateVector (w i)) *
          x ^ (wordExponent w).1 * z ^ (wordExponent w).2 := by
  have h := p.map_sum (fun (_ : Fin n) (b : Bool) =>
    (if b = false then x else z) • coordinateVector b)
  have he : (fun _ : Fin n => ∑ b : Bool,
      (if b = false then x else z) • coordinateVector b) = fun _ => (x, z) := by
    ext i <;> simp [coordinateVector]
  rw [he] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro w _
  rw [p.map_smul_univ, smul_eq_mul, prod_coordinate_word]
  ring

def ordinaryCoefficient (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ) (a b : ℕ) : ℂ :=
  ∑ w : Fin (a + b) → Bool, if wordExponent w = (a, b) then
    p (a + b) (fun i => coordinateVector (w i)) else 0

lemma ordinaryCoefficient_norm_le (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ) (a b : ℕ) :
    ‖ordinaryCoefficient p a b‖ ≤ (2 : ℝ) ^ (a + b) * ‖p (a + b)‖ := by
  calc
    _ ≤ ∑ _w : Fin (a + b) → Bool, ‖p (a + b)‖ := by
      apply norm_sum_le_of_le _
      intro w _
      split_ifs
      · simpa using (p (a + b)).le_opNorm (fun i => coordinateVector (w i))
      · simp
    _ = _ := by simp

lemma ordinaryCoefficient_eq_degree (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    {a b n : ℕ} (h : a + b = n) :
    ordinaryCoefficient p a b = ∑ w : Fin n → Bool, if wordExponent w = (a, b) then
      p n (fun i => coordinateVector (w i)) else 0 := by
  subst n
  rfl

theorem ordinaryCoefficient_homogeneous (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (n : ℕ) (x z : ℂ) :
    (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
      ordinaryCoefficient p ab.1 ab.2 * x ^ ab.1 * z ^ ab.2) =
        p n (fun _ => (x, z)) := by
  rw [multilinear_coordinate_expansion]
  have he : (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
      ordinaryCoefficient p ab.1 ab.2 * x ^ ab.1 * z ^ ab.2) =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ w : Fin n → Bool,
        if wordExponent w = ab then
          p n (fun i => coordinateVector (w i)) * x ^ ab.1 * z ^ ab.2 else 0 := by
    apply Finset.sum_congr rfl
    intro ab hab
    rw [ordinaryCoefficient_eq_degree p (Finset.HasAntidiagonal.mem_antidiagonal.mp hab)]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w _
    split_ifs <;> simp
  rw [he, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  simp [Finset.HasAntidiagonal.mem_antidiagonal, wordExponent_degree]

theorem ordinaryCoefficient_geometric_bound (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (ρ C : ℝ) (hρ : 0 < ρ)
    (hp : ∀ n, ‖p n‖ ≤ C / ρ ^ n) (a b : ℕ) :
    ‖ordinaryCoefficient p a b‖ * (ρ / 4) ^ (a + b) ≤ C * (1 / 2 : ℝ) ^ (a + b) := by
  calc
    _ ≤ ((2 : ℝ) ^ (a + b) * (C / ρ ^ (a + b))) * (ρ / 4) ^ (a + b) := by
      gcongr
      exact (ordinaryCoefficient_norm_le p a b).trans (mul_le_mul_of_nonneg_left
        (hp (a + b)) (by positivity))
    _ = _ := by
      rw [div_pow, div_pow]
      field_simp
      ring_nf
      rw [Nat.mul_comm a 2, Nat.mul_comm b 2, pow_mul, pow_mul]
      norm_num

theorem ordinaryCoefficient_absolutely_convergent
    (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ) (ρ : ℝ≥0)
    (hρ : 0 < ρ) (hr : (ρ : ℝ≥0∞) < p.radius) :
    Summable (fun ab : ℕ × ℕ => ‖ordinaryCoefficient p ab.1 ab.2‖ *
      ((ρ : ℝ) / 4) ^ (ab.1 + ab.2)) := by
  obtain ⟨C, _, hp⟩ := p.norm_le_div_pow_of_pos_of_lt_radius hρ hr
  have hs : Summable (fun ab : ℕ × ℕ => C * ((1 / 2 : ℝ) ^ (ab.1 + ab.2))) := by
    have h := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1))
    simpa only [pow_add] using (h.mul_of_nonneg h (fun _ => by positivity)
      (fun _ => by positivity)).mul_left C
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun ab => ordinaryCoefficient_geometric_bound p ρ C hρ hp ab.1 ab.2) hs

lemma ordinary_hasSum_by_degree (c : ℕ × ℕ → ℂ) (hc : Summable c) :
    HasSum (fun n : ℕ => ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, c ab) (∑' ab, c ab) := by
  let e := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)
  have hs : HasSum (fun s : Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n => c s.2.val)
      (∑' ab, c ab) := e.hasSum_iff.mpr hc.hasSum
  apply hs.sigma
  intro n
  simpa only [Finset.sum_coe_sort] using
    (hasSum_fintype (fun ab : Finset.HasAntidiagonal.antidiagonal n => c ab.val))

lemma ordinary_terms_summable (c : ℕ × ℕ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hc : Summable (fun ab => ‖c ab‖ * R ^ (ab.1 + ab.2)))
    (x z : ℂ) (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) :
    Summable (fun ab => c ab * x ^ ab.1 * z ^ ab.2) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hc
  intro ab
  simp only [norm_mul, norm_pow, pow_add, ← mul_assoc]
  gcongr

theorem hasFPowerSeriesOnBall_ordinary_expansion
    (f : ℂ × ℂ → ℂ) (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (r : ℝ≥0∞) (hf : HasFPowerSeriesOnBall f p 0 r)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hr : (ρ : ℝ≥0∞) < r)
    (x z : ℂ) (hx : ‖x‖ < (ρ : ℝ) / 4) (hz : ‖z‖ < (ρ : ℝ) / 4) :
    f (x,z) = ∑' ab : ℕ × ℕ, ordinaryCoefficient p ab.1 ab.2 * x ^ ab.1 * z ^ ab.2 := by
  have hc := ordinaryCoefficient_absolutely_convergent p ρ hρ (hr.trans_le hf.r_le)
  have hs := ordinary_terms_summable (fun ab => ordinaryCoefficient p ab.1 ab.2)
    ((ρ : ℝ) / 4) (by positivity) hc x z hx.le hz.le
  have hh := ordinary_hasSum_by_degree _ hs
  simp_rw [ordinaryCoefficient_homogeneous] at hh
  have hnorm : ‖(x,z)‖₊ < ρ := by
    change max ‖x‖ ‖z‖ < (ρ : ℝ)
    apply max_lt
    · linarith [show (0 : ℝ) < ρ from hρ]
    · linarith [show (0 : ℝ) < ρ from hρ]
  have hm : (x,z) ∈ Metric.eball (0 : ℂ × ℂ) r := by
    rw [mem_eball_zero_iff]
    exact (ENNReal.coe_lt_coe.mpr hnorm).trans hr
  have hh' := hf.hasSum hm
  simpa only [zero_add] using hh'.unique hh

theorem analyticAt_exists_ordinary_expansion (f : ℂ × ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    ∃ c : ℕ × ℕ → ℂ, ∃ R : ℝ, 0 < R ∧
      Summable (fun ab => ‖c ab‖ * R ^ (ab.1 + ab.2)) ∧
      ∀ x z : ℂ, ‖x‖ < R → ‖z‖ < R →
        f (x,z) = ∑' ab : ℕ × ℕ, c ab * x ^ ab.1 * z ^ ab.2 := by
  obtain ⟨p, r, hp⟩ := hf
  obtain ⟨ρ, hρ, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hρ' : (0 : ℝ≥0) < ρ := by exact_mod_cast hρ
  refine ⟨fun ab => ordinaryCoefficient p ab.1 ab.2, (ρ : ℝ) / 4, by positivity,
    ordinaryCoefficient_absolutely_convergent p ρ hρ' (hr.trans_le hp.r_le), ?_⟩
  intro x z hx hz
  exact hasFPowerSeriesOnBall_ordinary_expansion f p r hp ρ hρ' hr x z hx hz

end
end MaximalSeshadri.AnalyticCoordinates

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators Topology
open Filter Set

lemma monomialDeriv_at_zero (n a : ℕ) :
    monomialDeriv n a 0 = if n = a then (a.factorial : ℂ) else 0 := by
  by_cases h : n = a
  · subst n
    simp [monomialDeriv, Nat.descFactorial_self]
  · rw [ite_eq_right_iff.mpr (fun he => (h he).elim)]
    by_cases hn : n < a
    · simp [monomialDeriv, Nat.descFactorial_eq_zero_iff_lt.mpr hn]
    · have hd : n - a ≠ 0 := by omega
      simp [monomialDeriv, zero_pow hd]

lemma seriesPartial_at_zero (c : Exponent → ℂ) (a b : ℕ) :
    seriesPartial c a b 0 0 = c (a,b) * (a.factorial : ℂ) * (b.factorial : ℂ) := by
  unfold seriesPartial
  rw [tsum_eq_single (a,b)]
  · simp [monomialDeriv_at_zero]
  · intro p hp
    by_cases h₁ : p.1 = a
    · have h₂ : p.2 ≠ b := by intro h₂; exact hp (Prod.ext h₁ h₂)
      simp [monomialDeriv_at_zero, h₂]
    · simp [monomialDeriv_at_zero, h₁]

theorem mixedDeriv_at_zero (c : Exponent → ℂ) (hc : ConvergentSeries c) (a b : ℕ) :
    iteratedDeriv b (fun z => iteratedDeriv a (fun x => seriesEval c x z) 0) 0 =
      c (a,b) * (a.factorial : ℂ) * (b.factorial : ℂ) := by
  obtain ⟨R, hR, hconv⟩ := hc
  rw [mixedDeriv_seriesEval c (R / 2)
    (derivativeSummable_of_absolute c R (R / 2) hR (by positivity) (by linarith) hconv)
    a b 0 0 (by simpa using (show (0 : ℝ) < R / 2 by positivity))
      (by simpa using (show (0 : ℝ) < R / 2 by positivity))]
  exact seriesPartial_at_zero c a b

lemma mixedDeriv_congr_germ (f g : ℂ × ℂ → ℂ) (h : f =ᶠ[𝓝 0] g) (a b : ℕ) :
    iteratedDeriv b (fun z => iteratedDeriv a (fun x => f (x,z)) 0) 0 =
      iteratedDeriv b (fun z => iteratedDeriv a (fun x => g (x,z)) 0) 0 := by
  obtain ⟨ε, hε, hfg⟩ := Metric.eventually_nhds_iff.mp h
  have hn : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < ε := by
    change {z : ℂ | ‖z‖ < ε} ∈ 𝓝 (0 : ℂ)
    simpa only [Metric.ball, dist_zero_right] using
      (Metric.ball_mem_nhds (0 : ℂ) hε)
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [hn] with z hz
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [hn] with x hx
  apply hfg
  simpa [Prod.dist_eq, dist_zero_right, max_lt_iff] using And.intro hx hz

theorem convergent_expansion_unique (c d : Exponent → ℂ)
    (hc : ConvergentSeries c) (hd : ConvergentSeries d)
    (heq : (fun q : ℂ × ℂ => seriesEval c q.1 q.2) =ᶠ[𝓝 0]
      (fun q : ℂ × ℂ => seriesEval d q.1 q.2)) : c = d := by
  ext ab
  have h := mixedDeriv_congr_germ _ _ heq ab.1 ab.2
  rw [mixedDeriv_at_zero c hc, mixedDeriv_at_zero d hd] at h
  exact mul_right_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero ab.1)
    (mul_right_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero ab.2) h)

def analyticFunctionAlgebra : Subalgebra ℂ (ℂ × ℂ → ℂ) where
  carrier := {f | AnalyticAt ℂ f 0}
  mul_mem' := fun hf hg => hf.mul hg
  add_mem' := fun hf hg => hf.add hg
  algebraMap_mem' := fun _ => analyticAt_const

def analyticCoefficients (f : analyticFunctionAlgebra) : Exponent → ℂ :=
  (analyticAt_exists_ordinary_expansion f f.property).choose

lemma analyticCoefficients_spec (f : analyticFunctionAlgebra) :
    ConvergentSeries (analyticCoefficients f) ∧
      (fun q : ℂ × ℂ => f.val q) =ᶠ[𝓝 0]
        (fun q : ℂ × ℂ => seriesEval (analyticCoefficients f) q.1 q.2) := by
  obtain ⟨R, hR, hsum, heq⟩ := (analyticAt_exists_ordinary_expansion f f.property).choose_spec
  refine ⟨⟨R, hR, hsum⟩, ?_⟩
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨R, hR, ?_⟩
  intro q hq
  have hq' : ‖q.1‖ < R ∧ ‖q.2‖ < R := by
    simpa [Prod.dist_eq, dist_zero_right, Prod.norm_def, max_lt_iff] using hq
  exact heq q.1 q.2 hq'.1 hq'.2

theorem analyticCoefficients_eq_derivative (f : analyticFunctionAlgebra) (a b : ℕ) :
    analyticCoefficients f (a,b) * (a.factorial : ℂ) * (b.factorial : ℂ) =
      iteratedDeriv b (fun z => iteratedDeriv a (fun x => f.val (x,z)) 0) 0 := by
  rw [mixedDeriv_congr_germ _ _ (analyticCoefficients_spec f).2 a b]
  exact (mixedDeriv_at_zero _ (analyticCoefficients_spec f).1 a b).symm

end
end MaximalSeshadri.AnalyticCoordinates

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators Topology
open Filter

local instance : Finset.HasAntidiagonal Exponent :=
  Finset.HasAntidiagonal.antidiagonalOfLocallyFinite

def coeffConvolution (c d : Exponent → ℂ) (e : Exponent) : ℂ :=
  ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal e, c ab.1 * d ab.2

lemma absolute_mono {c : Exponent → ℂ} {R ρ : ℝ}
    (hR : AbsolutelyConvergentAt c R) (hρ : 0 ≤ ρ) (h : ρ ≤ R) :
    AbsolutelyConvergentAt c ρ := by
  exact Summable.of_nonneg_of_le (fun p => by positivity)
    (fun p => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ h _) (norm_nonneg _)) hR

lemma absolute_terms_summable {c : Exponent → ℂ} {R : ℝ}
    (hc : AbsolutelyConvergentAt c R) {x z : ℂ} (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) :
    Summable (fun e : Exponent => ‖c e * x ^ e.1 * z ^ e.2‖) := by
  exact (ordinary_terms_summable c R ((norm_nonneg _).trans hx) hc x z hx hz).norm

lemma absolute_convolution {c d : Exponent → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hc : AbsolutelyConvergentAt c R) (hd : AbsolutelyConvergentAt d R) :
    AbsolutelyConvergentAt (coeffConvolution c d) R := by
  have hs := hc.mul_of_nonneg hd (fun e => by positivity) (fun e => by positivity)
  have ht := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd
    (A := Exponent)).summable_iff.mpr hs
  have hu := ht.sigma
  change Summable (fun e : Exponent => ∑' ab : Finset.HasAntidiagonal.antidiagonal e,
    (‖c ab.val.1‖ * R ^ (ab.val.1.1 + ab.val.1.2)) *
      (‖d ab.val.2‖ * R ^ (ab.val.2.1 + ab.val.2.2))) at hu
  have hu' : Summable (fun e : Exponent => ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal e,
    (‖c ab.1‖ * R ^ (ab.1.1 + ab.1.2)) *
      (‖d ab.2‖ * R ^ (ab.2.1 + ab.2.2))) := hu.congr (fun e => by
        rw [tsum_fintype]
        exact Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal e)
          (fun ab : Exponent × Exponent => (‖c ab.1‖ * R ^ (ab.1.1 + ab.1.2)) *
            (‖d ab.2‖ * R ^ (ab.2.1 + ab.2.2))))
  refine Summable.of_nonneg_of_le (fun e => by positivity) (fun e => ?_) hu'
  calc
    ‖coeffConvolution c d e‖ * R ^ (e.1 + e.2) ≤
      (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal e, ‖c ab.1 * d ab.2‖) *
        R ^ (e.1 + e.2) := by
          exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg hR _)
    _ = ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal e,
      (‖c ab.1‖ * R ^ (ab.1.1 + ab.1.2)) *
        (‖d ab.2‖ * R ^ (ab.2.1 + ab.2.2)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ab hab
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      have he₁ := congrArg Prod.fst he
      have he₂ := congrArg Prod.snd he
      simp only [Prod.fst_add, Prod.snd_add] at he₁ he₂
      rw [← he₁, ← he₂, norm_mul]
      simp only [pow_add]
      ring

lemma seriesEval_convolution {c d : Exponent → ℂ} {R : ℝ}
    (hc : AbsolutelyConvergentAt c R) (hd : AbsolutelyConvergentAt d R)
    {x z : ℂ} (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) :
    seriesEval (coeffConvolution c d) x z = seriesEval c x z * seriesEval d x z := by
  have hf := absolute_terms_summable hc hx hz
  have hg := absolute_terms_summable hd hx hz
  have hs := summable_mul_of_summable_norm hf hg
  let E := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := Exponent)
  have ht := E.summable_iff.mpr hs
  unfold seriesEval
  rw [tsum_mul_tsum_of_summable_norm hf hg, ← E.tsum_eq]
  have hsum := ht.tsum_sigma
  simp only [Function.comp_def] at hsum
  rw [hsum]
  apply tsum_congr
  intro e
  change _ = ∑' ab : Finset.HasAntidiagonal.antidiagonal e,
    (c ab.val.1 * x ^ ab.val.1.1 * z ^ ab.val.1.2) *
      (d ab.val.2 * x ^ ab.val.2.1 * z ^ ab.val.2.2)
  rw [tsum_fintype]
  have heq := Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal e)
    (fun ab : Exponent × Exponent =>
      (c ab.1 * x ^ ab.1.1 * z ^ ab.1.2) * (d ab.2 * x ^ ab.2.1 * z ^ ab.2.2))
  rw [heq]
  simp only [coeffConvolution, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  have he₁ := congrArg Prod.fst he
  have he₂ := congrArg Prod.snd he
  simp only [Prod.fst_add, Prod.snd_add] at he₁ he₂
  rw [← he₁, ← he₂]
  simp only [pow_add]
  ring

end
end MaximalSeshadri.AnalyticCoordinates


end
end
end

end OAI
