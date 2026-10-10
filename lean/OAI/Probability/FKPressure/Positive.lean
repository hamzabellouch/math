import OAI.Probability.FKPressure.Polydisk

namespace OAI

 

noncomputable section
open Finset FormalMultilinearSeries
open scoped Classical Topology NNReal ENNReal
namespace BelowOne.FKPressure
open PressureSeries
variable {V I : Type*} [Fintype V]

def complexSitePolynomial (ends : I → V × V) (E : Finset I)
    (s : ℝ) (v : I → ℝ) (x : V → ℂ) : ℂ :=
  (∑ A ∈ E.powerset, (∏ e ∈ A, (v e : ℂ)) *
    ∏ c : (graph ⊥ ends A).ConnectedComponent, (1 + (s : ℂ) *
      ∏ i ∈ univ.filter (fun i => (graph ⊥ ends A).connectedComponentMk i = c), x i)) /
    ∏ e ∈ E, (1 + (v e : ℂ))

lemma complexSitePolynomial_real (ends : I → V × V) (E : Finset I)
    (s : ℝ) (v : I → ℝ) (x : V → ℝ) :
    complexSitePolynomial ends E s v (fun i => (x i : ℂ)) =
      (percolationSitePolynomial ends E s v x : ℂ) := by
  unfold complexSitePolynomial percolationSitePolynomial componentProduct
  push_cast
  rfl

lemma analyticAt_complexSitePolynomial (ends : I → V × V) (E : Finset I)
    (s : ℝ) (v : I → ℝ) (x : V → ℂ) :
    AnalyticAt ℂ (complexSitePolynomial ends E s v) x := by
  unfold complexSitePolynomial
  apply AnalyticAt.div_const
  apply Finset.analyticAt_fun_sum
  intro A hA
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro c hc
  apply AnalyticAt.add analyticAt_const
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i hi
  exact (ContinuousLinearMap.proj i : (V → ℂ) →L[ℂ] ℂ).analyticAt x

lemma complex_pressure_exponential (ends : I → V × V) (E : Finset I)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (v : I → ℝ) (hv : ∀ e ∈ E, 0 ≤ v e)
    {r : ℝ} (hr : 1 < r)
    (hR : ENNReal.ofReal r < (PositiveAnalyticCube.taylor (pressure ends E u v)).radius) :
    ∀ x : V → ℂ, (∀ i, ‖x i‖ < r) →
      Complex.exp (- (complexify (PositiveAnalyticCube.taylor (pressure ends E u v))).sum x) =
        complexSitePolynomial ends E (-u) v x := by
  let p := PositiveAnalyticCube.taylor (pressure ends E u v)
  have hp := pressure_expansion ends E hu hu1 v hv
  have hn : ∀ a : Labels V, 0 ≤ weight p a := fun a => hp.2.1 a.1 a.2
  have hb {x : V → ℂ} (hx : ∀ i, ‖x i‖ < r) : x ∈ Metric.eball 0 (complexify p).radius := by
    apply mem_eball_zero_iff.mpr
    have hnorm := norm_lt_of_coordinates (zero_lt_one.trans hr) hx
    exact (show ‖x‖ₑ ≤ ENNReal.ofReal r by
      simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hnorm.le).trans_lt
        (hR.trans_le (complexify_radius p hn))
  have hf : AnalyticOnNhd ℂ (fun x => Complex.exp (- (complexify p).sum x))
      {x | ∀ i, ‖x i‖ < r} := by
    intro x hx
    exact ((complexify p).analyticOnNhd x (hb hx)).neg.cexp
  have hg : AnalyticOnNhd ℂ (complexSitePolynomial ends E (-u) v)
      {x | ∀ i, ‖x i‖ < r} := fun x _ => analyticAt_complexSitePolynomial ends E (-u) v x
  have he : ∀ t : V → ℝ, (∀ i, t i ∈ Set.Icc 0 1) →
      Complex.exp (- (complexify p).sum (fun i => (t i : ℂ))) =
        complexSitePolynomial ends E (-u) v (fun i => (t i : ℂ)) := by
    intro t ht
    have hsum : p.sum t = pressure ends E u v t := (hp.2.2 t ht).tsum_eq
    rw [complexify_sum_real, hsum, complexSitePolynomial_real]
    unfold pressure
    rw [Complex.ofReal_neg, neg_neg, ← Complex.ofReal_exp,
      Real.exp_log (percolationSitePolynomial_pos ends E hu.le hu1 v hv t ht)]
  exact identity_on_polydisk hr hf hg he

lemma pressure_coefficient_connected (ends : I → V × V) (E : Finset I)
    (u : ℝ) (v : I → ℝ) (hv : ∀ e ∈ E, 0 ≤ v e) (m : V → ℕ)
    (hm : 0 < coefficient (PositiveAnalyticCube.taylor (pressure ends E u v)) m) :
    ((graph ⊥ ends E).induce {i | 0 < m i}).Connected := by
  obtain ⟨⟨n,τ⟩,ha,hw⟩ := coefficient_pos_has_label
    (PositiveAnalyticCube.taylor (pressure ends E u v)) m hm
  have hn : 0 < n := by
    by_contra! hn
    have hzero : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    apply hw
    simp only [weight, PositiveAnalyticCube.taylor, _root_.smul_apply,
      iteratedFDeriv_zero_apply, pressure_zero ends E u v hv, smul_zero]
  have hc := taylor_coordinate_connected hn τ ends E u v hv hw
  have hset : {i | 0 < m i} = Set.range τ := by
    ext i
    rw [← ha]
    exact multiplicity_pos ⟨n,τ⟩ i
  rwa [hset]

 

theorem positive_site_pressure (ends : I → V × V) (E : Finset I)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (v : I → ℝ)
    (hv : ∀ e ∈ E, 0 ≤ v e) :
    ∃ (c : (V → ℕ) → ℝ) (r : ℝ),
      1 < r ∧ c 0 = 0 ∧ (∀ m, 0 ≤ c m) ∧
      (∀ m, 0 < c m → ((graph ⊥ ends E).induce {i | 0 < m i}).Connected) ∧
      (∀ x : V → ℂ, (∀ i, ‖x i‖ < r) →
        Summable (fun m : V → ℕ => ‖(c m : ℂ) * ∏ i, x i ^ m i‖) ∧
        Complex.exp (-(∑' m : V → ℕ, (c m : ℂ) * ∏ i, x i ^ m i)) =
          complexSitePolynomial ends E (q - 1) v x) ∧
      (∀ x : V → ℝ, (∀ i, x i ∈ Set.Icc 0 1) →
        HasSum (fun m : V → ℕ => c m * ∏ i, x i ^ m i)
          (-Real.log (percolationSitePolynomial ends E (q - 1) v x))) := by
  let u := 1 - q
  have hu : 0 < u := sub_pos.mpr hq1
  have hu1 : u < 1 := by dsimp [u]; linarith
  have huq : -u = q - 1 := by dsimp [u]; ring
  let p := PositiveAnalyticCube.taylor (pressure ends E u v)
  have hp := pressure_expansion ends E hu hu1 v hv
  have hn : ∀ a : Labels V, 0 ≤ weight p a := fun a => hp.2.1 a.1 a.2
  obtain ⟨r,hr1,hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.1
  have hr : 1 < (r : ℝ) := by exact_mod_cast hr1
  have hR : ENNReal.ofReal (r : ℝ) < p.radius := by simpa only [ENNReal.ofReal_coe_nnreal] using hrR
  refine ⟨coefficient p,r,hr,?_,coefficient_nonneg p hn,?_,?_,?_⟩
  · apply coefficient_zero
    ext w
    simp only [p, PositiveAnalyticCube.taylor, _root_.smul_apply,
      iteratedFDeriv_zero_apply, pressure_zero ends E u v hv, smul_zero, _root_.zero_apply]
  · exact pressure_coefficient_connected ends E u v hv
  · intro x hx
    have hs := complexify_hasSum p hn (zero_lt_one.trans hr) hR x hx
    refine ⟨hs.summable.norm, ?_⟩
    rw [hs.tsum_eq]
    simpa only [huq] using complex_pressure_exponential ends E hu hu1 v hv hr hR x hx
  · intro x hx
    have hcx : ∀ i, ‖(x i : ℂ)‖ < (r : ℝ) := fun i => by
      rw [Complex.norm_real, Real.norm_of_nonneg (hx i).1]
      exact (hx i).2.trans_lt hr
    have hs := complexify_hasSum p hn (zero_lt_one.trans hr) hR (fun i => (x i : ℂ)) hcx
    have hsum : p.sum x = pressure ends E u v x := (hp.2.2 x hx).tsum_eq
    rw [complexify_sum_real, hsum] at hs
    apply Complex.hasSum_ofReal.mp
    simpa only [pressure, huq, Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_pow] using hs

end BelowOne.FKPressure

end

end OAI
