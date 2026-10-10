import OAI.Probability.InvariantIsing.Core.FiniteVariationalBounds

namespace OAI

/-! Continuity under changes of the positive masses of a fixed finite spectral
alphabet. The inverse is compared using its defining resolvent equation. -/

noncomputable section
open Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem finiteResolvent_tendsto_weights (ρs : ℕ → ι → ℝ) (ρ eig : ι → ℝ)
    (hρs : Tendsto ρs atTop (𝓝 ρ)) (b : ℝ) :
    Tendsto (fun k => finiteResolvent (ρs k) eig b) atTop (𝓝 (finiteResolvent ρ eig b)) := by
  exact tendsto_finsetSum Finset.univ (fun a _ =>
    ((tendsto_pi_nhds.mp hρs) a).div_const (b - eig a))

theorem finiteInverse_tendsto_weights (ρs : ℕ → ι → ℝ) (ρ eig : ι → ℝ)
    (hspos : ∀ k a, 0 < ρs k a) (hssum : ∀ k, ∑ a, ρs k a = 1)
    (hpos : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (hρs : Tendsto ρs atTop (𝓝 ρ))
    (xs : ℕ → ℝ) {x : ℝ} (hxs : Tendsto xs atTop (𝓝 x)) (hx : 0 < x) :
    Tendsto (fun k => finiteInverse (ρs k) eig (hspos k) (hssum k) (xs k))
      atTop (𝓝 (finiteInverse ρ eig hpos hsum x)) := by
  have hs := finiteInverse_spec ρ eig hpos hsum hx
  have hxp : ∀ᶠ k in atTop, 0 < xs k := hxs.eventually (Ioi_mem_nhds hx)
  apply tendsto_order.2
  constructor
  · intro l hl
    by_cases he : ∀ a, eig a < l
    · have hR : x < finiteResolvent ρ eig l := by
        rw [← hs.2]
        exact finiteResolvent_strictAnti (fun a => (hpos a).le) hsum he hl
      have ht := hxs.eventually_lt (finiteResolvent_tendsto_weights ρs ρ eig hρs l) hR
      filter_upwards [hxp, ht] with k hk hlt
      have hsk := finiteInverse_spec (ρs k) eig (hspos k) (hssum k) hk
      by_contra hnot
      rcases (le_of_not_gt hnot).eq_or_lt with h | h
      · rw [← h, hsk.2] at hlt
        exact (lt_irrefl _ hlt)
      · have hc := finiteResolvent_strictAnti (fun a => (hspos k a).le)
          (hssum k) hsk.1 h
        rw [hsk.2] at hc
        exact (not_lt_of_ge hc.le hlt)
    · push Not at he
      obtain ⟨a, ha⟩ := he
      filter_upwards [hxp] with k hk
      exact ha.trans_lt ((finiteInverse_spec (ρs k) eig (hspos k) (hssum k) hk).1 a)
  · intro u hu
    have he : ∀ a, eig a < u := fun a => (hs.1 a).trans hu
    have hR : finiteResolvent ρ eig u < x := by
      rw [← hs.2]
      exact finiteResolvent_strictAnti (fun a => (hpos a).le) hsum hs.1 hu
    have ht := (finiteResolvent_tendsto_weights ρs ρ eig hρs u).eventually_lt hxs hR
    filter_upwards [hxp, ht] with k hk hlt
    have hsk := finiteInverse_spec (ρs k) eig (hspos k) (hssum k) hk
    by_contra hnot
    rcases (le_of_not_gt hnot).eq_or_lt with h | h
    · rw [h, hsk.2] at hlt
      exact (lt_irrefl _ hlt)
    · have hc := finiteResolvent_strictAnti (fun a => (hspos k a).le) (hssum k) he h
      rw [hsk.2] at hc
      exact (not_lt_of_ge hc.le hlt)

theorem finiteR_tendsto_weights_pos (ρs : ℕ → ι → ℝ) (ρ eig : ι → ℝ)
    (hspos : ∀ k a, 0 < ρs k a) (hssum : ∀ k, ∑ a, ρs k a = 1)
    (hpos : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (hρs : Tendsto ρs atTop (𝓝 ρ))
    (xs : ℕ → ℝ) {x : ℝ} (hxs : Tendsto xs atTop (𝓝 x)) (hx : 0 < x) :
    Tendsto (fun k => finiteR (ρs k) eig (hspos k) (hssum k) (xs k))
      atTop (𝓝 (finiteR ρ eig hpos hsum x)) := by
  have hb := finiteInverse_tendsto_weights ρs ρ eig hspos hssum hpos hsum hρs xs hxs hx
  have hi : Tendsto (fun k => 1 / xs k) atTop (𝓝 (1 / x)) :=
    tendsto_const_nhds.div hxs hx.ne'
  have he : (fun k => finiteR (ρs k) eig (hspos k) (hssum k) (xs k)) =ᶠ[atTop]
      (fun k => finiteInverse (ρs k) eig (hspos k) (hssum k) (xs k) - 1 / xs k) := by
    filter_upwards [hxs.eventually (Ioi_mem_nhds hx)] with k hk
    simp only [finiteR, ite_eq_left hk]
  have hl : Tendsto
      (fun k => finiteInverse (ρs k) eig (hspos k) (hssum k) (xs k) - 1 / xs k)
      atTop (𝓝 (finiteR ρ eig hpos hsum x)) := by
    simpa only [finiteR, ite_eq_left hx] using hb.sub hi
  exact hl.congr' he.symm

theorem finiteR_tendsto_weights_zero (ρs : ℕ → ι → ℝ) (ρ eig : ι → ℝ)
    (hspos : ∀ k a, 0 < ρs k a) (hssum : ∀ k, ∑ a, ρs k a = 1)
    (hpos : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (hρs : Tendsto ρs atTop (𝓝 ρ))
    (xs : ℕ → ℝ) (hxs : Tendsto xs atTop (𝓝 0)) :
    Tendsto (fun k => finiteR (ρs k) eig (hspos k) (hssum k) (xs k))
      atTop (𝓝 (finiteR ρ eig hpos hsum 0)) := by
  let K := 1 + ∑ a, |eig a|
  have hK : 0 < K := by
    have := Finset.sum_nonneg (s := Finset.univ) (fun a _ => abs_nonneg (eig a))
    dsimp only [K]
    linarith
  have heig a : |eig a| ≤ K := by
    have := Finset.single_le_sum (f := fun a => |eig a|)
      (fun a _ => abs_nonneg (eig a)) (Finset.mem_univ a)
    dsimp only [K]
    linarith
  have hsmall : ∀ᶠ k in atTop, xs k < 1 / (4 * K) :=
    hxs.eventually (Iio_mem_nhds (by positivity))
  have herr : ∀ᶠ k in atTop,
      ‖finiteR (ρs k) eig (hspos k) (hssum k) (xs k) - ∑ a, ρs k a * eig a‖ ≤
        8 * K ^ 2 * |xs k| := by
    filter_upwards [hsmall] with k hk
    rw [Real.norm_eq_abs]
    by_cases hxk : 0 < xs k
    · rw [abs_of_nonneg (sub_nonneg.mpr (mean_le_finiteR (ρs k) eig
        (hspos k) (hssum k) hxk)), abs_of_pos hxk]
      apply finiteR_sub_mean_le (ρs k) eig (hspos k) (hssum k) hK.le heig hxk
      have := (lt_div_iff₀ (show 0 < 4 * K by positivity)).mp hk
      nlinarith
    · simp only [finiteR, ite_eq_right hxk, sub_self, abs_zero]
      positivity
  have hb : Tendsto (fun k => 8 * K ^ 2 * |xs k|) atTop (𝓝 0) := by
    simpa using hxs.abs.const_mul (8 * K ^ 2)
  have hz := squeeze_zero_norm' herr hb
  have hm : Tendsto (fun k => ∑ a, ρs k a * eig a) atTop (𝓝 (∑ a, ρ a * eig a)) :=
    tendsto_finsetSum Finset.univ (fun a _ => ((tendsto_pi_nhds.mp hρs) a).mul_const _)
  simpa only [sub_add_cancel, zero_add, finiteR, lt_self_iff_false, ite_false] using hz.add hm

theorem finiteR_tendsto_weights_nonneg (ρs : ℕ → ι → ℝ) (ρ eig : ι → ℝ)
    (hspos : ∀ k a, 0 < ρs k a) (hssum : ∀ k, ∑ a, ρs k a = 1)
    (hpos : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (hρs : Tendsto ρs atTop (𝓝 ρ))
    (xs : ℕ → ℝ) {x : ℝ} (hxs : Tendsto xs atTop (𝓝 x)) (hx : 0 ≤ x) :
    Tendsto (fun k => finiteR (ρs k) eig (hspos k) (hssum k) (xs k))
      atTop (𝓝 (finiteR ρ eig hpos hsum x)) := by
  rcases hx.eq_or_lt with hx | hx
  · subst x
    exact finiteR_tendsto_weights_zero ρs ρ eig hspos hssum hpos hsum hρs xs hxs
  · exact finiteR_tendsto_weights_pos ρs ρ eig hspos hssum hpos hsum hρs xs hxs hx

/-- Uniformity on the whole interval includes the transform's value at zero. -/
theorem finiteR_uniform_weights (ρs : ℕ → ι → ℝ) (ρ eig : ι → ℝ)
    (hspos : ∀ k a, 0 < ρs k a) (hssum : ∀ k, ∑ a, ρs k a = 1)
    (hpos : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (hρs : Tendsto ρs atTop (𝓝 ρ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ Icc (0 : ℝ) 1,
      |finiteR (ρs k) eig (hspos k) (hssum k) x - finiteR ρ eig hpos hsum x| < ε := by
  classical
  intro ε hε
  by_contra hbad
  have hbad' : ∃ᶠ k in atTop, ∃ x ∈ Icc (0 : ℝ) 1,
      ε ≤ |finiteR (ρs k) eig (hspos k) (hssum k) x - finiteR ρ eig hpos hsum x| := by
    simpa only [Filter.not_eventually, not_forall, not_imp, not_lt, exists_prop] using hbad
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hbad'
  choose xs hxs herror using hφbad
  obtain ⟨x, hx, ψ, hψ, hlim⟩ := isCompact_Icc.tendsto_subseq hxs
  have hweights := hρs.comp (hφ.comp hψ).tendsto_atTop
  have hR := finiteR_tendsto_weights_nonneg
    (fun k => ρs (φ (ψ k))) ρ eig (fun k => hspos (φ (ψ k)))
    (fun k => hssum (φ (ψ k))) hpos hsum hweights (fun k => xs (ψ k)) hlim hx.1
  have hfixed := (continuous_finiteR ρ eig hpos hsum).continuousAt.tendsto.comp hlim
  have hdiff := (hR.sub hfixed).abs
  have hzero : Tendsto (fun k =>
      |finiteR (ρs (φ (ψ k))) eig (hspos (φ (ψ k))) (hssum (φ (ψ k))) (xs (ψ k)) -
        finiteR ρ eig hpos hsum (xs (ψ k))|) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self, abs_zero] using hdiff
  have hsmall : ∀ᶠ k in atTop,
      |finiteR (ρs (φ (ψ k))) eig (hspos (φ (ψ k))) (hssum (φ (ψ k))) (xs (ψ k)) -
        finiteR ρ eig hpos hsum (xs (ψ k))| < ε := by
    exact hzero.eventually (Iio_mem_nhds hε)
  obtain ⟨k, hk⟩ := hsmall.exists
  exact (not_le_of_gt hk) (herror (ψ k))

theorem finiteVariational_tendsto_weights (ρs : ℕ → ι → ℝ) (ρ eig : ι → ℝ)
    (hspos : ∀ k a, 0 < ρs k a) (hssum : ∀ k, ∑ a, ρs k a = 1)
    (hpos : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (hρs : Tendsto ρs atTop (𝓝 ρ)) :
    Tendsto (fun k => (variationalFunctional (finiteR (ρs k) eig (hspos k) (hssum k))).toReal)
      atTop (𝓝 (variationalFunctional (finiteR ρ eig hpos hsum)).toReal) := by
  have hf := finiteVariational_ne_top_bot ρ eig hpos hsum
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [finiteR_uniform_weights ρs ρ eig hspos hssum hpos hsum hρs ε hε] with k hk
  have hfk := finiteVariational_ne_top_bot (ρs k) eig (hspos k) (hssum k)
  have hleft := variationalFunctional_le_add (finiteR (ρs k) eig (hspos k) (hssum k))
    (finiteR ρ eig hpos hsum) (continuous_finiteR (ρs k) eig (hspos k) (hssum k))
    (continuous_finiteR ρ eig hpos hsum) ε (fun x hx => (hk x hx).le)
  have hright := variationalFunctional_le_add (finiteR ρ eig hpos hsum)
    (finiteR (ρs k) eig (hspos k) (hssum k)) (continuous_finiteR ρ eig hpos hsum)
    (continuous_finiteR (ρs k) eig (hspos k) (hssum k)) ε
    (fun x hx => by simpa only [abs_sub_comm] using (hk x hx).le)
  rw [← EReal.coe_toReal hfk.1 hfk.2, ← EReal.coe_toReal hf.1 hf.2,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at hleft hright
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end InvariantIsing

end

end OAI
