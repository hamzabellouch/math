import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Lattice.InitialWeights
import OAI.AlgebraicGeometry.Seshadri.Interpolation.CompressionRanks
import OAI.AlgebraicGeometry.Seshadri.Interpolation.ConvergentSeries

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
open scoped BigOperators Topology
open Filter Set
noncomputable def exponentWeight (t : ℝ) (p : Exponent) : ℝ := p.1 + t * p.2

def StrictInitial (c : Exponent → ℂ) (t : ℝ) (e : Exponent) : Prop :=
  c e ≠ 0 ∧ ∀ p, c p ≠ 0 → p ≠ e → exponentWeight t e < exponentWeight t p

noncomputable def rescaleCoeff (c : Exponent → ℂ) (t : ℝ) (e : Exponent)
    (s : ℝ) (p : Exponent) : ℂ :=
  c p * ((s ^ (exponentWeight t p - exponentWeight t e) : ℝ) : ℂ)

lemma norm_rescaleCoeff_mono (c : Exponent → ℂ) (t : ℝ) (e : Exponent)
    (he : StrictInitial c t e) (s s₀ : ℝ) (hs : 0 ≤ s) (hss : s ≤ s₀) (p : Exponent) :
    ‖rescaleCoeff c t e s p‖ ≤ ‖rescaleCoeff c t e s₀ p‖ := by
  by_cases hp : c p = 0
  · simp [rescaleCoeff, hp]
  have hw : 0 ≤ exponentWeight t p - exponentWeight t e := by
    by_cases hpe : p = e
    · simp [hpe]
    · exact (sub_pos.mpr (he.2 p hp hpe)).le
  simp only [rescaleCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hs _), abs_of_nonneg (Real.rpow_nonneg (hs.trans hss) _)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs hss hw) (norm_nonneg _)

lemma rescaleCoeff_eq_scaled (c : Exponent → ℂ) (t : ℝ) (e : Exponent)
    (s : ℝ) (hs : 0 < s) (p : Exponent) :
    rescaleCoeff c t e s p = (((s ^ exponentWeight t e)⁻¹ : ℝ) : ℂ) *
      c p * (s : ℂ) ^ p.1 * ((s ^ t : ℝ) : ℂ) ^ p.2 := by
  rw [rescaleCoeff, Real.rpow_sub hs, exponentWeight, Real.rpow_add hs,
    Real.rpow_natCast, Real.rpow_mul_natCast hs.le]
  push_cast
  ring

lemma absolute_rescaleCoeff (c : Exponent → ℂ) (t : ℝ) (e : Exponent)
    (R K s : ℝ) (hR : 0 ≤ R) (hK : 0 ≤ K) (hs : 0 < s)
    (hc : AbsolutelyConvergentAt c R) (hx : s * K ≤ R) (hz : s ^ t * K ≤ R) :
    AbsolutelyConvergentAt (rescaleCoeff c t e s) K := by
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_)
    (hc.mul_left (s ^ exponentWeight t e)⁻¹)
  rw [rescaleCoeff_eq_scaled c t e s hs, norm_mul, norm_mul, norm_mul,
    norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hs, abs_of_nonneg (Real.rpow_nonneg hs.le _),
    abs_of_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hs.le _))]
  calc
    _ = (s ^ exponentWeight t e)⁻¹ * ‖c p‖ * ((s * K) ^ p.1 * (s ^ t * K) ^ p.2) := by
      rw [pow_add, mul_pow, mul_pow]
      ring
    _ ≤ (s ^ exponentWeight t e)⁻¹ * (‖c p‖ * R ^ (p.1 + p.2)) := by
      rw [pow_add]
      calc
        _ ≤ (s ^ exponentWeight t e)⁻¹ * ‖c p‖ * (R ^ p.1 * R ^ p.2) := by
          gcongr
        _ = _ := by ring

noncomputable def initialCoeff (c : Exponent → ℂ) (e : Exponent) (p : Exponent) : ℂ :=
  if p = e then c e else 0

lemma rescaleCoeff_tendsto (c : Exponent → ℂ) (t : ℝ) (e : Exponent)
    (he : StrictInitial c t e) (p : Exponent) :
    Tendsto (fun s => rescaleCoeff c t e s p) (𝓝 (0 : ℝ)) (𝓝 (initialCoeff c e p)) := by
  by_cases hp : p = e
  · subst p
    simp [rescaleCoeff, initialCoeff]
  by_cases hc : c p = 0
  · simp [rescaleCoeff, initialCoeff, hp, hc]
  have hw := sub_pos.mpr (he.2 p hc hp)
  have hr := (Real.continuous_rpow_const hw.le).tendsto (0 : ℝ)
  rw [Real.zero_rpow hw.ne'] at hr
  simpa [rescaleCoeff, initialCoeff, hp] using
    (Complex.continuous_ofReal.continuousAt.tendsto.comp hr).const_mul (c p)

lemma seriesPartial_initialCoeff (c : Exponent → ℂ) (e : Exponent) (a b : ℕ) (x z : ℂ) :
    seriesPartial (initialCoeff c e) a b x z =
      c e * monomialDeriv e.1 a x * monomialDeriv e.2 b z := by
  unfold seriesPartial
  rw [tsum_eq_single e (fun p hp => by simp [initialCoeff, hp])]
  simp [initialCoeff]

theorem mixedDeriv_rescale_tendsto (c : Exponent → ℂ) (t : ℝ) (e : Exponent)
    (ht : 0 < t) (he : StrictInitial c t e) (hc : ConvergentSeries c)
    (a b : ℕ) (x z : ℂ) :
    Tendsto (fun s => iteratedDeriv b (fun y => iteratedDeriv a
      (fun w => seriesEval (rescaleCoeff c t e s) w y) x) z)
      (𝓝[>] (0 : ℝ)) (𝓝 (c e * monomialDeriv e.1 a x * monomialDeriv e.2 b z)) := by
  obtain ⟨R, hR, hc⟩ := hc
  let K : ℝ := max ‖x‖ ‖z‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hx : ‖x‖ < K := by dsimp [K]; linarith [le_max_left ‖x‖ ‖z‖]
  have hz : ‖z‖ < K := by dsimp [K]; linarith [le_max_right ‖x‖ ‖z‖]
  have h₁ : Tendsto (fun s : ℝ => s * (2 * K)) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 0) (𝓝 0)).mul_const (2 * K)
  have h₂ : Tendsto (fun s : ℝ => s ^ t * (2 * K)) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa [Real.zero_rpow ht.ne'] using
      ((Real.continuous_rpow_const ht.le).tendsto (0 : ℝ)).mul_const (2 * K)
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s ∧ s * (2 * K) < R ∧ s ^ t * (2 * K) < R := by
    filter_upwards [self_mem_nhdsWithin,
        ((h₁.eventually (gt_mem_nhds hR)).filter_mono nhdsWithin_le_nhds),
        ((h₂.eventually (gt_mem_nhds hR)).filter_mono nhdsWithin_le_nhds)] with s hs h1 h2
    exact ⟨hs, h1, h2⟩
  obtain ⟨s₀, hs₀, hsx, hsz⟩ := hsmall.exists
  have habs := absolute_rescaleCoeff c t e R (2 * K) s₀ hR.le (by positivity)
    hs₀ hc hsx.le hsz.le
  have hdom := derivativeSummable_of_absolute (rescaleCoeff c t e s₀) (2 * K) K
    (by positivity) hK (by linarith) habs
  have hb : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ p,
      ‖rescaleCoeff c t e s p‖ ≤ ‖rescaleCoeff c t e s₀ p‖ := by
    filter_upwards [self_mem_nhdsWithin,
      ((eventually_lt_nhds hs₀).filter_mono nhdsWithin_le_nhds)] with s hs hss p
    exact norm_rescaleCoeff_mono c t e he s s₀ hs.le hss.le p
  simpa only [seriesPartial_initialCoeff] using
    mixedDeriv_limit_of_coefficients (𝓝[>] (0 : ℝ)) (rescaleCoeff c t e)
      (initialCoeff c e) (rescaleCoeff c t e s₀) K hK hdom
      (fun p => (rescaleCoeff_tendsto c t e he p).mono_left nhdsWithin_le_nhds)
      hb a b x z hx hz

lemma seriesEval_rescale (c : Exponent → ℂ) (t : ℝ) (e : Exponent)
    (s : ℝ) (hs : 0 < s) (x z : ℂ) :
    seriesEval (rescaleCoeff c t e s) x z =
      (((s ^ exponentWeight t e)⁻¹ : ℝ) : ℂ) *
        seriesEval c ((s : ℂ) * x) (((s ^ t : ℝ) : ℂ) * z) := by
  unfold seriesEval
  rw [← tsum_mul_left]
  apply tsum_congr
  intro p
  rw [rescaleCoeff_eq_scaled c t e s hs, mul_pow, mul_pow]
  ring

lemma iteratedDeriv_dilation (f : ℂ → ℂ) (s : ℂ) (a : ℕ) :
    iteratedDeriv a (fun x => f (s * x)) = fun x => s ^ a * iteratedDeriv a f (s * x) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [deriv_const_mul_field, deriv_comp_mul_left]
    simp only [smul_eq_mul, iteratedDeriv_succ, pow_succ]
    ring

lemma mixedDeriv_dilation (f : ℂ → ℂ → ℂ) (A s t : ℂ) (a b : ℕ) (x z : ℂ) :
    iteratedDeriv b (fun y => iteratedDeriv a (fun w => A * f (s * w) (t * y)) x) z =
      A * s ^ a * t ^ b *
        iteratedDeriv b (fun y => iteratedDeriv a (fun w => f w y) (s * x)) (t * z) := by
  have ha (y : ℂ) : iteratedDeriv a (fun w => A * f (s * w) (t * y)) x =
      A * (s ^ a * iteratedDeriv a (fun w => f w (t * y)) (s * x)) := by
    rw [iteratedDeriv_const_mul_field]
    congr 1
    exact congrFun (iteratedDeriv_dilation (fun w => f w (t * y)) s a) x
  simp_rw [ha, iteratedDeriv_const_mul_field]
  rw [congrFun (iteratedDeriv_dilation
    (fun y => iteratedDeriv a (fun w => f w y) (s * x)) t b) z]
  ring

lemma mixedDeriv_rescale (c : Exponent → ℂ) (t : ℝ) (e : Exponent)
    (s : ℝ) (hs : 0 < s) (a b : ℕ) (x z : ℂ) :
    iteratedDeriv b (fun y => iteratedDeriv a
      (fun w => seriesEval (rescaleCoeff c t e s) w y) x) z =
      (((s ^ exponentWeight t e)⁻¹ : ℝ) : ℂ) * (s : ℂ) ^ a * ((s ^ t : ℝ) : ℂ) ^ b *
        iteratedDeriv b (fun y => iteratedDeriv a (fun w => seriesEval c w y)
          ((s : ℂ) * x)) (((s ^ t : ℝ) : ℂ) * z) := by
  simp_rw [seriesEval_rescale c t e s hs]
  exact mixedDeriv_dilation _ _ _ _ _ _ _ _

lemma finiteJetColumn_const_mul (r m : ℕ) (p : Fin r → ℂ × ℂ)
    (A : ℂ) (f : ℂ → ℂ → ℂ) :
    finiteJetColumn r m p (fun x z => A * f x z) = A • finiteJetColumn r m p f := by
  funext j
  simp only [finiteJetColumn, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · simp_rw [iteratedDeriv_const_mul_field]
  · simp

lemma finiteJetColumn_monomial (r m : ℕ) (p : Fin r → ℂ × ℂ)
    (e : Exponent) (j : JetIndex r m) :
    finiteJetColumn r m p (fun x z => x ^ e.1 * z ^ e.2) j =
      if j.2.1.val + j.2.2.val < m then
        monomialDeriv e.1 j.2.1 (p j.1).1 * monomialDeriv e.2 j.2.2 (p j.1).2 else 0 := by
  unfold finiteJetColumn
  simp_rw [iteratedDeriv_mul_const_field, iteratedDeriv_const_mul_field, monomialDeriv_eq]

lemma rescale_jet_limit {ι : Type*} [Finite ι] (c : ι → Exponent → ℂ)
    (e : ι → Exponent) (t : ℝ) (ht : 0 < t)
    (he : ∀ i, StrictInitial (c i) t (e i)) (hc : ∀ i, ConvergentSeries (c i))
    (r m : ℕ) (p : Fin r → ℂ × ℂ)
    (h : LinearIndependent ℂ (fun i => finiteJetColumn r m p
      (fun x z => x ^ (e i).1 * z ^ (e i).2))) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, LinearIndependent ℂ (fun i =>
      finiteJetColumn r m p (seriesEval (rescaleCoeff (c i) t (e i) s))) := by
  have hlim (i : ι) (j : JetIndex r m) :
      Tendsto (fun s => finiteJetColumn r m p
        (seriesEval (rescaleCoeff (c i) t (e i) s)) j) (𝓝[>] (0 : ℝ))
        (𝓝 (finiteJetColumn r m p
          (fun x z => c i (e i) * (x ^ (e i).1 * z ^ (e i).2)) j)) := by
    rw [finiteJetColumn_const_mul]
    simp only [Pi.smul_apply, smul_eq_mul, finiteJetColumn_monomial]
    unfold finiteJetColumn
    split_ifs with hj
    · simpa only [mul_assoc] using mixedDeriv_rescale_tendsto (c i) t (e i) ht
        (he i) (hc i) j.2.1 j.2.2 (p j.1).1 (p j.1).2
    · simp
  apply finite_jet_rank_persistence _ _ _ _ _ _ hlim
  simp_rw [finiteJetColumn_const_mul]
  simpa only [Pi.smul_def', Units.smul_def, Units.val_mk0] using
    h.units_smul (fun i => Units.mk0 (c i (e i)) (he i).1)

noncomputable def dilationJetScale (r m : ℕ) (a b : ℂ) :
    (JetIndex r m → ℂ) →ₗ[ℂ] (JetIndex r m → ℂ) :=
  LinearMap.pi fun j => (a ^ j.2.1.val * b ^ j.2.2.val) • LinearMap.proj j

lemma finiteJetColumn_rescale (r m : ℕ) (p : Fin r → ℂ × ℂ)
    (c : Exponent → ℂ) (e : Exponent) (t s : ℝ) (hs : 0 < s) :
    finiteJetColumn r m p (seriesEval (rescaleCoeff c t e s)) =
      (((s ^ exponentWeight t e)⁻¹ : ℝ) : ℂ) •
        dilationJetScale r m (s : ℂ) ((s ^ t : ℝ) : ℂ)
          (finiteJetColumn r m (fun j => ((s : ℂ) * (p j).1,
            ((s ^ t : ℝ) : ℂ) * (p j).2)) (seriesEval c)) := by
  funext j
  simp only [finiteJetColumn, Pi.smul_apply, dilationJetScale, LinearMap.pi_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  split_ifs with hj
  · rw [mixedDeriv_rescale c t e s hs]
    ring
  · simp

lemma rescale_jet_rank {ι : Type*} (c : ι → Exponent → ℂ) (e : ι → Exponent)
    (t s : ℝ) (hs : 0 < s) (r m : ℕ) (p : Fin r → ℂ × ℂ)
    (h : LinearIndependent ℂ (fun i => finiteJetColumn r m p
      (seriesEval (rescaleCoeff (c i) t (e i) s)))) :
    LinearIndependent ℂ (fun i => finiteJetColumn r m
      (fun j => ((s : ℂ) * (p j).1, ((s ^ t : ℝ) : ℂ) * (p j).2)) (seriesEval (c i))) := by
  let A : ι → ℂˣ := fun i => Units.mk0 (((s ^ exponentWeight t (e i))⁻¹ : ℝ) : ℂ)
    (by exact_mod_cast inv_ne_zero (Real.rpow_pos_of_pos hs _).ne')
  simp_rw [finiteJetColumn_rescale r m p _ _ t s hs] at h
  apply LinearIndependent.of_comp (dilationJetScale r m (s : ℂ) ((s ^ t : ℝ) : ℂ))
  exact (LinearIndependent.units_smul_iff _ A).mp h

theorem initial_monomial_jet_transfer_strict {ι : Type*} [Finite ι]
    (c : ι → Exponent → ℂ) (e : ι → Exponent) (t : ℝ) (ht : 0 < t)
    (he : ∀ i, StrictInitial (c i) t (e i)) (hc : ∀ i, ConvergentSeries (c i))
    (r m : ℕ) (p : Fin r → ℂ × ℂ) (hp : Function.Injective p)
    (h : LinearIndependent ℂ (fun i => finiteJetColumn r m p
      (fun x z => x ^ (e i).1 * z ^ (e i).2))) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : Fin r → ℂ × ℂ, Function.Injective q ∧
      (∀ j, ‖(q j).1‖ < ε ∧ ‖(q j).2‖ < ε) ∧
      LinearIndependent ℂ (fun i => finiteJetColumn r m q (seriesEval (c i))) := by
  have hl := rescale_jet_limit c e t ht he hc r m p h
  have hx (j : Fin r) : Tendsto (fun s : ℝ => (s : ℂ) * (p j).1)
      (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa using (Complex.continuous_ofReal.tendsto (0 : ℝ)).mul_const (p j).1
  have hz (j : Fin r) : Tendsto (fun s : ℝ => ((s ^ t : ℝ) : ℂ) * (p j).2)
      (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hr := (Real.continuous_rpow_const ht.le).tendsto (0 : ℝ)
    simpa [Real.zero_rpow ht.ne'] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hr).mul_const (p j).2
  have hnear : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ j : Fin r,
      ‖(s : ℂ) * (p j).1‖ < ε ∧ ‖((s ^ t : ℝ) : ℂ) * (p j).2‖ < ε := by
    apply Filter.eventually_all.mpr
    intro j
    filter_upwards [(((hx j).norm.eventually
      (by simpa using gt_mem_nhds hε)).filter_mono nhdsWithin_le_nhds),
      (((hz j).norm.eventually (by simpa using gt_mem_nhds hε)).filter_mono
        nhdsWithin_le_nhds)] with s hs ht
    exact ⟨hs, ht⟩
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  obtain ⟨s, hs, hli, hn⟩ := (hpos.and (hl.and hnear)).exists
  refine ⟨fun j => ((s : ℂ) * (p j).1, ((s ^ t : ℝ) : ℂ) * (p j).2), ?_, hn,
    rescale_jet_rank c e t s hs r m p hli⟩
  intro i j hij
  apply hp
  apply Prod.ext
  · exact mul_left_cancel₀ (by exact_mod_cast hs.ne') (congrArg Prod.fst hij)
  · exact mul_left_cancel₀ (by exact_mod_cast (Real.rpow_pos_of_pos hs t).ne')
      (congrArg Prod.snd hij)


end MaximalSeshadri.Interpolation
end

end OAI
