import Mathlib
import OAI.Probability.SKRatio.Entropy.Entropy
import OAI.Probability.SKRatio.Gaussian.HammingGeometry

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter ContinuousLinearMap
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

lemma semigroup_small_set_of_mgf {n : ℕ} (J : Interaction n) (B : Set (Spin n))
    (f : Observables n) {d C a : ℝ} (hd : 0 ≤ d)
    (hf : ∀ y ∈ B, f y = 0)
    (hmean : ∀ x, a ≤ semigroup J d f x)
    (hmgf : ∀ x, semigroup J d (fun y => Real.exp (-(f y-semigroup J d f x))) x ≤
      Real.exp C) (x : Spin n) :
    semigroup J d (fun y => if y ∈ B then 1 else 0) x ≤ Real.exp (C-a) := by
  have hp (y : Spin n) : Real.exp a*(if y ∈ B then 1 else 0) ≤
      Real.exp (-(f y-semigroup J d f x)) := by
    by_cases hy : y ∈ B
    · simp only [hy,↓reduceIte,mul_one,hf y hy,zero_sub,neg_neg]
      exact Real.exp_le_exp.mpr (hmean x)
    · simp only [hy,↓reduceIte,mul_zero]
      exact Real.exp_nonneg _
  have h := semigroup_mono J hd _ _ hp x
  change semigroup J d (Real.exp a • (fun y => if y ∈ B then 1 else 0)) x ≤ _ at h
  rw [map_smul] at h
  change Real.exp a*semigroup J d (fun y => if y ∈ B then 1 else 0) x ≤ _ at h
  have hm := mul_le_mul_of_nonneg_left (h.trans (hmgf x)) (Real.exp_nonneg (-a))
  simpa only [← mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul,
    show -a+C=C-a by ring] using hm

lemma bad_avoidance_burnin {n : ℕ} (hn : 0 < n) (g : Disorder n)
    (B : Set (Spin n)) {d A κ δ : ℝ} (hd : 0 ≤ d) (hA : 0 ≤ A)
    (hκ : 0 < κ) (hδ : 0 ≤ δ)
    (hsmall : FiniteLaw.mean (mass g 0)
      (fun y => if y ∈ hammingNeighborhood B δ then 1 else 0) ≤ Real.exp (-(κ/2*n)))
    (hentropy : ∀ x, transitionEntropy g x d ≤ κ*n/8)
    (hsize : Real.log 2 ≤ κ*n/8)
    (hdrift : ∀ f : Observables n, ∀ r ∈ Set.Icc (0:ℝ) d, ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          A*unweightedGradient (semigroup (coupling g) r f) y) (x : Spin n) :
    let Q := Real.exp (A*d)/4
    semigroup (coupling g) d (fun y => if y ∈ B then 1 else 0) x ≤
      Real.exp (2*Real.exp (2*Real.sqrt Q)*(d*Q)-δ*Real.sqrt n/2) := by
  dsimp only
  by_cases hB : B.Nonempty
  · have hhalf (x : Spin n) : FiniteLaw.mean (continuousKernel (coupling g) d x)
        (fun y => if y ∈ hammingNeighborhood B δ then 1 else 0) ≤ 1/2 := by
      have h := FiniteLaw.event_entropy_bound (continuousKernel (coupling g) d x) (mass g 0)
        (hammingNeighborhood B δ) (continuousKernel_nonneg (coupling g) d hd x)
        (mass_pos g 0) (continuousKernel_sum _ d x) (sum_mass g 0) hsmall
      change (κ/2*n)*FiniteLaw.mean _ _ ≤ transitionEntropy g x d+Real.log 2 at h
      have hkn : 0 < κ*(n:ℝ) := mul_pos hκ (Nat.cast_pos.mpr hn)
      nlinarith only [h,hentropy x,hsize,hkn]
    have hmean (x : Spin n) : δ*Real.sqrt n/2 ≤
        semigroup (coupling g) d (distanceObservable B) x := by
      rw [semigroup_eq_kernel]
      exact distanceObservable_mean_lower hn B hB _
        (continuousKernel_nonneg _ d hd x) (continuousKernel_sum _ d x) hδ (hhalf x)
    have henv (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) d) (y : Spin n) :
        unweightedGradient (semigroup (coupling g) r (distanceObservable B)) y ≤
          Real.exp (A*d)/4 := by
      calc
        _ ≤ Real.exp (A*r)*(1/4) := gradient_envelope_of_drift (coupling g) _ hr.1
          (fun v hv => hdrift _ v ⟨hv.1,hv.2.trans hr.2⟩) (unweightedGradient_distanceObservable hn B hB) y
        _ ≤ _ := by
          simpa only [mul_one_div] using mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr.2 hA)) (by norm_num : (0:ℝ)≤1/4)
    apply semigroup_small_set_of_mgf (coupling g) B (distanceObservable B) hd
      (distanceObservable_zero B) hmean _ x
    intro z
    have h := semigroup_jump_mgf (coupling g) (distanceObservable B) d hd
      (fun _ => Real.exp (A*d)/4) (Real.exp (A*d)/4) (-1) intervalIntegrable_const
      (fun _ _ => le_rfl) henv z
    simpa only [neg_one_mul,neg_sq,one_pow,mul_one,abs_neg,abs_one,
      intervalIntegral.integral_const,sub_zero,smul_eq_mul] using h
  · have he : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
    simpa only [he,Set.mem_empty_iff_false,↓reduceIte,semigroup_const] using
      (Real.exp_nonneg (2*Real.exp (2*Real.sqrt (Real.exp (A*d)/4))*(d*(Real.exp (A*d)/4))-
        δ*Real.sqrt n/2))

lemma semigroup_event_bound_later {n : ℕ} (J : Interaction n) (B : Set (Spin n))
    {d q : ℝ} (hB : ∀ x, semigroup J d (fun y => if y ∈ B then 1 else 0) x ≤ q)
    {u : ℝ} (hu : d ≤ u) (x : Spin n) :
    semigroup J u (fun y => if y ∈ B then 1 else 0) x ≤ q := by
  have h := semigroup_le_const J (u-d) (sub_nonneg.mpr hu) hB x
  rwa [← mul_apply_eq_comp,← semigroup_add,sub_add_cancel] at h

lemma stretched_exp_le_dimensionDecay {c m : ℝ} (hc : 0 < c) (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-c*Real.sqrt n) ≤ dimensionDecay m n := by
  have hlim : Tendsto (fun n : ℕ => Real.log n/Real.sqrt n) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (r := (1/2:ℝ)) (by norm_num)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def,← Real.sqrt_eq_rpow] using h
  filter_upwards [hlim.eventually (gt_mem_nhds (div_pos hc hm)),eventually_gt_atTop 0]
    with n hn hn0
  have hs := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn0 : 0 < (n:ℝ))
  have h := (div_lt_iff₀ hs).mp hn
  apply Real.exp_le_exp.mpr
  have hh := mul_lt_mul_of_pos_left h hm
  have hcan : m*(c/m*Real.sqrt n) = c*Real.sqrt n := by field_simp
  rw [hcan] at hh
  linarith only [hh]

theorem uniform_bad_avoidance
    (G : ∀ n : ℕ, Set (Disorder n))
    (bad : ∀ n, Disorder n → Set (Spin n)) {κ A χ K : ℝ}
    (hκ : 0 < κ) (hA : 0 ≤ A) (hχ : 0 < χ) (hK : 0 ≤ K)
    (hnorm : ∀ n, ∀ g ∈ G n, euclideanOpNorm (coupling g) ≤ K)
    (hmlsi : ∀ n, ∀ g ∈ G n, ∀ F : Observables n,
      (∀ y, 0 < F y) → FiniteLaw.mean (mass g 0) F = 1 →
      χ*FiniteLaw.entropy (mass g 0) F ≤
        -stationaryInner g (generator (coupling g) F) (fun y => Real.log (F y)))
    (hsmall : ∀ n, ∀ g ∈ G n, FiniteLaw.mean (mass g 0)
      (fun y => if y ∈ bad n g then 1 else 0) ≤ Real.exp (-κ*n))
    (hdrift : ∀ n, ∀ g ∈ G n, ∀ f : Observables n, ∀ r : ℝ, 0 ≤ r → ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          (-κ + if y ∈ bad n g then A else 0)*
            unweightedGradient (semigroup (coupling g) r f) y) :
    ∃ d c : ℝ, 0 < d ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      ∀ u : ℝ, d ≤ u → ∀ x, semigroup (coupling g) u
        (fun y => if y ∈ bad n g then 1 else 0) x ≤ Real.exp (-c*Real.sqrt n) := by
  obtain ⟨δ,ρ,hδ,hδhalf,hρ,hδρ⟩ := exists_small_hamming_radius (K := K) hκ
  have he : Tendsto (fun t : ℝ => Real.exp (-χ*t)*(Real.log 2+K)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 χ hχ).mul_const (Real.log 2+K)
    simpa only [Real.rpow_zero,one_mul,zero_mul] using h
  obtain ⟨d,hd,hE⟩ := ((eventually_gt_atTop (0:ℝ)).and
    (he.eventually (gt_mem_nhds (by positivity : (0:ℝ)<κ/8)))).exists
  let Q := Real.exp (A*d)/4
  let C := 2*Real.exp (2*Real.sqrt Q)*(d*Q)
  have hsize : ∀ᶠ n : ℕ in atTop, Real.log 2 ≤ κ*(n:ℝ)/8 := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by positivity : (0:ℝ)<κ/8)
    simpa only [div_mul_eq_mul_div] using h.eventually_ge_atTop (Real.log 2)
  have hC : ∀ᶠ n : ℕ in atTop, C ≤ δ*Real.sqrt n/4 := by
    have h := (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop
      (by positivity : (0:ℝ)<δ/4)
    simpa only [Function.comp_def,div_mul_eq_mul_div] using h.eventually_ge_atTop C
  refine ⟨d,δ/4,hd,by positivity,?_⟩
  filter_upwards [hsize,hC,eventually_gt_atTop 0] with n hnsize hnC hn
  intro g hg u hu x
  apply semigroup_event_bound_later (coupling g) (bad n g) (d := d) (q := Real.exp (-(δ/4)*Real.sqrt n)) _ hu x
  intro z
  have hneigh : FiniteLaw.mean (mass g 0)
      (fun y => if y ∈ hammingNeighborhood (bad n g) δ then 1 else 0) ≤ Real.exp (-(κ/2*n)) := by
    apply (gibbs_hamming_neighborhood g (bad n g) hK hδ.le hρ (hnorm n g hg) (hsmall n g hg)).trans
    apply Real.exp_le_exp.mpr
    have hcoeff : -κ+2*K*Real.sqrt δ+ρ*δ+Real.log (1+Real.exp (-ρ)) ≤ -(κ/2) := by
      linarith only [hδρ]
    simpa only [neg_mul] using mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg n)
  have hent (y : Spin n) : transitionEntropy g y d ≤ κ*n/8 := by
    calc
      _ ≤ Real.exp (-χ*d)*Real.log (1/mass g 0 y) := transitionEntropy_decay g (hmlsi n g hg) y hd.le
      _ ≤ Real.exp (-χ*d)*((n:ℝ)*(Real.log 2+K)) := mul_le_mul_of_nonneg_left
        ((log_inverse_mass_le g y).trans (mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (hnorm n g hg)) (Nat.cast_nonneg n))) (Real.exp_nonneg _)
      _ = (Real.exp (-χ*d)*(Real.log 2+K))*(n:ℝ) := by ring
      _ ≤ _ := by simpa only [div_mul_eq_mul_div] using
        mul_le_mul_of_nonneg_right hE.le (Nat.cast_nonneg n)
  have hrough (f : Observables n) (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) d) (y : Spin n) :
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          A*unweightedGradient (semigroup (coupling g) r f) y := by
    apply (hdrift n g hg f r hr.1 y).trans
    apply mul_le_mul_of_nonneg_right _ (unweightedGradient_nonneg _ _)
    split_ifs <;> linarith only [hκ,hA]
  have h := bad_avoidance_burnin hn g (bad n g) hd.le hA hκ hδ.le hneigh hent hnsize hrough z
  apply h.trans (Real.exp_le_exp.mpr ?_)
  change C-δ*Real.sqrt n/2 ≤ _
  linarith only [hnC]

theorem superpolynomial_bad_avoidance
    (G : ∀ n : ℕ, Set (Disorder n))
    (bad : ∀ n, Disorder n → Set (Spin n)) {d c : ℝ} (hc : 0 < c)
    (havoid : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ u : ℝ, d ≤ u → ∀ x,
      semigroup (coupling g) u (fun y => if y ∈ bad n g then 1 else 0) x ≤ Real.exp (-c*Real.sqrt n)) :
    ∀ D m : ℝ, 0 < D → 0 < m → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      ∀ u ∈ Set.Icc d (D*Real.log n), ∀ x, semigroup (coupling g) u
        (fun y => if y ∈ bad n g then 1 else 0) x ≤ dimensionDecay m n := by
  intro D m _ hm
  filter_upwards [havoid,stretched_exp_le_dimensionDecay hc hm] with n hn hnexp
  intro g hg u hu x
  exact (hn g hg u hu.1 x).trans hnexp

end SKRatio.Calculus

end
end

end OAI
