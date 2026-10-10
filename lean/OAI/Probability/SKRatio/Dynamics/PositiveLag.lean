import Mathlib
import OAI.Probability.SKRatio.Dynamics.Propagation

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

def dimensionDecay (a : ℝ) (n : ℕ) : ℝ := Real.exp (-a * Real.log n)

lemma dimensionDecay_pos (a : ℝ) (n : ℕ) : 0 < dimensionDecay a n :=
  Real.exp_pos _

lemma dimensionDecay_tendsto_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (dimensionDecay a) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 a ha).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  unfold dimensionDecay
  simpa only [Function.comp_def, Real.rpow_zero, one_mul] using h

lemma log_pow_mul_dimensionDecay_tendsto_zero (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => (Real.log n)^k * dimensionDecay a n) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) a ha).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  simpa only [Function.comp_def, Real.rpow_natCast, dimensionDecay] using h

lemma nat_mul_dimensionDecay {n : ℕ} (hn : 0 < n) (a : ℝ) :
    (n : ℝ) * dimensionDecay a n = dimensionDecay (a - 1) n := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  calc
    _ = Real.exp (Real.log n) * Real.exp (-a * Real.log n) := by
      rw [Real.exp_log hn']; rfl
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

def logarithmicVarianceBound (κ A d₀ D α : ℝ) (n : ℕ) : ℝ :=
  (4*D*Real.exp (A*d₀)/α) * dimensionDecay (κ*α/4) n +
    (4*A*D^2*Real.exp (A*d₀)) * ((Real.log n)^2 * dimensionDecay 3 n) +
    (4*D*Real.exp (A*d₀)) * (Real.log n * dimensionDecay 3 n)

lemma logarithmicVarianceBound_nonneg {κ A d₀ D α : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hα : 0 ≤ α) (hn : 1 ≤ n) :
    0 ≤ logarithmicVarianceBound κ A d₀ D α n := by
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  unfold logarithmicVarianceBound dimensionDecay
  positivity

lemma logarithmicVarianceBound_tendsto_zero {κ α : ℝ}
    (hκ : 0 < κ) (hα : 0 < α) (A d₀ D : ℝ) :
    Tendsto (logarithmicVarianceBound κ A d₀ D α) atTop (𝓝 0) := by
  have h1 := (dimensionDecay_tendsto_zero
    (a := κ*α/4) (by positivity)).const_mul (4*D*Real.exp (A*d₀)/α)
  have h2 := (log_pow_mul_dimensionDecay_tendsto_zero 2 (by norm_num : (0:ℝ)<3)).const_mul
    (4*A*D^2*Real.exp (A*d₀))
  have h3 := (log_pow_mul_dimensionDecay_tendsto_zero 1 (by norm_num : (0:ℝ)<3)).const_mul
    (4*D*Real.exp (A*d₀))
  unfold logarithmicVarianceBound
  simpa only [zero_mul, mul_zero, add_zero, pow_one] using
    (h1.add h2).add h3

def logarithmicSmoothingBound (κ A d₀ D α γ ε : ℝ) (n : ℕ) : ℝ :=
  (Real.sqrt (logarithmicVarianceBound κ A d₀ D α n) +
    dimensionDecay (γ*α) n) / (2*Real.sqrt ε)

lemma logarithmicSmoothingBound_tendsto_zero {κ α γ : ℝ}
    (hκ : 0 < κ) (hα : 0 < α) (hγ : 0 < γ) (A d₀ D ε : ℝ) :
    Tendsto (logarithmicSmoothingBound κ A d₀ D α γ ε) atTop (𝓝 0) := by
  have h := (((logarithmicVarianceBound_tendsto_zero hκ hα A d₀ D).sqrt).add
    (dimensionDecay_tendsto_zero (a := γ*α) (by positivity))).div_const (2*Real.sqrt ε)
  unfold logarithmicSmoothingBound
  simpa only [Real.sqrt_zero, zero_add, zero_div] using h

lemma logarithmic_smoothing_of_small_set_gradient {n : ℕ} (hn : 1 < n)
    (g : Disorder n) (bad : Set (Spin n)) {κ A d₀ D α γ ε t : ℝ}
    (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀) (hD : 0 ≤ D)
    (hα : 0 < α) (hε : 0 < ε) (ht : 0 ≤ t)
    (horizon : t+α*Real.log n ≤ D*Real.log n)
    (hoverlap : continuousDistance g t ≤ 1-ε)
    (hgap : ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (hdrift : ∀ (f : Observables n), ∀ r ∈ Set.Icc (0:ℝ) (D*Real.log n), ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          (-κ + if y ∈ bad then A else 0)*
            unweightedGradient (semigroup (coupling g) r f) y)
    (havoid : ∀ u ∈ Set.Icc d₀ (D*Real.log n), ∀ x,
      semigroup (coupling g) u (fun y => if y ∈ bad then 1 else 0) x ≤
        dimensionDecay (A*D+4) n)
    (hfields : ∀ z ∈ Set.Icc t (t+α*Real.log n), ∀ x, semigroup (coupling g) z
      (fun y => if ∃ i, (κ*α/8)*Real.log n < |field (coupling g) y i| then 1 else 0) x ≤
        dimensionDecay 4 n) :
    continuousDistance g (t+α*Real.log n) ≤
      logarithmicSmoothingBound κ A d₀ D α γ ε n := by
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hs : 0 < α*Real.log n := mul_pos hα hlog
  have hsne : α*Real.log n ≠ 0 := ne_of_gt hs
  have h := smoothing_of_small_set_gradient g bad
    hκ hA hd₀ ht hs horizon (dimensionDecay_pos (A*D+4) n).le
    (dimensionDecay_pos 4 n).le hε hoverlap hgap hdrift havoid hfields
  dsimp only at h
  apply h.trans
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2*Real.sqrt ε)
  have hexpγ : Real.exp (-γ*(α*Real.log n)) = dimensionDecay (γ*α) n := by
    unfold dimensionDecay; congr 1; ring
  change Real.sqrt _ + Real.exp (-γ*(α*Real.log n)) ≤
    Real.sqrt (logarithmicVarianceBound κ A d₀ D α n) + dimensionDecay (γ*α) n
  rw [hexpγ]
  apply add_le_add _ le_rfl
  apply Real.sqrt_le_sqrt
  have htD : t ≤ D*Real.log n := by linarith only [horizon, hs]
  have haexp : Real.exp (-κ*(α*Real.log n/2))*Real.exp (2*((κ*α/8)*Real.log n)) =
      dimensionDecay (κ*α/4) n := by
    rw [← Real.exp_add]; unfold dimensionDecay; congr 1; ring
  have hqexp : Real.exp (A*(D*Real.log n))*dimensionDecay (A*D+4) n =
      dimensionDecay 4 n := by
    unfold dimensionDecay; rw [← Real.exp_add]; congr 1; ring
  have hN : (n:ℝ)*dimensionDecay 4 n = dimensionDecay 3 n := by
    simpa only [show (4:ℝ)-1=3 by norm_num] using nat_mul_dimensionDecay (by omega : 0<n) 4
  have hapos : 0 ≤ 2*Real.exp (A*d₀)*dimensionDecay (κ*α/4) n/(α*Real.log n) +
      (2*(n:ℝ)*(A*Real.exp (A*d₀)*(D*Real.log n)*dimensionDecay 4 n) +
        2*Real.exp (A*d₀)*(n:ℝ)*dimensionDecay 4 n) := by
    dsimp only [dimensionDecay]; positivity
  calc
    _ = 2*t*(2*Real.exp (A*d₀)*dimensionDecay (κ*α/4) n/(α*Real.log n) +
      (2*(n:ℝ)*(A*Real.exp (A*d₀)*(D*Real.log n)*dimensionDecay 4 n) +
        2*Real.exp (A*d₀)*(n:ℝ)*dimensionDecay 4 n)) := by
          rw [mul_assoc (2*Real.exp (A*d₀)), haexp]
          rw [mul_assoc (A*Real.exp (A*d₀)*(D*Real.log n)), hqexp]
    _ ≤ 2*(D*Real.log n)*(2*Real.exp (A*d₀)*dimensionDecay (κ*α/4) n/(α*Real.log n) +
      (2*(n:ℝ)*(A*Real.exp (A*d₀)*(D*Real.log n)*dimensionDecay 4 n) +
        2*Real.exp (A*d₀)*(n:ℝ)*dimensionDecay 4 n)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htD (by norm_num)) hapos
    _ = logarithmicVarianceBound κ A d₀ D α n := by
      have hαne := ne_of_gt hα
      have hlogne := ne_of_gt hlog
      have hregroup : 2*(n:ℝ)*(A*Real.exp (A*d₀)*(D*Real.log n)*dimensionDecay 4 n) +
          2*Real.exp (A*d₀)*(n:ℝ)*dimensionDecay 4 n =
          (2*A*Real.exp (A*d₀)*D*Real.log n+2*Real.exp (A*d₀))*dimensionDecay 3 n := by
        calc
          _ = (2*A*Real.exp (A*d₀)*D*Real.log n+2*Real.exp (A*d₀))*
            ((n:ℝ)*dimensionDecay 4 n) := by ring
          _ = _ := by rw [hN]
      rw [hregroup]
      unfold logarithmicVarianceBound
      field_simp
      ring

theorem uniform_positive_lag_of_small_set_gradient
    (G : ∀ n : ℕ, Set (Disorder n))
    (bad : ∀ n, Disorder n → Set (Spin n)) {κ A d₀ γ : ℝ}
    (hκ : 0 < κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀) (hγ : 0 < γ)
    (hgap : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (hdrift : ∀ D : ℝ, 0 < D → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      ∀ (f : Observables n), ∀ r ∈ Set.Icc (0:ℝ) (D*Real.log n), ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          (-κ + if y ∈ bad n g then A else 0)*
            unweightedGradient (semigroup (coupling g) r f) y)
    (havoid : ∀ D m : ℝ, 0 < D → 0 < m →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ u ∈ Set.Icc d₀ (D*Real.log n), ∀ x,
      semigroup (coupling g) u (fun y => if y ∈ bad n g then 1 else 0) x ≤ dimensionDecay m n)
    (hfields : ∀ ε δ D m : ℝ, 0 < ε → 0 < δ → 0 < D → 0 < m →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ z ∈ Set.Icc (0:ℝ) (D*Real.log n),
      continuousDistance g z ≤ 1-ε → ∀ x, semigroup (coupling g) z
        (fun y => if ∃ i, δ*Real.log n < |field (coupling g) y i| then 1 else 0) x ≤
          dimensionDecay m n) :
    ∀ ε α D δ : ℝ, 0 < ε → 0 < α → 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ t : ℝ,
      0 ≤ t → t+α*Real.log n ≤ D*Real.log n →
      continuousDistance g t ≤ 1-ε → continuousDistance g (t+α*Real.log n) ≤ δ := by
  intro ε α D δ hε hα hδ
  let D' := max 1 D
  have hD : 0 < D' := lt_of_lt_of_le (by norm_num) (le_max_left 1 D)
  have hm : 0 < A*D'+4 := by positivity
  have hthreshold : 0 < κ*α/8 := by positivity
  have hlim := logarithmicSmoothingBound_tendsto_zero hκ hα hγ A d₀ D' ε
  filter_upwards [hgap, hdrift D' hD, havoid D' (A*D'+4) hD hm,
    hfields ε (κ*α/8) D' 4 hε hthreshold hD (by norm_num),
    hlim.eventually (gt_mem_nhds hδ), eventually_gt_atTop 1]
    with n hngap hndrift hnavoid hnfields hnbound hn
  intro g hg t ht hhor ho
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hhor' : t+α*Real.log n ≤ D'*Real.log n :=
    hhor.trans (mul_le_mul_of_nonneg_right (le_max_right 1 D) hlog.le)
  apply (logarithmic_smoothing_of_small_set_gradient hn g (bad n g)
    hκ.le hA hd₀ hD.le hα hε ht hhor' ho (hngap g hg)
    (hndrift g hg) (hnavoid g hg) ?_).trans hnbound.le
  intro z hz
  apply hnfields g hg z ⟨ht.trans hz.1, hz.2.trans hhor'⟩
  exact (continuousDistance_antitone g ht hz.1).trans ho

end SKRatio.Calculus

end
end

end OAI
