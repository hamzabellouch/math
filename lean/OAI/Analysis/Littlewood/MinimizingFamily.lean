import OAI.Analysis.Littlewood.FlatnessModel
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.NormCast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

/-! A minimizing family with vanishing second error moment. -/
noncomputable section
open MeasureTheory Filter Complex
open scoped BigOperators Topology ComplexConjugate

namespace AsymptoticallyMinimalLittlewoodFiniteFlatness

def boolSign (b : Bool) : ℝ := if b then 1 else -1

abbrev μ : Measure UnitAddCircle := AddCircle.haarAddCircle

def circlePolynomial {N : ℕ} (ε : Fin N → ℝ) : C(UnitAddCircle, ℂ) :=
  ∑ k : Fin N, (ε k : ℂ) • fourier (k : ℤ)

lemma fourier_nat (n : ℕ) (t : UnitAddCircle) :
    fourier (n : ℤ) t = (fourier (1 : ℤ) t) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

lemma circlePolynomial_apply {N : ℕ} (ε : Fin N → ℝ) (t : UnitAddCircle) :
    circlePolynomial ε t = littlewoodValue ε (fourier (1 : ℤ) t) := by
  simp only [circlePolynomial, littlewoodValue, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [fourier_nat]

def signVector {N : ℕ} (b : Fin N → Bool) : Fin N → ℝ := fun k => boolSign (b k)

lemma signVector_signing {N : ℕ} (b : Fin N → Bool) : IsRealSigning (signVector b) := by
  intro k
  cases h : b k <;> simp [signVector, boolSign, h]

lemma signing_eq_signVector {N : ℕ} (ε : Fin N → ℝ) (hε : IsRealSigning ε) :
    ∃ b : Fin N → Bool, signVector b = ε := by
  classical
  refine ⟨fun k => decide (ε k = 1), ?_⟩
  funext k
  rcases hε k with h | h <;> norm_num [signVector, boolSign, h]

lemma exists_minimizing_signing (N : ℕ) :
    ∃ b : Fin N → Bool, ∀ c : Fin N → Bool,
      ‖circlePolynomial (signVector b)‖ ≤ ‖circlePolynomial (signVector c)‖ := by
  classical
  obtain ⟨b, _, hb⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin N → Bool))
    (fun b => ‖circlePolynomial (signVector b)‖) Finset.univ_nonempty
  exact ⟨b, fun c => hb c (Finset.mem_univ c)⟩

def minimizingBits (N : ℕ) : Fin N → Bool := Classical.choose (exists_minimizing_signing N)
def chosenSigns (N : ℕ) : Fin N → ℝ := signVector (minimizingBits N)

lemma chosenSigns_signing (N : ℕ) : IsRealSigning (chosenSigns N) :=
  signVector_signing _

lemma chosenSigns_minimal {N : ℕ} (ε : Fin N → ℝ) (hε : IsRealSigning ε) :
    ‖circlePolynomial (chosenSigns N)‖ ≤ ‖circlePolynomial ε‖ := by
  obtain ⟨b, rfl⟩ := signing_eq_signVector ε hε
  exact Classical.choose_spec (exists_minimizing_signing N) b

/- An all-length upper-flatness bound for real-sign polynomials. -/
variable (hmain : ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
  ∃ ε : Fin N → ℝ, IsRealSigning ε ∧
    ∀ z : ℂ, ‖z‖ = 1 → ‖littlewoodValue ε z‖ ≤ (1 + η) * Real.sqrt N)

include hmain in
lemma chosenSigns_eventually_bound {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ t : UnitAddCircle,
      ‖circlePolynomial (chosenSigns N) t‖ ≤ (1 + η) * Real.sqrt (N : ℝ) := by
  obtain ⟨N₀, _, hN₀⟩ := hmain η hη
  filter_upwards [eventually_ge_atTop N₀] with N hN
  obtain ⟨ε, hε, hbound⟩ := hN₀ N hN
  have hsup : ‖circlePolynomial ε‖ ≤ (1 + η) * Real.sqrt (N : ℝ) := by
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro t
    rw [circlePolynomial_apply]
    exact hbound _ (Circle.norm_coe _)
  intro t
  exact (ContinuousMap.norm_coe_le_norm _ t).trans ((chosenSigns_minimal ε hε).trans hsup)

/-- Exact finite Parseval, obtained from finite orthonormal Fourier sums. -/
lemma circlePolynomial_energy {N : ℕ} (ε : Fin N → ℝ) :
    (∫ t : UnitAddCircle, ‖circlePolynomial ε t‖ ^ 2 ∂μ) = ∑ k, (ε k) ^ 2 := by
  classical
  have hi : Function.Injective (fun k : Fin N => (k : ℤ)) := by
    intro i j h
    apply Fin.ext
    change (i.val : ℤ) = (j.val : ℤ) at h
    exact_mod_cast h
  have ho := (orthonormal_fourier (T := (1 : ℝ))).comp
    (fun k : Fin N => (k : ℤ)) hi
  have he := ho.inner_sum (fun k => (ε k : ℂ)) (fun k => (ε k : ℂ)) Finset.univ
  have hmap : ContinuousMap.toLp 2 μ ℂ (circlePolynomial ε) =
      ∑ k : Fin N, (ε k : ℂ) • fourierLp 2 (k : ℤ) := by
    simp [circlePolynomial, fourierLp, μ]
  change inner ℂ (∑ k : Fin N, (ε k : ℂ) • fourierLp 2 (k : ℤ))
    (∑ k : Fin N, (ε k : ℂ) • fourierLp 2 (k : ℤ)) = _ at he
  rw [← hmap, ContinuousMap.inner_toLp] at he
  have hc : (∫ t : UnitAddCircle, ((‖circlePolynomial ε t‖ ^ 2 : ℝ) : ℂ) ∂μ) =
      ((∑ k : Fin N, (ε k) ^ 2 : ℝ) : ℂ) := by
    simpa [Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_two] using he
  rw [integral_complex_ofReal] at hc
  exact_mod_cast hc

lemma signing_energy {N : ℕ} (ε : Fin N → ℝ) (hε : IsRealSigning ε) :
    (∫ t : UnitAddCircle, ‖circlePolynomial ε t‖ ^ 2 ∂μ) = (N : ℝ) := by
  rw [circlePolynomial_energy]
  have hs : ∀ k, (ε k) ^ 2 = (1 : ℝ) := by
    intro k
    rcases hε k with h | h <;> simp [h]
  simp [hs]

def normalized (N : ℕ) (t : UnitAddCircle) : ℝ :=
  ‖circlePolynomial (chosenSigns N) t‖ / Real.sqrt (N : ℝ)

lemma normalized_nonneg (N : ℕ) (t : UnitAddCircle) : 0 ≤ normalized N t :=
  div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

lemma normalized_continuous (N : ℕ) : Continuous (normalized N) :=
  (circlePolynomial (chosenSigns N)).continuous.norm.div_const _

lemma normalized_measurable (N : ℕ) : Measurable (normalized N) :=
  (normalized_continuous N).measurable

include hmain in
lemma normalized_eventually_bound {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ t, normalized N t ≤ 1 + η := by
  filter_upwards [chosenSigns_eventually_bound hmain hη, eventually_ge_atTop (1 : ℕ)] with N hb hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  intro t
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hNr)).2 (hb t)

include hmain in
lemma normalized_eventually_le_two :
    ∀ᶠ N : ℕ in atTop, ∀ t, normalized N t ≤ 2 := by
  simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using
    normalized_eventually_bound hmain (η := 1) (by norm_num)

lemma normalized_energy {N : ℕ} (hN : 1 ≤ N) :
    (∫ t : UnitAddCircle, normalized N t ^ 2 ∂μ) = 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  simp_rw [normalized, div_pow]
  rw [integral_div, signing_energy _ (chosenSigns_signing N), Real.sq_sqrt hNr.le]
  exact div_self hNr.ne'

lemma continuous_integrable (f : UnitAddCircle → ℝ) (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Elementary second-error-moment estimate; no p-dependent signing is used. -/
lemma normalized_error_sq_bound {N : ℕ} (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η)
    (hb : ∀ t, normalized N t ≤ 1 + η) :
    (∫ t : UnitAddCircle, (normalized N t - 1) ^ 2 ∂μ) ≤ 2 * η := by
  let f := normalized N
  have hf : Continuous f := normalized_continuous N
  have hi := continuous_integrable f hf
  have hi2 := continuous_integrable (fun t => f t ^ 2) (hf.pow 2)
  have hE : (∫ t, f t ^ 2 ∂μ) = 1 := normalized_energy hN
  have hmul : (∫ t, f t ^ 2 ∂μ) ≤ (1 + η) * ∫ t, f t ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono hi2 (hi.const_mul _)
    intro t
    have hp := normalized_nonneg N t
    have ht := hb t
    change f t ≤ 1 + η at ht
    change 0 ≤ f t at hp
    nlinarith
  rw [hE] at hmul
  have hmean : 1 / (1 + η) ≤ ∫ t, f t ∂μ :=
    (div_le_iff₀ (by linarith : 0 < 1 + η)).2 (by nlinarith [hmul])
  have hrec : 1 - η ≤ 1 / (1 + η) :=
    (le_div_iff₀ (by linarith : 0 < 1 + η)).2 (by nlinarith [sq_nonneg η])
  have hid : (∫ t, (f t - 1) ^ 2 ∂μ) = 2 - 2 * ∫ t, f t ∂μ := by
    calc
      _ = ∫ t, (f t ^ 2 - 2 * f t) + 1 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with t
        ring
      _ = 2 - 2 * ∫ t, f t ∂μ := by
        rw [integral_add (f := fun t => f t ^ 2 - 2 * f t) (g := fun _ => (1 : ℝ))
          (hi2.sub (hi.const_mul 2)) (integrable_const 1),
          integral_sub (f := fun t => f t ^ 2) (g := fun t => 2 * f t)
            hi2 (hi.const_mul 2), integral_const_mul, hE]
        simp
        ring
  change (∫ t, (f t - 1) ^ 2 ∂μ) ≤ 2 * η
  rw [hid]
  linarith

include hmain in
lemma normalized_error_sq_tendsto :
    Tendsto (fun N : ℕ => ∫ t : UnitAddCircle, (normalized N t - 1) ^ 2 ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [normalized_eventually_bound hmain (η := ε / 4) (by positivity),
    eventually_ge_atTop (1 : ℕ)] with N hb hN
  have hlo : 0 ≤ ∫ t : UnitAddCircle, (normalized N t - 1) ^ 2 ∂μ :=
    integral_nonneg (fun t => sq_nonneg _)
  have hhi := normalized_error_sq_bound hN (η := ε / 4) (by positivity) hb
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlo]
  linarith

end AsymptoticallyMinimalLittlewoodFiniteFlatness

end

end OAI
