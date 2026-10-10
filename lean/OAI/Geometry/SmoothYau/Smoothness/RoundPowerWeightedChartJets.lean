import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.CompactMetricInverseJets

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
section EnvelopePowers
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma real_power_envelope_jet_bound_on [FiniteDimensional ℝ E]
    {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f O) (h n : ℕ) {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ A*(C)^j) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => (f y^n).re) x‖ ≤ A^n*((n:ℝ)*C)^j := by
  obtain ⟨F,hF,he⟩ := smooth_extension_at hO hxO hf
  have hh := complex_power_envelope_jet_bound hF x h n hA hC (fun j hj => by
    rw [←(he.iteratedFDeriv ℝ j).self_of_nhds]
    exact hfj j hj)
  intro j hj
  have heRe : (fun y => (f y^n).re) =ᶠ[𝓝 x] (fun y => (F y^n).re) :=
    he.mono (fun y hy => congrArg (fun z : ℂ => (z^n).re) hy)
  rw [(heRe.iteratedFDeriv ℝ j).self_of_nhds]
  calc
    _ ≤ ‖Complex.reCLM‖*‖iteratedFDeriv ℝ j (fun y => F y^n) x‖ :=
      ContinuousLinearMap.norm_iteratedFDeriv_comp_left Complex.reCLM (x:=x)
        (hF.pow n).contDiffAt (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))
    _ ≤ 1*(A^n*((n:ℝ)*C)^j) := mul_le_mul (le_of_eq Complex.reCLM_norm)
      (hh j hj) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _
end EnvelopePowers

variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

theorem roundPower_dominated_chart_jets
    (a b : Euclidean (d+1)) (p : Sphere d) {K : Set (Euclidean d)}
    (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean d) p).target)
    (φ : Euclidean d → ℝ) (hφ : ContinuousOn φ K) (h : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hdom : ∀ y ∈ K, ‖roundPlanarChart a b p y‖ ≤ ρ*Real.exp (φ y)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ y ∈ K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) y‖ ≤
        C*(n:ℝ)^j*ρ^n*Real.exp ((n:ℝ)*φ y) := by
  have hf := roundPlanarChart_smooth a b p
  obtain ⟨D,hD,hDj⟩ := compact_raw_jet_bound (chartAt (Euclidean d) p).open_target hK hKO hf h
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hφ
  let r := ρ*Real.exp (-B)
  have hr : 0 < r := mul_pos hρ (Real.exp_pos _)
  let T := max 1 (D/r)
  have hT1 : 1 ≤ T := le_max_left _ _
  have hT0 : 0 ≤ T := zero_le_one.trans hT1
  refine ⟨T^h,pow_pos (zero_lt_one.trans_le hT1) _,?_⟩
  intro n y hy j hj
  have hry : r ≤ ρ*Real.exp (φ y) := by
    have hlow : -B ≤ φ y := by
      have hh := (neg_abs_le (φ y)).trans' (neg_le_neg (hB y hy))
      simpa only [Real.norm_eq_abs] using hh
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlow) hρ.le
  have hraw : ∀ k ≤ h, ‖iteratedFDeriv ℝ k (roundPlanarChart a b p) y‖ ≤
      (ρ*Real.exp (φ y))*T^k := by
    intro k hk
    by_cases hk0 : k=0
    · subst k
      simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hdom y hy
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hTk : T ≤ T^k := by simpa only [pow_one] using pow_le_pow_right₀ hT1 hk1
      calc
        _ ≤ D := hDj k hk y hy
        _ = r*(D/r) := by field_simp
        _ ≤ (ρ*Real.exp (φ y))*T^k := mul_le_mul hry ((le_max_right _ _).trans hTk)
          (div_nonneg (zero_le_one.trans hD) hr.le) (by positivity)
  have hp := real_power_envelope_jet_bound_on (chartAt (Euclidean d) p).open_target
    (hKO hy) hf h n (by positivity : 0 ≤ ρ*Real.exp (φ y)) hT0 hraw j hj
  have he : (ρ*Real.exp (φ y))^n*((n:ℝ)*T)^j =
      T^j*(n:ℝ)^j*ρ^n*Real.exp ((n:ℝ)*φ y) := by
    rw [mul_pow,mul_pow,Real.exp_nat_mul]
    ring
  rw [he] at hp
  exact hp.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT1 hj) (pow_nonneg (Nat.cast_nonneg _) _))
      (pow_nonneg hρ.le _)) (Real.exp_pos _).le)

theorem roundPower_dominated_chart_rapid_decay
    (a b : Euclidean (d+1)) (p : Sphere d) {K : Set (Euclidean d)}
    (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean d) p).target)
    (φ : Euclidean d → ℝ) (hφ : ContinuousOn φ K) (h P : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hdom : ∀ y ∈ K, ‖roundPlanarChart a b p y‖ ≤ ρ*Real.exp (φ y)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, ∀ y ∈ K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) y‖ ≤
        ((n:ℝ)^P)⁻¹*Real.exp ((n:ℝ)*φ y) := by
  obtain ⟨C,hC,hbound⟩ := roundPower_dominated_chart_jets a b p hK hKO φ hφ h hρ hdom
  have ht : Tendsto (fun n : ℕ => C*((n:ℝ)^(h+P)*ρ^n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_const_mul_const_pow_of_lt_one (h+P) hρ.le hρ1).const_mul C
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (Iio_mem_nhds zero_lt_one))
  refine ⟨max N 1,le_max_right _ _,?_⟩
  intro n hn y hy j hj
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn1
  have hnpos : 0 < (n:ℝ) := zero_lt_one.trans_le hnR
  have hsmall : C*(n:ℝ)^h*ρ^n ≤ ((n:ℝ)^P)⁻¹ := by
    rw [←one_div]
    apply (le_div_iff₀ (pow_pos hnpos P)).mpr
    have he : C*(n:ℝ)^h*ρ^n*(n:ℝ)^P = C*((n:ℝ)^(h+P)*ρ^n) := by
      rw [pow_add]; ring
    rw [he]
    exact (hN n ((le_max_left _ _).trans hn)).le
  apply (hbound n y hy j hj).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hnR hj) hC.le) (pow_nonneg hρ.le n)).trans hsmall


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

theorem roundPower_weighted_chart_jets
    (a b : Euclidean (d+1)) (p : Sphere d) {K : Set (Euclidean d)}
    (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean d) p).target)
    (φ : Euclidean d → ℝ) (hφ : ContinuousOn φ K) (h : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ y ∈ K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) y‖ ≤
        C*(n:ℝ)^j*(Real.exp ((n:ℝ)*φ y)+‖roundPlanarChart a b p y‖^n) := by
  have hf := roundPlanarChart_smooth a b p
  obtain ⟨D,hD,hDj⟩ := compact_raw_jet_bound (chartAt (Euclidean d) p).open_target hK hKO hf h
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hφ
  let r := Real.exp (-B)
  have hr : 0 < r := Real.exp_pos _
  let T := max 1 (D/r)
  have hT1 : 1 ≤ T := le_max_left _ _
  have hT0 : 0 ≤ T := zero_le_one.trans hT1
  refine ⟨T^h,pow_pos (zero_lt_one.trans_le hT1) _,?_⟩
  intro n y hy j hj
  let A := max ‖roundPlanarChart a b p y‖ (Real.exp (φ y))
  have hA : 0 ≤ A := (norm_nonneg _).trans (le_max_left _ _)
  have hrA : r ≤ A := by
    have hlow : -B ≤ φ y := by
      have hh := (neg_abs_le (φ y)).trans' (neg_le_neg (hB y hy))
      simpa only [Real.norm_eq_abs] using hh
    exact (Real.exp_le_exp.mpr hlow).trans (le_max_right _ _)
  have hraw : ∀ k ≤ h, ‖iteratedFDeriv ℝ k (roundPlanarChart a b p) y‖ ≤ A*T^k := by
    intro k hk
    by_cases hk0 : k=0
    · subst k
      simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using (le_max_left
        ‖roundPlanarChart a b p y‖ (Real.exp (φ y)))
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hTk : T ≤ T^k := by simpa only [pow_one] using pow_le_pow_right₀ hT1 hk1
      calc
        _ ≤ D := hDj k hk y hy
        _ = r*(D/r) := by field_simp
        _ ≤ A*T^k := mul_le_mul hrA ((le_max_right _ _).trans hTk)
          (div_nonneg (zero_le_one.trans hD) hr.le) hA
  have hp := real_power_envelope_jet_bound_on (chartAt (Euclidean d) p).open_target
    (hKO hy) hf h n hA hT0 hraw j hj
  have hAn : A^n ≤ Real.exp ((n:ℝ)*φ y)+‖roundPlanarChart a b p y‖^n := by
    by_cases he : ‖roundPlanarChart a b p y‖ ≤ Real.exp (φ y)
    · dsimp [A]
      rw [max_eq_right he,←Real.exp_nat_mul]
      exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
    · dsimp [A]
      rw [max_eq_left (le_of_not_ge he)]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have he : A^n*((n:ℝ)*T)^j = T^j*(n:ℝ)^j*A^n := by rw [mul_pow]; ring
  rw [he] at hp
  exact hp.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT1 hj) (pow_nonneg (Nat.cast_nonneg _) _))
    hAn (pow_nonneg hA _) (by positivity))


end YauCounterexamples
end

end OAI
