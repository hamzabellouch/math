import OAI.Probability.FreeIsing.Critical.GlobalEndgame
import OAI.Probability.FreeIsing.Trees.EndpointFromPaths

namespace OAI

noncomputable section
open Filter
namespace Problem367

structure WeightedPathEstimates (Q L : ℕ → ℝ)
    (A B E c a q C₀ S V ω : ℝ) : Prop where
  noise_nonneg : ∀ n, 0 ≤ Q n
  linear_nonneg : ∀ n, 0 ≤ L n
  noise_short : ∀ n, Q n ≤ A * S * n
  linear_short : ∀ n, L n ≤ A * V
  noise_long : ∀ n : ℕ, C₀ / ω ≤ (n : ℝ) →
    Q n ≤ B * S * ((n : ℝ) * Real.exp (-(c * ω) * n)) +
      E * ((n : ℝ) ^ 2 * Real.exp (-a * q ^ n))
  linear_long : ∀ n : ℕ, C₀ / ω ≤ (n : ℝ) →
    L n ≤ B * V * Real.exp (-(c * ω) * n) + E * Real.exp (-a * q ^ n)

theorem sqrt_le_path_majorant {x B S E c a q ω : ℝ} (n : ℕ)
    (hB : 0 ≤ B) (hS : 0 ≤ S) (hE : 0 ≤ E)
    (hx : x ≤ B * S * ((n : ℝ) * Real.exp (-(c * ω) * n)) +
      E * ((n : ℝ) ^ 2 * Real.exp (-a * q ^ n))) :
    Real.sqrt x ≤ Real.sqrt B * Real.sqrt S *
      (Real.sqrt n * Real.exp (-((c / 2) * ω) * n)) +
      Real.sqrt E * ((n : ℝ) * Real.exp (-(a / 2) * q ^ n)) := by
  let u := Real.sqrt B * Real.sqrt S *
    (Real.sqrt n * Real.exp (-((c / 2) * ω) * n))
  let v := Real.sqrt E * ((n : ℝ) * Real.exp (-(a / 2) * q ^ n))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu2 : u ^ 2 = B * S * ((n : ℝ) * Real.exp (-(c * ω) * n)) := by
    dsimp [u]
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hB, Real.sq_sqrt hS,
      Real.sq_sqrt (Nat.cast_nonneg n), ← Real.exp_nat_mul]
    congr 2
    ring_nf
  have hv2 : v ^ 2 = E * ((n : ℝ) ^ 2 * Real.exp (-a * q ^ n)) := by
    dsimp [v]
    rw [mul_pow, mul_pow, Real.sq_sqrt hE, ← Real.exp_nat_mul]
    congr 2
    ring_nf
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg hu hv, ?_⟩
  nlinarith [mul_nonneg hu hv]

theorem WeightedPathEstimates.summable
    {Q L : ℕ → ℝ} {A B E c a q C₀ S V ω : ℝ}
    (h : WeightedPathEstimates Q L A B E c a q C₀ S V ω)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hS : 0 ≤ S)
    (hc : 0 < c) (ha : 0 < a) (hq : 1 < q) (hω : 0 < ω) :
    Summable Q ∧ Summable L ∧ Summable (fun n => Real.sqrt (Q n)) := by
  let R := Nat.ceil (C₀ / ω)
  have hR (n : ℕ) (hn : R ≤ n) : C₀ / ω ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hQsum := ((summable_path_attenuation 1 (mul_pos hc hω)).mul_left (B * S)).add
    ((summable_superexponential_path 2 ha hq).mul_left E)
  have hLsum := ((summable_path_attenuation 0 (mul_pos hc hω)).mul_left (B * V)).add
    ((summable_superexponential_path 0 ha hq).mul_left E)
  have hZsum := ((summable_sqrt_path_attenuation (mul_pos (half_pos hc) hω)).mul_left
    (Real.sqrt B * Real.sqrt S)).add
    ((summable_superexponential_path 1 (half_pos ha) hq).mul_left (Real.sqrt E))
  refine ⟨?_, ?_, ?_⟩
  · apply hQsum.of_norm_bounded_eventually_nat
    refine eventually_atTop.mpr ⟨R, fun n hn => ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (h.noise_nonneg n)]
    simpa only [pow_one] using h.noise_long n (hR n hn)
  · apply hLsum.of_norm_bounded_eventually_nat
    refine eventually_atTop.mpr ⟨R, fun n hn => ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (h.linear_nonneg n)]
    simpa only [pow_zero, one_mul] using h.linear_long n (hR n hn)
  · apply hZsum.of_norm_bounded_eventually_nat
    refine eventually_atTop.mpr ⟨R, fun n hn => ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [pow_one] using sqrt_le_path_majorant n hB hS hE (h.noise_long n (hR n hn))

def weightedPathEndpointConstant (A B E c a q C : ℝ) : ℝ :=
  max 1 (max
    (max (2 * A * (C + 1) ^ 2 + B * (2 / min c 1) ^ 2)
      (E * ∑' n : ℕ, (n : ℝ) ^ 2 * Real.exp (-(a / 2) * q ^ n)))
    (max
      (max (A * (C + 1) + B * (2 / min c 1))
        (E * ∑' n : ℕ, Real.exp (-(a / 2) * q ^ n)))
      (max (4 * Real.sqrt A * (C + 1) * Real.sqrt (C + 1) +
        Real.sqrt B * (3 / (min (c / 2) 1 * Real.sqrt (min (c / 2) 1))))
        (Real.sqrt E * ∑' n : ℕ, (n : ℝ) * Real.exp (-((a / 2) / 2) * q ^ n)))))

theorem WeightedPathEstimates.endpoint_bounds
    {Q L : ℕ → ℝ} {A B E c a q C₀ S V K ω C : ℝ}
    (h : WeightedPathEstimates Q L A B E c a q C₀ S V ω)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E) (hS : 0 ≤ S)
    (hc : 0 < c) (ha : 0 < a) (hq : 1 < q)
    (hV : 0 < V) (hVK : V ≤ K) (hK : 1 ≤ K)
    (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hC0 : 0 ≤ C) (hCC : C₀ ≤ C) (hC : 1 ≤ Real.log q * C)
    (hbase : 2 ≤ ((a / 2) / 2) * q ^ C) :
    let M := weightedPathEndpointConstant A B E c a q C
    Summable Q ∧ Summable L ∧ Summable (fun n => Real.sqrt (Q n)) ∧
    (∑' n, Q n) ≤ M * (S * ((ω⁻¹) ^ 2 + (Real.log (1 + Real.log (K / V))) ^ 2) + V ^ 2) ∧
    (∑' n, L n) ≤ M * (V * (ω⁻¹ + Real.log (1 + Real.log (K / V))) + V ^ 2) ∧
    (∑' n, Real.sqrt (Q n)) ≤ M * (Real.sqrt S *
      (ω⁻¹ * Real.sqrt (ω⁻¹) + (Real.log (1 + Real.log (K / V))) ^ ((3 : ℝ) / 2)) + V) := by
  let R := pathCutoff C ω (1 + Real.log (K / V))
  have hI : 1 ≤ 1 + Real.log (K / V) := by
    linarith [Real.log_nonneg ((one_le_div hV).mpr hVK)]
  have hlog : 0 ≤ Real.log (1 + Real.log (K / V)) := Real.log_nonneg hI
  have happ (n : ℕ) (hn : R ≤ n) : C₀ / ω ≤ (n : ℝ) :=
    pathCutoff_applicability hCC hC0 hω hI hn
  have hbase' : 2 ≤ (a / 2) * q ^ C := by
    have hp : 0 ≤ q ^ C := Real.rpow_nonneg (zero_lt_one.trans hq).le _
    nlinarith [mul_nonneg ha.le hp]
  have hQ := tsum_quadratic_endpoint_at_cutoff R 2 h.noise_nonneg hA hB hE hS
    hV hVK hK hc hω hω1 ha hq hC0 hC hbase' rfl
    (fun n _ => h.noise_short n) (fun n hn => h.noise_long n (happ n hn))
  have hL := tsum_linear_endpoint_at_cutoff R 0 h.linear_nonneg hA hB hE
    hV hVK hK hc hω hω1 ha hq hC0 hC hbase' rfl
    (fun n _ => h.linear_short n)
    (fun n hn => by simpa only [pow_zero, one_mul] using h.linear_long n (happ n hn))
  have hZ := tsum_sqrt_endpoint_at_cutoff (S := S) R 1 (fun n => Real.sqrt_nonneg (Q n))
    (Real.sqrt_nonneg A) (Real.sqrt_nonneg B) (Real.sqrt_nonneg E)
    hV hVK hK (half_pos hc) hω hω1 (half_pos ha) hq hC0 hC hbase rfl
    (fun n _ => by
      calc
        Real.sqrt (Q n) ≤ Real.sqrt (A * S * n) := Real.sqrt_le_sqrt (h.noise_short n)
        _ = Real.sqrt A * Real.sqrt S * Real.sqrt n := by
          rw [Real.sqrt_mul (mul_nonneg hA hS), Real.sqrt_mul hA])
    (fun n hn => by simpa only [pow_one] using
      sqrt_le_path_majorant n hB hS hE (h.noise_long n (happ n hn)))
  rw [mul_sqrt_eq_three_halves hlog] at hZ
  obtain ⟨hsQ, hsL, hsZ⟩ := h.summable hB hE hS hc ha hq hω
  refine ⟨hsQ, hsL, hsZ, ?_, ?_, ?_⟩
  · exact hQ.trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) (by positivity))
  · simp only [pow_zero, one_mul] at hL
    exact hL.trans (mul_le_mul_of_nonneg_right
      (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) (by positivity))
  · simp only [pow_one] at hZ
    exact hZ.trans (mul_le_mul_of_nonneg_right
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) (by positivity))

theorem exists_spatial_endpoint_constant_of_path_estimates
    {A B E c a q N C₀ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : 0 < c) (ha : 0 < a) (hq : 1 < q) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ {Q L : ℕ → ℝ} {S V K ω D : ℝ},
      WeightedPathEstimates Q L A B E c a q C₀ S V ω →
      0 ≤ S → S ≤ N * V → 0 < V → V ≤ K → 1 ≤ K → 0 < ω → ω ≤ 1 →
      D ≤ N * (V + (∑' n, Q n) + (∑' n, L n) +
        Real.sqrt V * (∑' n, Real.sqrt (Q n))) →
      CriticalSpatialEndpointBounds D (∑' n, Q n) (∑' n, L n)
        (∑' n, Real.sqrt (Q n)) S V M K ω := by
  obtain ⟨C, hC0, hCC, hC, hbase⟩ := exists_path_cutoff_constant (half_pos ha) hq C₀
  let W := weightedPathEndpointConstant A B E c a q C
  let M := max N W
  have hW1 : 1 ≤ W := le_max_left _ _
  have hWM : W ≤ M := le_max_right _ _
  have hNM : N ≤ M := le_max_left _ _
  refine ⟨M, hW1.trans hWM, ?_⟩
  intro Q L S V K ω D h hS hSV hV hVK hK hω hω1 hD
  obtain ⟨_, _, _, hQ, hL, hZ⟩ := h.endpoint_bounds hA hB hE hS hc ha hq
    hV hVK hK hω hω1 hC0.le hCC hC hbase
  have hI : 1 ≤ 1 + Real.log (K / V) := by
    linarith [Real.log_nonneg ((one_le_div hV).mpr hVK)]
  have hlog : 0 ≤ Real.log (1 + Real.log (K / V)) := Real.log_nonneg hI
  refine ⟨hS, hSV.trans (mul_le_mul_of_nonneg_right hNM hV.le), ?_, ?_, ?_, ?_⟩
  · exact hQ.trans (mul_le_mul_of_nonneg_right hWM (by positivity))
  · exact hL.trans (mul_le_mul_of_nonneg_right hWM (by positivity))
  · exact hZ.trans (mul_le_mul_of_nonneg_right hWM (by positivity))
  · apply hD.trans
    apply mul_le_mul_of_nonneg_right hNM
    exact add_nonneg (add_nonneg (add_nonneg hV.le (tsum_nonneg h.noise_nonneg))
      (tsum_nonneg h.linear_nonneg))
      (mul_nonneg (Real.sqrt_nonneg _) (tsum_nonneg (fun _ => Real.sqrt_nonneg _)))

end Problem367

end

end OAI
