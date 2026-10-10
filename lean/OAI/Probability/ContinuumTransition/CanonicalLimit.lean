import OAI.Probability.ContinuumTransition.DensityLimit

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable def finiteCanonical (φ : ℝ → ℝ) (β L : ℝ) (N : ℕ) : ℝ :=
  -Real.log (partition φ β L N)/L^3

@[simp] theorem finiteCanonical_zero (φ : ℝ → ℝ) (β L : ℝ) :
    finiteCanonical φ β L 0 = 0 := by simp [finiteCanonical, partition]

theorem finiteCanonical_lower_constant {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x) (N : ℕ) :
    -Real.exp (β*B) ≤ finiteCanonical φ β L N := by
  have hc := (summable_grandPartition hφ hβ hL.le hstable 1 0).le_tsum N
    (fun n _ => mul_nonneg (Real.exp_pos _).le (partition_nonneg φ β L n))
  have hc' : partition φ β L N ≤ grandPartition φ 1 β 0 L := by
    simpa only [mul_zero, zero_mul, Real.exp_zero, one_mul, grandPartition] using hc
  have hZ := hc'.trans (grandPartition_le_exp hφ hβ hL.le hstable 1 0)
  simp only [mul_zero, zero_add] at hZ
  have hlog := Real.log_le_log (partition_pos hφ hβ hL hstable N) hZ
  rw [Real.log_exp] at hlog
  unfold finiteCanonical
  apply (le_div_iff₀ (pow_pos hL 3)).2
  nlinarith only [hlog]

theorem finiteCanonical_upper_trial {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {q t β B L D : ℝ} (hq : 0 < q) (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r)
    (hL : 8*q ≤ L) (hD : D ≤ (2*q)⁻¹^3) {N : ℕ} (hN : (N : ℝ) ≤ D*L^3) :
    finiteCanonical φ β L N ≤ (β*trialEnergyConstant t q-Real.log (trialVolume q)) * (N : ℝ)/L^3 := by
  have hpos : 0 < trialVolume q ^ N * Real.exp (-β*(trialEnergyConstant t q*N)) := by
    exact mul_pos (pow_pos (trialVolume_pos hq) N) (Real.exp_pos _)
  have hlow := partition_trial_lower hφ hq ht hβ hstable hcore hL hD hN
  have hlog := Real.log_le_log hpos hlow
  rw [Real.log_mul (pow_pos (trialVolume_pos hq) N).ne' (Real.exp_pos _).ne',
    Real.log_pow, Real.log_exp] at hlog
  unfold finiteCanonical
  apply div_le_div_of_nonneg_right _ (pow_nonneg (by linarith : 0 ≤ L) 3)
  nlinarith only [hlog]

theorem finiteCanonical_densityBounded {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    DensityBounded (finiteCanonical φ β) := by
  intro D hD
  let q : ℝ := (2*(D+1))⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  have hdmesh : D ≤ (2*q)⁻¹^3 := by
    have hh : (2*q)⁻¹ = D+1 := by dsimp [q]; field_simp
    rw [hh]
    nlinarith [sq_nonneg D]
  let C : ℝ := |β*trialEnergyConstant t q-Real.log (trialVolume q)|
  refine ⟨Real.exp (β*B)+C*D+1, 8*q, by dsimp [C]; positivity, by positivity, ?_⟩
  intro L hL N hN
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hlo := finiteCanonical_lower_constant hφ hβ hLpos hstable N
  have hup := finiteCanonical_upper_trial hφ hq ht hβ hstable hcore hL hdmesh hN
  have hup' : finiteCanonical φ β L N ≤ C*D := by
    calc
      _ ≤ (β*trialEnergyConstant t q-Real.log (trialVolume q)) * ((N : ℝ)/L^3) := by
        simpa only [mul_div_assoc] using hup
      _ ≤ C*((N : ℝ)/L^3) := mul_le_mul_of_nonneg_right (le_abs_self _)
        (div_nonneg (Nat.cast_nonneg _) (pow_nonneg hLpos.le 3))
      _ ≤ C*D := mul_le_mul_of_nonneg_left ((div_le_iff₀ (pow_pos hLpos 3)).2 hN) (abs_nonneg _)
  apply abs_le.mpr
  have hCD : 0 ≤ C*D := mul_nonneg (abs_nonneg _) hD.le
  have he := (Real.exp_pos (β*B)).le
  constructor <;> linarith

theorem finiteCanonical_hasBoxInequality {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hsign : ∀ r, 1 ≤ r → φ r ≤ 0) : HasBoxInequality (finiteCanonical φ β) := by
  intro ℓ L hℓ hL r
  classical
  let e : (Fin 3 → Fin ⌊L/(ℓ+2)⌋₊) ≃ Fin (tileCount ℓ L) :=
    Fintype.equivFinOfCardEq (by simp [tileCount])
  have htile := partition_tiling_lower hφ hβ hℓ.le hL.le hstable hsign (fun i => r (e i))
  rw [e.sum_comp] at htile
  have hprod := e.prod_comp (fun i => partition φ β ℓ (r i))
  rw [hprod] at htile
  have hlog := Real.log_le_log (Finset.prod_pos (fun i _ => partition_pos hφ hβ hℓ hstable (r i))) htile
  rw [Real.log_prod (fun i _ => (partition_pos hφ hβ hℓ hstable (r i)).ne')] at hlog
  unfold finiteCanonical
  calc
    -Real.log (partition φ β L (∑ i, r i))/L^3 ≤ -(∑ i, Real.log (partition φ β ℓ (r i)))/L^3 :=
      div_le_div_of_nonneg_right (neg_le_neg hlog) (pow_nonneg hL.le 3)
    _ = ℓ^3/L^3 * ∑ i, -Real.log (partition φ β ℓ (r i))/ℓ^3 := by
      rw [← Finset.sum_div, Finset.sum_neg_distrib]
      field_simp

theorem exists_canonical_density_limit {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) {d : ℝ} (hd : 0 < d) :
    ∃ I : ℝ, Tendsto (fun p : ℝ × ℕ => finiteCanonical φ β p.1 p.2) (densityFilter d) (𝓝 I) := by
  apply exists_density_limit (finiteCanonical_densityBounded hφ ht hβ hstable hcore)
    (finiteCanonical_hasBoxInequality hφ hβ hstable _) hd
  intro r hr
  exact (hcore r (lt_of_lt_of_le (by norm_num) hr)).trans_eq (coreProfile_eq_zero ht hr)

theorem finiteCanonical_lower_entropy {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (N : ℕ) :
    -β * B * ((N : ℝ) / L ^ 3) + ((N : ℝ) / L ^ 3) * Real.log ((N : ℝ) / L ^ 3)
      - (N : ℝ) / L ^ 3 ≤ finiteCanonical φ β L N := by
  by_cases hN : N = 0
  · simp [hN]
  have hh := neg_log_partition_lower hφ hβ hL hstable hN
    (fun x _ => hstable N x)
  have hh' := div_le_div_of_nonneg_right hh (pow_pos hL 3).le
  unfold finiteCanonical
  calc
    _ = (β * (-B * (N : ℝ)) + N * Real.log ((N : ℝ) / L ^ 3) - N) / L ^ 3 := by ring
    _ ≤ _ := hh'

theorem finiteCanonical_tendsto_zero_density {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    Tendsto (fun p : ℝ × ℕ => finiteCanonical φ β p.1 p.2) (densityFilter 0) (𝓝 0) := by
  have hden := densityFilter_density 0
  have hlo : Tendsto (fun p : ℝ × ℕ =>
      -β * B * ((p.2 : ℝ) / p.1 ^ 3) + ((p.2 : ℝ) / p.1 ^ 3) *
        Real.log ((p.2 : ℝ) / p.1 ^ 3) - (p.2 : ℝ) / p.1 ^ 3)
      (densityFilter 0) (𝓝 0) := by
    simpa only [mul_zero, Real.log_zero, add_zero, sub_zero, Function.comp_def] using
      ((hden.const_mul (-β * B)).add (Real.continuous_mul_log.tendsto 0 |>.comp hden)).sub hden
  let C := β * trialEnergyConstant t (1/2) - Real.log (trialVolume (1/2))
  have hup : Tendsto (fun p : ℝ × ℕ => C * ((p.2 : ℝ) / p.1 ^ 3))
      (densityFilter 0) (𝓝 0) := by
    simpa only [mul_zero] using hden.const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [(densityFilter_length 0).eventually (eventually_gt_atTop 0)] with p hp
    exact finiteCanonical_lower_entropy hφ hβ hp hstable p.2
  · filter_upwards [(densityFilter_length 0).eventually (eventually_ge_atTop 4),
      hden.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with p hp hpd
    have hL : 0 < p.1 := by linarith
    have hh := finiteCanonical_upper_trial hφ (by norm_num : (0 : ℝ) < 1 / 2)
      ht hβ hstable hcore (by linarith : 8*(1/2 : ℝ) ≤ p.1)
      (by norm_num : (1 : ℝ) ≤ (2*(1/2))⁻¹^3)
      ((div_le_iff₀ (pow_pos hL 3)).1 hpd)
    simpa only [C, mul_div_assoc] using hh

noncomputable def canonicalDensity (φ : ℝ → ℝ) (β d : ℝ) : ℝ :=
  liminf (fun p : ℝ × ℕ => finiteCanonical φ β p.1 p.2) (densityFilter d)

theorem finiteCanonical_tendsto {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) (hd : 0 ≤ d) :
    Tendsto (fun p : ℝ × ℕ => finiteCanonical φ β p.1 p.2)
      (densityFilter d) (𝓝 (canonicalDensity φ β d)) := by
  let : Fact (0 ≤ d) := ⟨hd⟩
  obtain hzero | hpos := hd.eq_or_lt
  · subst d
    have hz := finiteCanonical_tendsto_zero_density hφ ht hβ hstable hcore
    simpa only [canonicalDensity, hz.liminf_eq] using hz
  · obtain ⟨I, hI⟩ := exists_canonical_density_limit hφ ht hβ hstable hcore hpos
    simpa only [canonicalDensity, hI.liminf_eq] using hI

@[simp] theorem canonicalDensity_zero {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) : canonicalDensity φ β 0 = 0 := by
  let : Fact (0 ≤ (0 : ℝ)) := ⟨le_rfl⟩
  exact (finiteCanonical_tendsto_zero_density hφ ht hβ hstable hcore).liminf_eq

noncomputable def canonicalFreeEnergy (φ : ℝ → ℝ) (β d : ℝ) : ℝ :=
  canonicalDensity φ β d / β

theorem hasCanonicalFreeEnergy_of_core {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B : ℝ} (ht : 1 < t)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    HasCanonicalFreeEnergy φ (canonicalFreeEnergy φ) := by
  intro β d hβ hd
  have hlim := (finiteCanonical_tendsto hφ ht hβ.le hstable hcore hd.le).comp
    (floor_density_tendsto hd.le)
  have hneg := hlim.neg
  convert hneg using 1
  · ext L
    simp only [Function.comp_def, finiteCanonical, div_eq_mul_inv, inv_pow]
    ring
  · simp only [canonicalFreeEnergy]
    field_simp

theorem concaveOn_canonicalDensity {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B d : ℝ} (ht : 1 < t)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) (hd : 0 ≤ d) :
    ConcaveOn ℝ (Ioi 0) (fun β => canonicalDensity φ β d) := by
  let : Fact (0 ≤ d) := ⟨hd⟩
  refine ⟨convex_Ioi _, ?_⟩
  intro β hβ γ hγ a b ha hb hab
  simp only [smul_eq_mul]
  have hc : 0 < a * β + b * γ := by
    have hh := (convex_Ioi (0 : ℝ)) hβ hγ ha hb hab
    exact hh
  have hβlim := (finiteCanonical_tendsto hφ ht hβ.le hstable hcore hd)
  have hγlim := (finiteCanonical_tendsto hφ ht hγ.le hstable hcore hd)
  have hclim := (finiteCanonical_tendsto hφ ht hc.le hstable hcore hd)
  apply le_of_tendsto_of_tendsto ((hβlim.const_mul a).add (hγlim.const_mul b)) hclim
  filter_upwards [(densityFilter_length d).eventually (eventually_gt_atTop 0)] with p hp
  have hh := (convexOn_log_partition hφ hp hstable p.2).2 hβ hγ ha hb hab
  simp only [smul_eq_mul] at hh
  dsimp [finiteCanonical]
  have hden : 0 < p.1 ^ 3 := pow_pos hp 3
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
  exact div_le_div_of_nonneg_right (by linarith only [hh]) hden.le

end ContinuumTemperature
end

end OAI
