import Mathlib
import OAI.Analysis.CoulombRadii.LimitTheory.UniformGroundStateCountControl

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

theorem rawCount_le_packetMass {n : ℕ} (g : Position → ℝ)
    (hg : (∫ y, g y ^ 2) = 1) {c₁ r₀ s : ℝ} (hc : 0 < c₁)
    (hr : 0 < r₀) (hs : 0 < s) (S T : Set Position)
    (hST : ∀ z y, z ∈ S → packetKernel g c₁ r₀ s z y ≠ 0 → y ∈ T)
    (x : Configuration n) : rawCount S x ≤ packetMass g c₁ r₀ s T x := by
  classical
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : x i ∈ S
  · simp only [Set.indicator_of_mem hi]
    have h := setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := T) (μ := volume) (f := packetKernel g c₁ r₀ s (x i)) (fun y hy => by
        by_contra hK
        exact hy (hST (x i) y hi hK))
    rw [h, integral_packetKernel g hg hc hr hs]
  · simp only [Set.indicator_of_notMem hi]
    exact integral_nonneg fun y => packetKernel_nonneg g hc hr hs (x i) y

def spatialAnnulus (a b : ℝ) : Set Position := {x | a < ‖x‖ ∧ ‖x‖ < b}

theorem measurableSet_spatialAnnulus (a b : ℝ) : MeasurableSet (spatialAnnulus a b) :=
  (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (isOpen_lt continuous_norm continuous_const).measurableSet

theorem packetMass_annulus_sandwich {n : ℕ} (g : Position → ℝ)
    (hgnorm : (∫ y, g y ^ 2) = 1) (hgsupp : ∀ x, 1 < ‖x‖ → g x = 0)
    {c₁ r₀ s a b η : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (ha : 0 < a) (hab : a < b) (hη : 0 < η) (hηa : η < a)
    (hδ : (c₁ * s ^ packetExponent) * b < η)
    (hclamp : (1 + c₁ * s ^ packetExponent) * r₀ ≤ (a-η)*s)
    (x : Configuration n) :
    packetMass g c₁ r₀ s (spatialAnnulus ((a+η)*s) ((b-η)*s)) x ≤
      rawCount (spatialAnnulus (a*s) (b*s)) x ∧
    rawCount (spatialAnnulus (a*s) (b*s)) x ≤
      packetMass g c₁ r₀ s (spatialAnnulus ((a-η)*s) ((b+η)*s)) x := by
  have hdpos : 0 < c₁ * s ^ packetExponent := mul_pos hc (Real.rpow_pos_of_pos hs _)
  have hdb : 0 < b := ha.trans hab
  have hd1 : c₁ * s ^ packetExponent < 1 := by nlinarith
  have hr_as : r₀ < a*s := by nlinarith
  constructor
  · apply packetMass_le_rawCount g hgnorm hc hr hs
    intro z y hy hK
    change (a+η)*s < ‖y‖ ∧ ‖y‖ < (b-η)*s at hy
    have hz : r₀ ≤ ‖z‖ := by
      by_contra! hz
      have hyc := packetKernel_clamped_support g hgsupp hc hr hs z y hz.le hK
      nlinarith
    obtain ⟨hl, hu⟩ := packetKernel_relative_support g hgsupp hc hr hs z y hz hK
    change a*s < ‖z‖ ∧ ‖z‖ < b*s
    constructor
    · by_contra! hn
      have hstep : (1+c₁*s^packetExponent)*‖z‖ ≤ (1+c₁*s^packetExponent)*(a*s) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      have hδa : (c₁*s^packetExponent)*a < η := by nlinarith
      have hsmall := mul_lt_mul_of_pos_right hδa hs
      nlinarith
    · by_contra! hn
      have hstep : (1-c₁*s^packetExponent)*(b*s) ≤ (1-c₁*s^packetExponent)*‖z‖ :=
        mul_le_mul_of_nonneg_left hn (by linarith)
      have hsmall := mul_lt_mul_of_pos_right hδ hs
      nlinarith
  · apply rawCount_le_packetMass g hgnorm hc hr hs
    intro z y hz hK
    change a*s < ‖z‖ ∧ ‖z‖ < b*s at hz
    obtain ⟨hl, hu⟩ := packetKernel_relative_support g hgsupp hc hr hs z y
      (hr_as.le.trans hz.1.le) hK
    have hsmall := mul_lt_mul_of_pos_right hδ hs
    have hstep : (c₁*s^packetExponent)*‖z‖ < (c₁*s^packetExponent)*(b*s) :=
      mul_lt_mul_of_pos_left hz.2 hdpos
    change (a-η)*s < ‖y‖ ∧ ‖y‖ < (b+η)*s
    constructor <;> nlinarith

theorem conditional_integral_square_le {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (_hm : m ≤ m₀) {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    (∫ z, μ[X | m] z ^ 2 ∂μ) ≤ ∫ z, X z ^ 2 ∂μ := by
  have hnorm : Integrable (fun z => ‖X z‖ ^ (2 : ℝ)) μ := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hX.integrable_sq
  have hJ := integral_norm_condExp_rpow_le (m := m) (by norm_num : (1 : ℝ) ≤ 2) hnorm
  simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hJ

theorem conditional_l2_le {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    Real.sqrt (∫ z, μ[X | m] z ^ 2 ∂μ) ≤ Real.sqrt (∫ z, X z ^ 2 ∂μ) :=
  by exact Real.sqrt_le_sqrt (conditional_integral_square_le (m₀ := m₀) (m := m) μ hm hX)

theorem exteriorMass_sub {N : ℕ} {ψ : Wavefunction (N+1)}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) {r R : ℝ} (hrR : r ≤ R) :
    exteriorMass ψ r - exteriorMass ψ R = ∫ x in spatialAnnulus r R, density ψ x := by
  unfold exteriorMass
  rw [← setIntegral_sdiff (isOpen_lt continuous_const continuous_norm).measurableSet
    (integrable_density hψ).integrableOn (by intro x hx; exact lt_of_le_of_lt hrR hx)]
  apply setIntegral_congr_set
  have hsphere : ∀ᵐ x : Position, x ∉ Metric.sphere (0 : Position) R := by
    rw [ae_iff]
    convert Measure.addHaar_sphere volume (0 : Position) R using 1
    congr 1
    ext x
    simp
  filter_upwards [hsphere] with x hx
  simp only [Metric.mem_sphere, dist_zero_right] at hx
  apply propext
  change (r < ‖x‖ ∧ ¬ R < ‖x‖) ↔ (r < ‖x‖ ∧ ‖x‖ < R)
  constructor
  · rintro ⟨hr, hR⟩
    exact ⟨hr, lt_of_le_of_ne (le_of_not_gt hR) hx⟩
  · exact fun h => ⟨h.1, not_lt_of_ge h.2.le⟩

theorem dyadic_tail_bound {T : ℝ → ℝ} {A B : ℝ} (hA : 0 ≤ A)
    (hT : Antitone T) (hB : T 1 ≤ B)
    (hshell : ∀ r : ℝ, 0 < r → r < 1 → T r - T (2*r) ≤ A / r^3)
    {r : ℝ} (hr : 0 < r) : T r ≤ ((8/7 : ℝ)*A) / r^3 + B := by
  have hind : ∀ n : ℕ, ∀ u : ℝ, 0 < u → 1 ≤ (2:ℝ)^n*u →
      T u ≤ ((8/7 : ℝ)*A) / u^3 + B := by
    intro n
    induction n with
    | zero =>
      intro u hu htop
      have ht : T u ≤ B := (hT (by simpa using htop)).trans hB
      have : 0 ≤ ((8/7 : ℝ)*A) / u^3 := by positivity
      linarith
    | succ n ih =>
      intro u hu htop
      by_cases hu1 : 1 ≤ u
      · have ht := (hT hu1).trans hB
        have : 0 ≤ ((8/7 : ℝ)*A) / u^3 := by positivity
        linarith
      · have htop' : 1 ≤ (2:ℝ)^n*(2*u) := by
          simpa only [pow_succ, mul_assoc] using htop
        have hnext := ih (2*u) (by positivity) htop'
        have hnow := hshell u hu (lt_of_not_ge hu1)
        have hid : A/u^3 + ((8/7:ℝ)*A)/(2*u)^3 = ((8/7:ℝ)*A)/u^3 := by
          field_simp
          ring
        linarith
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).eventually
    (eventually_ge_atTop (1/r))).exists
  exact hind n r hr ((div_le_iff₀ hr).mp hn)

def Admissible (Zbar : ℝ → ℕ) (s : ℕ → ℝ) (N : ℕ → ℕ) : Prop :=
  (∀ᶠ n in atTop, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧
  (∀ᶠ n in atTop, Zbar (s n) ≤ N n + 1) ∧
  Tendsto (fun n => (N n + 1 : ℝ) * s n ^ (3 : ℕ)) atTop atTop

def ExpectedExteriorAsymptotic (Zbar : ℝ → ℕ) : Prop :=
  ∀ (s : ℕ → ℝ) (N : ℕ → ℕ), Admissible Zbar s N →
    ∀ ψ : ∀ n, Wavefunction (N n + 1),
      (∀ n, IsNormalizedGroundState (N n + 1) (ψ n)) →
      ∀ a : ℝ, 0 < a →
        Tendsto (fun n => s n ^ (3 : ℕ) * exteriorMass (ψ n) (a*s n))
          atTop (𝓝 (bTF^ (3 : ℕ) / a^ (3 : ℕ)))

def radiusChargeThreshold (Zbar : ℝ → ℕ) (m : ℕ) : ℕ :=
  max (Zbar ((m : ℝ)^(-(1/3 : ℝ)))) ((m+1)^2)

theorem radius_scales_admissible (Zbar : ℝ → ℕ) (m N : ℕ → ℕ)
    (hm : StrictMono m) (hN : ∀ n, radiusChargeThreshold Zbar (m n) ≤ N n) :
    Admissible Zbar (fun n => (m n : ℝ)^(-(1/3 : ℝ))) N := by
  have hmR : Tendsto (fun n => (m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm.tendsto_atTop
  have hmp : ∀ᶠ n in atTop, 0 < (m n : ℝ) := hmR.eventually (eventually_gt_atTop 0)
  refine ⟨hmp.mono (fun n hn => Real.rpow_pos_of_pos hn _),
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/3)).comp hmR, ?_, ?_⟩
  · exact Eventually.of_forall fun n =>
      ((le_max_left _ _).trans (hN n)).trans (Nat.le_succ _)
  · apply tendsto_atTop_mono' atTop _ hmR
    filter_upwards [hmp] with n hn
    rw [Real.rpow_neg hn.le, inv_pow, cube_root_cube, ← div_eq_mul_inv]
    apply (le_div_iff₀ hn).mpr
    have hlarge : ((m n + 1 : ℕ) : ℝ)^2 ≤ (N n : ℝ) := by
      exact_mod_cast ((le_max_right _ _).trans (hN n))
    simp only [Nat.cast_add, Nat.cast_one] at hlarge
    nlinarith

theorem iterated_limits_of_expected_exterior_asymptotic (Zbar : ℝ → ℕ)
    (htail : ExpectedExteriorAsymptotic Zbar)
    (Ψ : ∀ N : ℕ, Wavefunction (N + 1))
    (hΨ : ∀ N, IsNormalizedGroundState (N+1) (Ψ N)) :
    Tendsto (fun m : ℕ => (((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) : EReal) * upperRadius Ψ m)
      atTop (𝓝 (bTF : EReal)) ∧
    Tendsto (fun m : ℕ => (((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) : EReal) * lowerRadius Ψ m)
      atTop (𝓝 (bTF : EReal)) := by
  have huniform : ∀ a : ℝ, 0 < a → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m : ℕ in atTop, ∀ N, radiusChargeThreshold Zbar m ≤ N →
      ∀ ψ : Wavefunction (N+1), IsNormalizedGroundState (N+1) ψ →
        |exteriorMass ψ (a / (m : ℝ)^(1/3 : ℝ)) / m - bTF^ (3 : ℕ) / a^ (3 : ℕ)| < ε := by
    intro a ha
    apply uniform_threshold_of_sequential
      (fun N ψ => IsNormalizedGroundState (N+1) ψ)
      (radiusChargeThreshold Zbar)
      (fun m N ψ => exteriorMass ψ (a / (m : ℝ)^(1/3 : ℝ)) / m)
      (bTF^ (3 : ℕ) / a^ (3 : ℕ))
    intro m N hm hN ψ hψ
    have ht := htail _ _ (radius_scales_admissible Zbar m N hm hN) ψ hψ a ha
    simpa only [normalized_tail_scale] using ht
  apply iterated_limits_of_radius_brackets Ψ
  intro l u hl hlb hbu
  have hu : 0 < u := bTF_pos.trans hbu
  have cl : 1 < bTF^ (3 : ℕ) / l^ (3 : ℕ) :=
    (one_lt_div₀ (pow_pos hl 3)).mpr (pow_lt_pow_left₀ hlb hl.le (by decide))
  have cu : bTF^ (3 : ℕ) / u^ (3 : ℕ) < 1 :=
    (div_lt_one (pow_pos hu 3)).mpr (pow_lt_pow_left₀ hbu bTF_pos.le (by decide))
  filter_upwards [huniform l hl ((bTF^ (3 : ℕ) / l^ (3 : ℕ) - 1)/2) (by linarith),
    huniform u hu ((1 - bTF^ (3 : ℕ) / u^ (3 : ℕ))/2) (by linarith),
    eventually_gt_atTop (0 : ℕ)] with m hml hmu hm
  filter_upwards [eventually_ge_atTop (radiusChargeThreshold Zbar m)] with N hN
  have hmp : 0 < (m : ℝ) := by exact_mod_cast hm
  have hc : 0 < (m : ℝ)^(1/3 : ℝ) := Real.rpow_pos_of_pos hmp _
  have hL := (abs_lt.mp (hml N hN (Ψ N) (hΨ N))).1
  have hU := (abs_lt.mp (hmu N hN (Ψ N) (hΨ N))).2
  have hL' : (m : ℝ) < exteriorMass (Ψ N) (l / (m : ℝ)^(1/3 : ℝ)) :=
    (one_lt_div₀ hmp).mp (by linarith)
  have hU' : exteriorMass (Ψ N) (u / (m : ℝ)^(1/3 : ℝ)) < (m : ℝ) :=
    (div_lt_one hmp).mp (by linarith)
  obtain ⟨g, hdom, _, _⟩ := hΨ N
  obtain ⟨hlo, hup⟩ := radius_bracket hdom.2.2.1 hL' (by positivity) hU'.le
  exact ⟨by simpa [mul_comm] using (div_le_iff₀ hc).mp hlo,
    by simpa [mul_comm] using (le_div_iff₀ hc).mp hup⟩

theorem rawExpectation_count_le_l2 {N : ℕ} {ψ : Wavefunction (N+1)}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ = 1)
    {S : Set Position} (hS : MeasurableSet S) :
    rawExpectation ψ (rawCount S) ≤
      Real.sqrt (rawExpectation ψ (fun x => (rawCount S x)^2)) := by
  have := rawLaw_isProbability hψ hn
  have h := exceptional_event_bound (rawCount_memLp hψ hn hS)
    (Eventually.of_forall (rawCount_nonneg S)) MeasurableSet.univ
  simpa only [setIntegral_univ, probReal_univ, Real.sqrt_one, mul_one,
    integral_rawLaw hψ] using h

theorem small_shell_bounds_of_count_control (hcount : UniformGroundStateCountControl) :
    ∃ (A B : ℝ) (Z₀ : ℕ), 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (N : ℕ) (ψ : Wavefunction (N+1)), Z₀ ≤ N+1 →
      IsNormalizedGroundState (N+1) ψ →
      exteriorMass ψ 1 ≤ B ∧ ∀ r : ℝ, 0 < r → r < 1 →
        exteriorMass ψ r - exteriorMass ψ (2*r) ≤ A/r^3 := by
  obtain ⟨D, Z₀, hD, hann, C₀, hC₀, h₀⟩ := hcount
  obtain ⟨C, hC, hCbound⟩ := hann 1 2 (by norm_num) (by norm_num)
  refine ⟨C*(1+Real.sqrt D), C₀*(1+Real.sqrt D), Z₀, by positivity, by positivity, ?_⟩
  intro N ψ hZ hψ
  refine ⟨h₀ N ψ hZ hψ, ?_⟩
  intro r hr hr1
  obtain ⟨g, hdom, hnorm, _⟩ := hψ
  have hbound := hCbound N ψ hZ ⟨g, hdom, hnorm, by assumption⟩ r hr
  have hmean := rawExpectation_count_le_l2 hdom.2.2.1 hnorm
    (measurableSet_spatialAnnulus (a := r) (b := 2*r))
  have hmean' : exteriorMass ψ r - exteriorMass ψ (2*r) ≤
      C * (max (r^3)⁻¹ 1 + Real.sqrt (D*r)) := by
    rw [exteriorMass_sub hdom.2.2.1 (by linarith),
      ← rawExpectation_count_eq_density hdom.1 hdom.2.2.1 (measurableSet_spatialAnnulus _ _)]
    exact hmean.trans (by simpa only [one_mul, spatialAnnulus] using hbound)
  have hr3 : 0 < r^3 := by positivity
  have hr3le : r^3 ≤ 1 := pow_le_one₀ hr.le hr1.le
  have hinv : 1 ≤ (r^3)⁻¹ := (one_le_inv₀ hr3).mpr hr3le
  have hsqrt : Real.sqrt (D*r) ≤ Real.sqrt D :=
    Real.sqrt_le_sqrt (mul_le_of_le_one_right hD hr1.le)
  calc
    exteriorMass ψ r - exteriorMass ψ (2*r) ≤
        C*((r^3)⁻¹ + Real.sqrt D) := by
      apply hmean'.trans
      rw [max_eq_left hinv]
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hsqrt) hC
    _ ≤ C*((r^3)⁻¹ + Real.sqrt D*(r^3)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact add_le_add le_rfl (le_mul_of_one_le_right (Real.sqrt_nonneg D) hinv)
    _ = (C*(1+Real.sqrt D))/r^3 := by ring

theorem scaled_dyadic_tail_bound {T : ℝ → ℝ} {A B s M : ℝ} (hA : 0 ≤ A)
    (hT : Antitone T) (hB : T 1 ≤ B)
    (hshell : ∀ r : ℝ, 0 < r → r < 1 → T r - T (2*r) ≤ A/r^3)
    (hs : 0 < s) (hM : 0 < M) :
    s^3*T (M*s) ≤ ((8/7 : ℝ)*A)/M^3 + B*s^3 := by
  have h := mul_le_mul_of_nonneg_left
    (dyadic_tail_bound hA hT hB hshell (mul_pos hM hs)) (pow_nonneg hs.le 3)
  calc
    s^3*T (M*s) ≤ s^3*(((8/7:ℝ)*A)/(M*s)^3+B) := h
    _ = _ := by field_simp

theorem tails_converge_of_annuli {T : ℕ → ℝ → ℝ} {β : ℕ → ℝ} {C D a : ℝ}
    (hC : 0 ≤ C) (ha : 0 < a) (hβ : Tendsto β atTop (𝓝 0))
    (hT : ∀ n r, 0 ≤ T n r)
    (hbound : ∀ M : ℝ, 0 < M → ∀ᶠ n in atTop, T n M ≤ D/M^3 + β n)
    (hann : ∀ M : ℝ, a < M →
      Tendsto (fun n => T n a - T n M) atTop (𝓝 (C/a^3-C/M^3))) :
    Tendsto (fun n => T n a) atTop (𝓝 (C/a^3)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall : Tendsto (fun M : ℝ => (C+D)/M^3) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by decide : 3 ≠ 0))
  obtain ⟨M, hlarge, hMsmall⟩ := ((eventually_gt_atTop a).and
    (hsmall.eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/3)))).exists
  have hM : 0 < M := ha.trans hlarge
  have hann' := (Metric.tendsto_nhds.mp (hann M hlarge)) (ε/3) (by positivity)
  have hβ' := hβ.eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/3))
  filter_upwards [hann', hβ', hbound M hM] with n hn hβn hbn
  rw [Real.dist_eq] at hn ⊢
  have hsplit : |T n a - C/a^3| ≤
      |(T n a-T n M)-(C/a^3-C/M^3)| + T n M + C/M^3 := by
    have hh := abs_add_le ((T n a-T n M)-(C/a^3-C/M^3)) (T n M-C/M^3)
    have hh' := abs_sub (T n M) (C/M^3)
    rw [abs_of_nonneg (hT n M), abs_of_nonneg (div_nonneg hC (pow_nonneg hM.le 3))] at hh'
    have hid : ((T n a-T n M)-(C/a^3-C/M^3)) + (T n M-C/M^3) =
        T n a-C/a^3 := by ring
    rw [hid] at hh
    linarith
  have hcoeff : C/M^3+D/M^3 = (C+D)/M^3 := by ring
  linarith

end NeutralAtom
end

end
end

end OAI
