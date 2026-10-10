import Mathlib
import OAI.Analysis.CoulombRadii.Variational.ConfigurationDensity

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

theorem rawExpectation_perm {n : ℕ} {ψ : Wavefunction n}
    (hψ : IsAntisymmetric ψ) (p : Equiv.Perm (Fin n)) (F : Configuration n → ℝ) :
    rawExpectation ψ (fun x => F (x ∘ p)) = rawExpectation ψ F := by
  unfold rawExpectation
  calc
    (∫ x, F (x ∘ p) * configurationDensity ψ x) =
        ∫ x, F (x ∘ p) * configurationDensity ψ (x ∘ p) := by
      apply integral_congr_ae
      filter_upwards [configurationDensity_perm hψ p] with x hx
      rw [hx]
    _ = ∫ x, F x * configurationDensity ψ x := by
      have hi := (volume_measurePreserving_piCongrLeft
        (fun _ : Fin n => Position) p.symm).integral_comp'
        (fun x => F x * configurationDensity ψ x)
      simpa only [MeasurableEquiv.coe_piCongrLeft, piCongrLeft_perm] using hi

theorem integrable_siteWeight {n : ℕ} {f : Configuration n → ℝ}
    (hf : Integrable f) {S : Set Position} (hS : MeasurableSet S) (i : Fin n) :
    Integrable (fun x : Configuration n => S.indicator (fun _ => (1 : ℝ)) (x i) * f x) := by
  have hi := hf.indicator (hS.preimage (measurable_pi_apply i))
  have heq : (fun x : Configuration n => S.indicator (fun _ => (1 : ℝ)) (x i) * f x) =
      ((fun x : Configuration n => x i) ⁻¹' S).indicator f := by
    funext x
    by_cases hx : x i ∈ S <;> simp [hx]
  rw [heq]
  exact hi

theorem rawExpectation_site {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hψ : IsAntisymmetric ψ) (S : Set Position) (i : Fin (N + 1)) :
    rawExpectation ψ (fun x => S.indicator (fun _ => (1 : ℝ)) (x i)) =
      rawExpectation ψ (fun x => S.indicator (fun _ => (1 : ℝ)) (x 0)) := by
  have hp := rawExpectation_perm hψ (Equiv.swap 0 i)
    (fun x => S.indicator (fun _ => (1 : ℝ)) (x 0))
  simpa only [Function.comp_apply, Equiv.swap_apply_left] using hp

theorem rawExpectation_count_factor {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hanti : IsAntisymmetric ψ) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    {S : Set Position} (hS : MeasurableSet S) :
    rawExpectation ψ (rawCount S) =
      (N + 1 : ℝ) * rawExpectation ψ (fun x => S.indicator (fun _ => (1 : ℝ)) (x 0)) := by
  have hi := integrable_siteWeight (integrable_configurationDensity hψ) hS
  calc
    rawExpectation ψ (rawCount S) = ∑ i : Fin (N + 1),
        rawExpectation ψ (fun x => S.indicator (fun _ => (1 : ℝ)) (x i)) := by
      unfold rawExpectation rawCount
      simp_rw [Finset.sum_mul]
      exact integral_finsetSum _ fun i _ => hi i
    _ = ∑ _i : Fin (N + 1),
        rawExpectation ψ (fun x => S.indicator (fun _ => (1 : ℝ)) (x 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact rawExpectation_site hanti S i
    _ = _ := by simp

theorem density_integral_eq_first_site {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) {S : Set Position} (hS : MeasurableSet S) :
    (∫ x in S, density ψ x) =
      (N + 1 : ℝ) * rawExpectation ψ (fun x => S.indicator (fun _ => (1 : ℝ)) (x 0)) := by
  have hw (σ : Spins (N + 1)) := integrable_siteWeight
    (hψ σ).norm.integrable_sq hS (0 : Fin (N + 1))
  have hinn (σ : Spins (N + 1)) :
      Integrable (fun x : Position => ∫ y : Configuration N, ‖ψ σ (Fin.cons x y)‖ ^ 2) :=
    (integrable_cons (hψ σ).norm.integrable_sq).integral_prod_left
  unfold density rawExpectation configurationDensity
  rw [integral_const_mul, integral_finsetSum _ (fun σ _ => (hinn σ).integrableOn)]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun σ _ => hw σ), ← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  calc
    (∫ x in S, ∫ y : Configuration N, ‖ψ σ (Fin.cons x y)‖ ^ 2) =
        ∫ x, S.indicator (fun x => ∫ y : Configuration N, ‖ψ σ (Fin.cons x y)‖ ^ 2) x :=
      (integral_indicator hS).symm
    _ = ∫ x : Position, ∫ y : Configuration N,
        S.indicator (fun _ => (1 : ℝ)) x * ‖ψ σ (Fin.cons x y)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ S <;> simp [hx]
    _ = _ := by simpa only [Fin.cons_zero] using integral_cons (hw σ)

theorem rawExpectation_count_eq_density {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hanti : IsAntisymmetric ψ) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    {S : Set Position} (hS : MeasurableSet S) :
    rawExpectation ψ (rawCount S) = ∫ x in S, density ψ x := by
  rw [rawExpectation_count_factor hanti hψ hS, density_integral_eq_first_site hψ hS]

theorem exceptional_event_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y : Ω → ℝ}
    (hY : MemLp Y 2 μ) (hY0 : 0 ≤ᵐ[μ] Y)
    {S : Set Ω} (hS : MeasurableSet S) :
    (∫ z in S, Y z ∂μ) ≤
      Real.sqrt (∫ z, Y z ^ 2 ∂μ) * Real.sqrt (μ.real S) := by
  let χ : Ω → ℝ := S.indicator (fun _ => 1)
  have hχ0 : 0 ≤ᵐ[μ] χ := Filter.Eventually.of_forall fun z => by
    by_cases hz : z ∈ S <;> simp [χ, hz]
  have hχ : MemLp χ (ENNReal.ofReal 2) μ := by
    simpa [χ] using (memLp_const (1 : ℝ) (p := 2) (μ := μ)).indicator hS
  have hY' : MemLp Y (ENNReal.ofReal 2) μ := by simpa using hY
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    hY0 hχ0 hY' hχ
  have heq : (fun z => Y z * χ z) = S.indicator Y := by
    funext z
    by_cases hz : z ∈ S <;> simp [χ, hz]
  have hχsq : (fun z => χ z ^ (2 : ℝ)) = χ := by
    funext z
    by_cases hz : z ∈ S <;> simp [χ, hz]
  rw [heq, integral_indicator hS, hχsq] at h
  simpa only [χ, Real.rpow_two, integral_indicator hS, setIntegral_const,
    smul_eq_mul, mul_one, ← Real.sqrt_eq_rpow] using h

theorem expectation_error_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : MemLp Y 2 μ) (hY0 : 0 ≤ᵐ[μ] Y)
    {G : Set Ω} (hG : MeasurableSet G) {δ C L : ℝ}
    (hδ : 0 ≤ δ) (hgood : ∀ z ∈ G, |Y z - L| ≤ δ)
    (hL2 : Real.sqrt (∫ z, Y z ^ 2 ∂μ) ≤ C) :
    |(∫ z, Y z ∂μ) - L| ≤ δ + C * Real.sqrt (μ.real Gᶜ) + |L| * μ.real Gᶜ := by
  have hi : Integrable Y μ := hY.integrable (by norm_num)
  have heq : (∫ z, Y z ∂μ) - L =
      (∫ z in G, Y z - L ∂μ) + ((∫ z in Gᶜ, Y z ∂μ) - μ.real Gᶜ * L) := by
    have hsplit := integral_add_compl hG (hi.sub (integrable_const L))
    simp only [Pi.sub_apply] at hsplit
    rw [integral_sub hi (integrable_const L), integral_const] at hsplit
    rw [integral_sub (μ := μ.restrict Gᶜ) hi.integrableOn (integrable_const L),
      setIntegral_const] at hsplit
    simpa [smul_eq_mul] using hsplit.symm
  have hA : |∫ z in G, Y z - L ∂μ| ≤ δ := by
    have h := norm_setIntegral_le_of_norm_le_const (f := fun z => Y z - L) (C := δ)
      (measure_lt_top μ G)
      (fun z hz => by simpa only [Real.norm_eq_abs] using hgood z hz)
    calc
      _ ≤ δ * μ.real G := by simpa only [Real.norm_eq_abs] using h
      _ ≤ δ := by nlinarith [measureReal_le_one (μ := μ) (s := G)]
  have hB0 : 0 ≤ ∫ z in Gᶜ, Y z ∂μ := integral_nonneg_of_ae (ae_restrict_of_ae hY0)
  have hB : (∫ z in Gᶜ, Y z ∂μ) ≤ C * Real.sqrt (μ.real Gᶜ) :=
    (exceptional_event_bound hY hY0 hG.compl).trans
      (mul_le_mul_of_nonneg_right hL2 (Real.sqrt_nonneg _))
  rw [heq]
  calc
    _ ≤ |∫ z in G, Y z - L ∂μ| +
        |(∫ z in Gᶜ, Y z ∂μ) - μ.real Gᶜ * L| := abs_add_le _ _
    _ ≤ |∫ z in G, Y z - L ∂μ| +
        (|∫ z in Gᶜ, Y z ∂μ| + |μ.real Gᶜ * L|) :=
      add_le_add le_rfl (abs_sub _ _)
    _ = |∫ z in G, Y z - L ∂μ| +
        ((∫ z in Gᶜ, Y z ∂μ) + μ.real Gᶜ * |L|) := by
      rw [abs_of_nonneg hB0, abs_mul, abs_of_nonneg measureReal_nonneg]
    _ ≤ _ := by linarith

theorem expectation_tendsto_of_good_events {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (Y : ∀ n, Ω n → ℝ)
    (G : ∀ n, Set (Ω n)) (δ : ℕ → ℝ) {C L : ℝ}
    (hY : ∀ n, MemLp (Y n) 2 (μ n)) (hY0 : ∀ n, 0 ≤ᵐ[μ n] Y n)
    (hG : ∀ n, MeasurableSet (G n)) (hδ0 : ∀ n, 0 ≤ δ n)
    (hgood : ∀ n z, z ∈ G n → |Y n z - L| ≤ δ n)
    (hL2 : ∀ n, Real.sqrt (∫ z, Y n z ^ 2 ∂μ n) ≤ C)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hbad : Tendsto (fun n => (μ n).real (G n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, Y n z ∂μ n) atTop (𝓝 L) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ => abs_nonneg _)
    (fun n => expectation_error_bound (hY n) (hY0 n) (hG n) (hδ0 n) (hgood n) (hL2 n))
  have hs : Tendsto (fun n => Real.sqrt ((μ n).real (G n)ᶜ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hbad
  simpa only [mul_zero, add_zero] using (hδ.add (hs.const_mul C)).add (hbad.const_mul |L|)

theorem rawCount_nonneg {n : ℕ} (S : Set Position) (x : Configuration n) :
    0 ≤ rawCount S x := by
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : x i ∈ S <;> simp [hi]

theorem rawCount_le_number {n : ℕ} (S : Set Position) (x : Configuration n) :
    rawCount S x ≤ n := by
  calc
    rawCount S x ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : x i ∈ S <;> simp [hi]
    _ = n := by simp

theorem measurable_rawCount {n : ℕ} {S : Set Position} (hS : MeasurableSet S) :
    Measurable (rawCount (n := n) S) := by
  apply Finset.measurable_sum
  intro i _
  exact (measurable_const.indicator hS).comp (measurable_pi_apply i)

theorem integrable_count_squared_weight {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) {S : Set Position} (hS : MeasurableSet S) :
    Integrable (fun x : Configuration n => (rawCount S x) ^ 2 * configurationDensity ψ x) := by
  have hq := integrable_configurationDensity hψ
  refine (hq.const_mul ((n : ℝ) ^ 2)).mono' ?_ ?_
  · exact (measurable_rawCount hS).pow_const 2 |>.aestronglyMeasurable.mul
      hq.aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (sq_nonneg _) (configurationDensity_nonneg ψ x))]
    apply mul_le_mul_of_nonneg_right _ (configurationDensity_nonneg ψ x)
    exact pow_le_pow_left₀ (rawCount_nonneg S x) (rawCount_le_number S x) 2

theorem rawExpectation_count_squared_le {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) {S : Set Position} (hS : MeasurableSet S) :
    rawExpectation ψ (fun x => (rawCount S x) ^ 2) ≤ (n : ℝ) ^ 2 * normSquared ψ := by
  calc
    _ ≤ ∫ x : Configuration n, (n : ℝ) ^ 2 * configurationDensity ψ x := by
      apply integral_mono (integrable_count_squared_weight hψ hS)
        ((integrable_configurationDensity hψ).const_mul _)
      intro x
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (rawCount_nonneg S x) (rawCount_le_number S x) 2)
        (configurationDensity_nonneg ψ x)
    _ = _ := by rw [integral_const_mul, integral_configurationDensity hψ]

theorem normalized_count_l2_le_number {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ = 1)
    {S : Set Position} (hS : MeasurableSet S) :
    Real.sqrt (rawExpectation ψ (fun x => (rawCount S x) ^ 2)) ≤ n := by
  have h := rawExpectation_count_squared_le hψ hS
  rw [hn, mul_one] at h
  calc
    _ ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt h
    _ = n := Real.sqrt_sq (by positivity)

def UniformGroundStateCountControl : Prop :=
  ∃ (D : ℝ) (Z₀ : ℕ), 0 ≤ D ∧
    (∀ α β : ℝ, 0 < α → α < β → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (ψ : Wavefunction (N + 1)), Z₀ ≤ N + 1 →
        IsNormalizedGroundState (N + 1) ψ → ∀ u : ℝ, 0 < u →
        Real.sqrt (rawExpectation ψ (fun x =>
          (rawCount {y : Position | α * u < ‖y‖ ∧ ‖y‖ < β * u} x) ^ 2)) ≤
          C * (max (u ^ 3)⁻¹ 1 + Real.sqrt (D * u))) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (ψ : Wavefunction (N + 1)), Z₀ ≤ N + 1 →
      IsNormalizedGroundState (N + 1) ψ → exteriorMass ψ 1 ≤ C * (1 + Real.sqrt D))

def rawLaw {n : ℕ} (ψ : Wavefunction n) : Measure (Configuration n) :=
  volume.withDensity (fun x => ENNReal.ofReal (configurationDensity ψ x))

theorem integral_rawLaw {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (F : Configuration n → ℝ) :
    (∫ x, F x ∂rawLaw ψ) = rawExpectation ψ F := by
  have hq := (integrable_configurationDensity hψ).aemeasurable.ennreal_ofReal
  have hqtop : ∀ᵐ x : Configuration n ∂volume,
      ENNReal.ofReal (configurationDensity ψ x) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hi := integral_withDensity_eq_integral_toReal_smul₀ hq hqtop F
  simpa only [rawLaw, rawExpectation, ENNReal.toReal_ofReal (configurationDensity_nonneg ψ _),
    smul_eq_mul, mul_comm] using hi

theorem rawLaw_isProbability {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ = 1) :
    IsProbabilityMeasure (rawLaw ψ) := by
  apply isProbabilityMeasure_iff_real.mpr
  have h := integral_rawLaw hψ (fun _ => 1)
  simpa [integral_const, rawExpectation, integral_configurationDensity hψ, hn] using h

theorem rawCount_memLp {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ = 1)
    {S : Set Position} (hS : MeasurableSet S) :
    MemLp (rawCount (n := n) S) 2 (rawLaw ψ) := by
  have := rawLaw_isProbability hψ hn
  apply MemLp.of_bound (measurable_rawCount hS).aestronglyMeasurable (n : ℝ)
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (rawCount_nonneg S x)] using rawCount_le_number S x

theorem rawExpectation_sphere_eq_zero {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hanti : IsAntisymmetric ψ) (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (r : ℝ) :
    rawExpectation ψ (rawCount (Metric.sphere (0 : Position) r)) = 0 := by
  rw [rawExpectation_count_eq_density hanti hψ Metric.isClosed_sphere.measurableSet]
  exact setIntegral_measure_zero _ (Measure.addHaar_sphere volume _ _)

def packetExponent : ℝ := 1 / 100000

def packetWidth (c₁ r₀ s : ℝ) (z : Position) : ℝ :=
  c₁ * max ‖z‖ r₀ * (min (max ‖z‖ r₀) s) ^ packetExponent

def packetKernel (g : Position → ℝ) (c₁ r₀ s : ℝ) (z y : Position) : ℝ :=
  (packetWidth c₁ r₀ s z ^ 3)⁻¹ *
    (g ((packetWidth c₁ r₀ s z)⁻¹ • (y - z))) ^ 2

theorem packetWidth_pos {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) (z : Position) : 0 < packetWidth c₁ r₀ s z := by
  unfold packetWidth
  have hmax : 0 < max ‖z‖ r₀ := lt_of_lt_of_le hr (le_max_right _ _)
  exact mul_pos (mul_pos hc hmax) (Real.rpow_pos_of_pos (lt_min hmax hs) _)

theorem packetKernel_eq_wavepacket_sq (g : Position → ℝ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z y : Position) :
    packetKernel g c₁ r₀ s z y =
      ((packetWidth c₁ r₀ s z) ^ (-(3 / 2 : ℝ)) *
        g ((packetWidth c₁ r₀ s z)⁻¹ • (y-z))) ^ 2 := by
  have ht := (packetWidth_pos hc hr hs z).le
  rw [mul_pow]
  unfold packetKernel
  congr 1
  rw [← Real.rpow_natCast (_ ^ (-(3 / 2 : ℝ))) 2, ← Real.rpow_mul ht]
  norm_num

theorem packetKernel_nonneg (g : Position → ℝ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z y : Position) :
    0 ≤ packetKernel g c₁ r₀ s z y := by
  rw [packetKernel_eq_wavepacket_sq g hc hr hs]
  positivity

theorem integral_packetKernel (g : Position → ℝ) (hg : (∫ y, g y ^ 2) = 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z : Position) :
    (∫ y, packetKernel g c₁ r₀ s z y) = 1 := by
  have ht := packetWidth_pos hc hr hs z
  unfold packetKernel
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun y : Position => (g ((packetWidth c₁ r₀ s z)⁻¹ • y)) ^ 2)]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun y : Position => g y ^ 2) ht.le]
  simp only [Position, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, hg, mul_one]
  exact inv_mul_cancel₀ (pow_ne_zero _ ht.ne')

theorem integrable_packetKernel (g : Position → ℝ) (hg : (∫ y, g y ^ 2) = 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z : Position) :
    Integrable (packetKernel g c₁ r₀ s z) := by
  by_contra hnot
  have hzero := integral_undef hnot
  rw [integral_packetKernel g hg hc hr hs z] at hzero
  exact one_ne_zero hzero

theorem packetKernel_support (g : Position → ℝ)
    (hg : ∀ x, 1 < ‖x‖ → g x = 0) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z y : Position)
    (hK : packetKernel g c₁ r₀ s z y ≠ 0) :
    ‖y-z‖ ≤ packetWidth c₁ r₀ s z := by
  have ht := packetWidth_pos hc hr hs z
  by_contra! hlt
  have harg : 1 < ‖(packetWidth c₁ r₀ s z)⁻¹ • (y-z)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    have : 1 < ‖y-z‖ / packetWidth c₁ r₀ s z := (lt_div_iff₀ ht).mpr (by simpa using hlt)
    simpa only [one_mul, div_eq_mul_inv, mul_comm] using this
  exact hK (by simp [packetKernel, hg _ harg])

theorem packetWidth_le (c₁ r₀ s : ℝ) (hc : 0 ≤ c₁) (_hr : 0 < r₀)
    (hs : 0 < s) (z : Position) :
    packetWidth c₁ r₀ s z ≤ (c₁ * s ^ packetExponent) * max ‖z‖ r₀ := by
  unfold packetWidth
  calc
    c₁ * max ‖z‖ r₀ * min (max ‖z‖ r₀) s ^ packetExponent
      ≤ c₁ * max ‖z‖ r₀ * s ^ packetExponent := by
        apply mul_le_mul_of_nonneg_left
        · exact Real.rpow_le_rpow (le_min (le_max_of_le_left (norm_nonneg _)) hs.le)
            (min_le_right _ _) (by norm_num [packetExponent])
        · exact mul_nonneg hc (le_max_of_le_left (norm_nonneg _))
    _ = (c₁ * s ^ packetExponent) * max ‖z‖ r₀ := by ring

theorem packetKernel_relative_support (g : Position → ℝ)
    (hg : ∀ x, 1 < ‖x‖ → g x = 0) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z y : Position)
    (hz : r₀ ≤ ‖z‖) (hK : packetKernel g c₁ r₀ s z y ≠ 0) :
    (1-c₁*s^packetExponent)*‖z‖ ≤ ‖y‖ ∧
      ‖y‖ ≤ (1+c₁*s^packetExponent)*‖z‖ := by
  have hd := (packetKernel_support g hg hc hr hs z y hK).trans
    (packetWidth_le c₁ r₀ s hc.le hr hs z)
  rw [max_eq_left hz] at hd
  have hn₁ := norm_sub_norm_le y z
  have hn₂ := norm_sub_norm_le z y
  rw [norm_sub_rev z y] at hn₂
  constructor <;> nlinarith

theorem packetKernel_clamped_support (g : Position → ℝ)
    (hg : ∀ x, 1 < ‖x‖ → g x = 0) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z y : Position)
    (hz : ‖z‖ ≤ r₀) (hK : packetKernel g c₁ r₀ s z y ≠ 0) :
    ‖y‖ ≤ (1+c₁*s^packetExponent)*r₀ := by
  have hd := (packetKernel_support g hg hc hr hs z y hK).trans
    (packetWidth_le c₁ r₀ s hc.le hr hs z)
  rw [max_eq_right hz] at hd
  have hn := norm_sub_norm_le y z
  nlinarith

def packetMass {n : ℕ} (g : Position → ℝ) (c₁ r₀ s : ℝ)
    (S : Set Position) (x : Configuration n) : ℝ :=
  ∑ i, ∫ y in S, packetKernel g c₁ r₀ s (x i) y

theorem packetMass_nonneg {n : ℕ} (g : Position → ℝ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (S : Set Position) (x : Configuration n) : 0 ≤ packetMass g c₁ r₀ s S x := by
  exact Finset.sum_nonneg fun i _ => integral_nonneg fun y =>
    packetKernel_nonneg g hc hr hs (x i) y

theorem packetMass_le_rawCount {n : ℕ} (g : Position → ℝ)
    (hg : (∫ y, g y ^ 2) = 1) {c₁ r₀ s : ℝ} (hc : 0 < c₁)
    (hr : 0 < r₀) (hs : 0 < s) (S T : Set Position)
    (hST : ∀ z y, y ∈ S → packetKernel g c₁ r₀ s z y ≠ 0 → z ∈ T)
    (x : Configuration n) : packetMass g c₁ r₀ s S x ≤ rawCount T x := by
  classical
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : x i ∈ T
  · simp only [Set.indicator_of_mem hi]
    calc
      (∫ y in S, packetKernel g c₁ r₀ s (x i) y)
        ≤ ∫ y, packetKernel g c₁ r₀ s (x i) y :=
          setIntegral_le_integral (integrable_packetKernel g hg hc hr hs (x i))
            (Filter.Eventually.of_forall (packetKernel_nonneg g hc hr hs (x i)))
      _ = 1 := integral_packetKernel g hg hc hr hs (x i)
  · simp only [Set.indicator_of_notMem hi]
    have hz : (∫ y in S, packetKernel g c₁ r₀ s (x i) y) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun y hy => by
        by_contra hK
        exact hi (hST (x i) y hy hK)
    exact hz.le

end NeutralAtom
end
end
end

end OAI
