import Mathlib
import OAI.Probability.SLE.InverseMoments
import OAI.Probability.SLE.SausagePointBound
import OAI.Probability.SLE.SpatialMeans

namespace OAI

/-! Measure Support for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable def spatialGreenMass (κ : ℝ) (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
    (G : ℝ≥0 → ℂ → ℂ) (r : ℝ) (A : Set ℂ) : ℝ≥0∞ :=
  ∫⁻ z in A, ENNReal.ofReal (spatialGreenWeight κ U γ G z r)

namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

lemma spatialGreenMass_measurable (r : ℝ) (A : Set ℂ) :
    Measurable (fun ω : a.samples => spatialGreenMass κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) r A) :=
  (a.spatialGreenWeight_measurable r).ennreal_ofReal.lintegral_prod_left'

 

lemma spatialGreenMass_expectation [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ8 : κ < 8) (r : ℝ) (hr : 0 < r)
    (A : Set ℂ) (hA : MeasurableSet A) (hheight : ∀ z ∈ A, r ≤ z.im) :
    (∫⁻ ω : a.samples, spatialGreenMass κ (fun t => Real.sqrt κ * a.B t ω)
      (γ ω) (a.G ω) r A ∂(P.comap Subtype.val)) =
      ∫⁻ z in A, ENNReal.ofReal (initialGreen κ z) := by
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  simp only [spatialGreenMass]
  rw [← lintegral_lintegral_swap (a.spatialGreenWeight_measurable r).ennreal_ofReal.aemeasurable]
  apply setLIntegral_congr_fun hA
  intro z hz
  obtain ⟨hi, he⟩ := a.spatialGreen_expectation hκ hκ8 z r hr (hheight z hz)
  change (∫⁻ ω : a.samples, ENNReal.ofReal (spatialGreenWeight κ
    (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r) ∂μ) = ENNReal.ofReal (initialGreen κ z)
  rw [← he]
  exact (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun ω => by
    dsimp only [Pi.zero_apply, spatialGreenWeight]
    split_ifs
    · exact le_rfl
    · exact greenDensity_nonneg (a.witness ω) κ _ z)).symm

 

lemma spatialGreenMass_expectation_le [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ8 : κ < 8) (r : ℝ) (hr : 0 < r)
    (A : Set ℂ) (hA : MeasurableSet A) (hheight : ∀ z ∈ A, r ≤ z.im) :
    (∫⁻ ω : a.samples, spatialGreenMass κ (fun t => Real.sqrt κ * a.B t ω)
      (γ ω) (a.G ω) r A ∂(P.comap Subtype.val)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-codimension κ) * r ^ (-codimension κ)) * volume A := by
  rw [a.spatialGreenMass_expectation hκ hκ8 r hr A hA hheight]
  calc
    _ ≤ ∫⁻ _z in A, ENNReal.ofReal ((2 : ℝ) ^ (-codimension κ) * r ^ (-codimension κ)) := by
      apply setLIntegral_mono' hA
      intro z hz
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (2 : ℝ) ^ (-codimension κ) * z.im ^ (-codimension κ) :=
          initialGreen_le_height κ hκ hκ8 z (hr.trans_le (hheight z hz))
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hr (hheight z hz) (neg_nonpos.mpr (codimension_pos κ hκ8).le))
          (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

end RegularSLEPresentation
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

lemma finite_density_crossing_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P Q : Measure Ω)
    (F : Filtration ℕ mΩ) (B : ℕ → Set Ω)
    (hBm : ∀ n, MeasurableSet[F n] (B n)) (c : ℝ≥0∞)
    (hQ : ∀ n A, MeasurableSet[F n] A → A ⊆ B n → Q A ≤ c * P A)
    (n : ℕ) : Q (⋃ i ∈ Finset.range n, B i) ≤ c * P (⋃ i ∈ Finset.range n, B i) := by
  classical
  let E (n : ℕ) : Set Ω := ⋃ i ∈ Finset.range n, B i
  have hEm (n : ℕ) : MeasurableSet[F n] (E n) := by
    apply MeasurableSet.iUnion
    intro i
    apply MeasurableSet.iUnion
    intro hi
    exact F.mono (Nat.le_of_lt (Finset.mem_range.mp hi)) _ (hBm i)
  have hrec (n : ℕ) : E (n + 1) = E n ∪ (B n \ E n) := by
    calc
      E (n + 1) = B n ∪ E n := by
        ext ω
        simp only [E, Finset.range_add_one, Finset.mem_insert, mem_iUnion, mem_union]
        aesop
      _ = E n ∪ (B n \ E n) := by
        ext ω
        by_cases h : ω ∈ E n <;> simp [h]
  change Q (E n) ≤ c * P (E n)
  induction n with
  | zero => simp [E]
  | succ n ih =>
      have hD := (hBm n).diff (hEm n)
      have hd : Disjoint (E n) (B n \ E n) := disjoint_sdiff_right
      rw [hrec n, measure_union hd (F.le n _ hD), measure_union hd (F.le n _ hD), mul_add]
      exact add_le_add ih (hQ n _ hD sdiff_subset)

lemma finite_density_crossing_bound_of_subset
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P Q : Measure Ω)
    (F : Filtration ℕ mΩ) (B : ℕ → Set Ω)
    (hBm : ∀ n, MeasurableSet[F n] (B n)) (c : ℝ≥0∞)
    (hQ : ∀ n A, MeasurableSet[F n] A → A ⊆ B n → Q A ≤ c * P A)
    (A : Set Ω) (hA : ∀ n, B n ⊆ A) (n : ℕ) :
    Q (⋃ i ∈ Finset.range n, B i) ≤ c * P A := by
  refine (finite_density_crossing_bound P Q F B hBm c hQ n).trans ?_
  exact mul_le_mul (show c ≤ c from le_rfl)
    (show P (⋃ i ∈ Finset.range n, B i) ≤ P A from
      measure_mono (iUnion₂_subset fun i _ => hA i)) bot_le bot_le

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

lemma limitRadiusKernel_pos_iff
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hu : 0 ≤ u)
    (p α : ℝ) (ω : Ω) :
    0 < limitRadiusKernel a p α u ω ↔ localizedRadiusStop a ω < ⊤ := by
  have hx : (∃ n, max u 0 ≤ (a n).clock.S ((a n).τ ω) ω) ↔ ∃ n, ω ∈ (a n).hit := by
    simp only [max_eq_left hu]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, le_antisymm ((a n).clock_upper ω) hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, le_of_eq hn.symm⟩
  by_cases hh : ∃ n, ω ∈ (a n).hit
  · have he := hx.mpr hh
    obtain ⟨n, hn⟩ := hh
    rw [localizedRadiusStop_eq_hit a ω n hn, limitRadiusKernel, dite_eq_left he,
      AngularLocalization.radiusKernel, ite_eq_left (Nat.find_spec he)]
    exact iff_of_true (Real.exp_pos _) (WithTop.coe_lt_top _)
  · rw [localizedRadiusStop_eq_top a ω (not_exists.mp hh), limitRadiusKernel,
      dite_eq_right (fun h => hh (hx.mp h))]
    simp

lemma finiteCenteredLaw_eq_radiusKernel
    {P : Measure Ω} (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω)) :
    finiteCenteredLaw P κ B γ G z u = P.withDensity
      (fun ω => ENNReal.ofReal (limitRadiusKernel a (codimension κ) (greenExponent κ) u ω /
        initialGreen κ z)) := by
  apply withDensity_congr_ae
  filter_upwards [hw] with ω hω
  rw [limitRadiusKernel_eq_stoppedGreen a hε hεlim hBc hz hu ω (γ ω) (G ω) (F ω) hω]

lemma radiusKernel_density_bound
    {P : Measure Ω} (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (δ : ℝ) (A : Set Ω) (hA : MeasurableSet A)
    (hδ : ∀ ω ∈ A, limitRadiusKernel a (codimension κ) (greenExponent κ) u ω ≤ δ) :
    finiteCenteredLaw P κ B γ G z u A ≤ ENNReal.ofReal (δ / initialGreen κ z) * P A := by
  rw [finiteCenteredLaw_eq_radiusKernel a hε hεlim hBc hz hu γ G F hw, withDensity_apply _ hA]
  calc
    _ ≤ ∫⁻ ω in A, ENNReal.ofReal (δ / initialGreen κ z) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with ω hω
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hδ ω hω) (initialGreen_pos κ z hz).le)
    _ = _ := by simp

lemma finiteCenteredLaw_consistent_at_radius
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω)) (hz : z ∈ upperHalfPlane)
    {v : ℝ} (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (b : ∀ n, AngularLocalization B hm κ z v (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hu : 0 ≤ u) (huv : u ≤ v)
    (A : Set Ω) (hA : MeasurableSet[(localizedRadiusStop_stopping a).measurableSpace] A) :
    finiteCenteredLaw P κ B γ G z v A = finiteCenteredLaw P κ B γ G z u A := by
  have hAm := (localizedRadiusStop_stopping a).measurableSpace_le _ hA
  rw [finiteCenteredLaw_apply hB κ hκ hκ8 γ G F hw z hz v (hu.trans huv) A hAm,
    finiteCenteredLaw_apply hB κ hκ hκ8 γ G F hw z hz u hu A hAm,
    finite_stopped_green_consistent_regular hB hBm hBc hB0 hκ hκ8 γ G F hw hz
      a b hεlim hε hu huv A hA]

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma finite_radius_density_crossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    {z : ℂ} (hz : z ∈ upperHalfPlane) {ε : ℕ → ℝ}
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (v U : ℝ≥0) (s : ℕ → ℝ≥0) (hs : Monotone s)
    (hvs : ∀ n, v ≤ s n) (hsU : ∀ n, s n ≤ U) (δ : ℝ) (N : ℕ) :
    finiteCenteredLaw P κ B γ G z U
      (⋃ i ∈ Finset.range N, {ω | 0 < limitRadiusKernel (a (s i)) (codimension κ) (greenExponent κ) (s i) ω ∧
        limitRadiusKernel (a (s i)) (codimension κ) (greenExponent κ) (s i) ω ≤ δ}) ≤
      ENNReal.ofReal (δ / initialGreen κ z) * P {ω | localizedRadiusStop (a v) ω < ⊤} := by
  let K (n : ℕ) := limitRadiusKernel (a (s n)) (codimension κ) (greenExponent κ) (s n)
  let E (n : ℕ) : Set Ω := {ω | 0 < K n ω ∧ K n ω ≤ δ}
  let H : Filtration ℕ mΩ :=
    { seq := fun n => radiusFiltration a (s n)
      mono' := fun n m hnm => (radiusFiltration a).mono (hs hnm)
      le' := fun n => (radiusFiltration a).le (s n) }
  have hKm (n : ℕ) : Measurable[H n] (K n) :=
    limitRadiusKernel_terminal_measurable (a (s n)) hε hBc (s n).coe_nonneg _ _
  have hEm (n : ℕ) : MeasurableSet[H n] (E n) :=
    measurableSet_Ioc.preimage (hKm n)
  apply finite_density_crossing_bound_of_subset P (finiteCenteredLaw P κ B γ G z U)
    H E hEm (ENNReal.ofReal (δ / initialGreen κ z))
  · intro n A hA hAE
    rw [finiteCenteredLaw_consistent_at_radius hB hBm hBc hB0 hκ hκ8 γ G F hw hz
      (a (s n)) (a U) hε hεlim (s n).coe_nonneg (show (s n : ℝ) ≤ U from hsU n) A hA]
    exact radiusKernel_density_bound (a (s n)) hε hεlim hBc hz (s n).coe_nonneg γ G F hw
      δ A (H.le n _ hA) (fun ω hω => (hAE hω).2)
  · intro n ω hω
    have hp := (limitRadiusKernel_pos_iff (a (s n)) (s n).coe_nonneg
      (codimension κ) (greenExponent κ) ω).mp hω.1
    exact lt_of_le_of_lt (localizedRadiusStop_mono (a v) (a (s n))
      (show (v : ℝ) ≤ s n from hvs n) ω) hp

lemma radius_kernel_scale_cancel (κ v w L C : ℝ) (z : ℂ) (hz : z ∈ upperHalfPlane)
    (hL : L ≠ 0) :
    (Real.exp (codimension κ * (w - Real.log 2 - Real.log z.im)) / L / initialGreen κ z) *
      (C * Real.exp (-codimension κ * v) * (Real.sin (Complex.arg z)) ^ greenExponent κ) =
      C * Real.exp (codimension κ * (w - v)) / L := by
  have hI := (initialGreen_pos κ z hz).ne'
  have he : Real.exp (-codimension κ * v) * (Real.sin (Complex.arg z)) ^ greenExponent κ =
      initialGreen κ z / Real.exp (codimension κ * (v - Real.log 2 - Real.log z.im)) :=
    (initialGreen_div_zeroKernel κ v z hz).symm
  rw [mul_assoc C, he]
  rw [show (Real.exp (codimension κ * (w - Real.log 2 - Real.log z.im)) / L / initialGreen κ z) *
      (C * (initialGreen κ z / Real.exp (codimension κ * (v - Real.log 2 - Real.log z.im)))) =
      C * (Real.exp (codimension κ * (w - Real.log 2 - Real.log z.im)) /
        Real.exp (codimension κ * (v - Real.log 2 - Real.log z.im))) / L by
      field_simp]
  rw [← Real.exp_sub]
  congr 2
  ring_nf

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma finite_radius_scaled_crossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    {z : ℂ} (hz : z ∈ upperHalfPlane) {ε : ℕ → ℝ}
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (v U : ℝ≥0) (hv : 1 ≤ (v : ℝ)) (s : ℕ → ℝ≥0) (hs : Monotone s)
    (hvs : ∀ n, v ≤ s n) (hsU : ∀ n, s n ≤ U) (w L : ℝ) (hL : 0 < L) (N : ℕ) :
    finiteCenteredLaw P κ B γ G z U
      (⋃ i ∈ Finset.range N, {ω | 0 < limitRadiusKernel (a (s i)) (codimension κ) (greenExponent κ) (s i) ω ∧
        limitRadiusKernel (a (s i)) (codimension κ) (greenExponent κ) (s i) ω ≤
          Real.exp (codimension κ * (w - Real.log 2 - Real.log z.im)) / L}) ≤
      ENNReal.ofReal (uniformInverseAngleConstant κ 1 * Real.exp (codimension κ * (w - v)) / L) := by
  let C := uniformInverseAngleConstant κ 1
  have hC : 0 < C := uniformInverseAngleConstant_pos κ 1 hκ hκ8 (by norm_num)
  let Kv := Real.exp (codimension κ * ((v : ℝ) - Real.log 2 - Real.log z.im))
  let δ := Real.exp (codimension κ * (w - Real.log 2 - Real.log z.im)) / L
  have hδ : 0 ≤ δ / initialGreen κ z := div_nonneg (div_pos (Real.exp_pos _) hL).le
    (initialGreen_pos κ z hz).le
  have hPe : P {ω | localizedRadiusStop (a v) ω < ⊤} =
      P {ω | radiusLevelTime (γ ω) (G ω) z v < ∞} := by
    apply measure_congr
    filter_upwards [hw] with ω hω
    rw [localizedRadiusStop_eq_source (a v) hεlim hBc hz ω (γ ω) (G ω) (F ω) hω]
    rfl
  have hPr : (P {ω | localizedRadiusStop (a v) ω < ⊤}).toReal ≤ C * initialGreen κ z / Kv := by
    rw [hPe]
    refine (radius_approach_regular hB hBm hBc hB0 κ hκ hκ8 γ G F hw z hz v hv).trans_eq ?_
    dsimp only [C, Kv]
    rw [mul_div_assoc, initialGreen_div_zeroKernel κ v z hz, mul_assoc]
  have hPn : P {ω | localizedRadiusStop (a v) ω < ⊤} ≤ ENNReal.ofReal (C * initialGreen κ z / Kv) :=
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (div_nonneg (mul_nonneg hC.le (initialGreen_pos κ z hz).le) (Real.exp_pos _).le)).mpr hPr
  calc
    _ ≤ ENNReal.ofReal (δ / initialGreen κ z) * P {ω | localizedRadiusStop (a v) ω < ⊤} :=
      finite_radius_density_crossing hB hBm hBc hB0 hκ hκ8 γ G F hw hz a hε hεlim v U s hs hvs hsU δ N
    _ ≤ ENNReal.ofReal (δ / initialGreen κ z) * ENNReal.ofReal (C * initialGreen κ z / Kv) :=
      mul_le_mul le_rfl hPn bot_le bot_le
    _ = ENNReal.ofReal ((δ / initialGreen κ z) * (C * initialGreen κ z / Kv)) :=
      (ENNReal.ofReal_mul hδ).symm
    _ = _ := by
      congr 1
      have he := radius_kernel_scale_cancel κ v w L C z hz hL.ne'
      change (δ / initialGreen κ z) * (C * initialGreen κ z /
        Real.exp (codimension κ * ((v : ℝ) - Real.log 2 - Real.log z.im))) = _
      rw [mul_div_assoc C, initialGreen_div_zeroKernel κ v z hz, ← mul_assoc C]
      exact he

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v : ℝ} {ε : ℕ → ℝ}

lemma limitRadiusKernel_eq_of_surviving_cutoff
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (p α s : ℝ) (hs : 0 ≤ s) (ω : Ω) (n : ℕ)
    (hn : s ≤ (a n).clock.S ((a n).τ ω) ω) :
    limitRadiusKernel a p α s ω = (a n).radiusValue p α s ω := by
  obtain ⟨m, hm, hlim⟩ := ((eventually_ge_atTop n).and (radiusKernel_eventually_limit a hε p α s ω)).exists
  rw [max_eq_left hs] at hlim
  rw [← hlim, ← (a n).radiusKernel_eq_of_live (a m) le_rfl (hε hm) p α s hs ω hn,
    AngularLocalization.radiusKernel, ite_eq_left hn]

lemma limitRadiusKernel_eq_below
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (b : ∀ n, AngularLocalization B hm κ z v (ε n)) (hε : Antitone ε)
    (huv : u ≤ v) (p α s : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u) (ω : Ω) :
    limitRadiusKernel a p α s ω = limitRadiusKernel b p α s ω := by
  obtain ⟨n, hn, hm⟩ := ((radiusKernel_eventually_limit a hε p α s ω).and
    (radiusKernel_eventually_limit b hε p α s ω)).exists
  rw [max_eq_left hs] at hn hm
  rw [← hn, ← hm]
  exact (a n).radiusKernel_eq_below (b n) huv p α s hs hsu ω

lemma exists_cutoff_of_radiusStop_lt_top
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (ω : Ω)
    (hω : localizedRadiusStop a ω < ⊤) : ∃ n, ω ∈ (a n).hit := by
  by_contra hn
  rw [localizedRadiusStop_eq_top a ω (not_exists.mp hn)] at hω
  exact lt_irrefl _ hω

lemma limitRadiusKernel_continuousOn_of_live
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (p α : ℝ) (ω : Ω)
    (hω : localizedRadiusStop a ω < ⊤) :
    ContinuousOn (fun s => limitRadiusKernel a p α s ω) (Icc 0 u) := by
  obtain ⟨n, hn⟩ := exists_cutoff_of_radiusStop_lt_top a ω hω
  apply ((a n).radiusValue_continuous hBc p α ω).continuousOn.congr
  intro s hs
  exact limitRadiusKernel_eq_of_surviving_cutoff a hε p α s hs.1 ω n (hs.2.trans_eq hn.symm)

lemma limitRadiusKernel_pos_of_live
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (p α s : ℝ) (hs : s ∈ Icc 0 u) (ω : Ω) (hω : localizedRadiusStop a ω < ⊤) :
    0 < limitRadiusKernel a p α s ω := by
  obtain ⟨n, hn⟩ := exists_cutoff_of_radiusStop_lt_top a ω hω
  rw [limitRadiusKernel_eq_of_surviving_cutoff a hε p α s hs.1 ω n (hs.2.trans_eq hn.symm)]
  exact powerLogDensity_pos _ _ _ _ _

lemma radius_limit_clock_angle
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (p α s : ℝ) (hs : s ∈ Icc 0 u) (ω : Ω) (hω : localizedRadiusStop a ω < ⊤) :
    limitRadiusKernel a p α s ω = Real.exp (p * (s - Real.log 2 - Real.log z.im)) *
      (limitRadiusKernel a 0 2 s ω) ^ (α / 2) := by
  obtain ⟨n, hn⟩ := exists_cutoff_of_radiusStop_lt_top a ω hω
  have hs' : s ≤ (a n).clock.S ((a n).τ ω) ω := hs.2.trans_eq hn.symm
  rw [limitRadiusKernel_eq_of_surviving_cutoff a hε p α s hs.1 ω n hs',
    limitRadiusKernel_eq_of_surviving_cutoff a hε 0 2 s hs.1 ω n hs']
  unfold AngularLocalization.radiusValue
  rw [powerLogDensity_radius_angle κ p α (Real.log z.im),
    powerLogDensity_radius_angle κ 0 2 (Real.log z.im)]
  norm_num only [zero_mul, Real.exp_zero, one_mul, div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one]
  have he := (a n).clock.clock_inverse s ω
  change (a n).clock.S ((a n).clock.inverse s ω) ω =
    min (max s 0) ((a n).clock.S ((a n).τ ω) ω) at he
  rw [max_eq_left hs.1, min_eq_left hs'] at he
  change logRadiusClock (Real.log z.im)
    ((a n).solution.Q ((a n).clock.inverse s ω) ω) = s at he
  rw [he]

end SLEExactGauge
end

 
section

open Set MeasureTheory Classical
open scoped ENNReal
namespace SLEExactGauge

lemma finite_grid_from_monotone
    {Ω T : Type*} [MeasurableSpace Ω] [LinearOrder T]
    (Q : Measure Ω) (E : T → Set Ω) (v U : T) (hvU : v ≤ U) (c : ℝ≥0∞)
    (h : ∀ s : ℕ → T, Monotone s → (∀ n, v ≤ s n) → (∀ n, s n ≤ U) →
      ∀ N, Q (⋃ i ∈ Finset.range N, E (s i)) ≤ c)
    (t : Finset T) (ht : ∀ x ∈ t, x ∈ Icc v U) :
    Q (⋃ x ∈ t, E x) ≤ c := by
  let f := t.orderEmbOfFin rfl
  let s (n : ℕ) : T := if hn : n < t.card then f ⟨n, hn⟩ else U
  have hmem (i : Fin t.card) : f i ∈ t := t.orderEmbOfFin_mem rfl i
  have hs : Monotone s := by
    intro n m hnm
    dsimp only [s]
    split_ifs with hn hm hm
    · exact f.monotone hnm
    · exact (ht _ (hmem _)).2
    · omega
    · exact le_rfl
  have hl (n : ℕ) : v ≤ s n := by
    dsimp only [s]; split_ifs with hn
    · exact (ht _ (hmem _)).1
    · exact hvU
  have hu (n : ℕ) : s n ≤ U := by
    dsimp only [s]; split_ifs with hn
    · exact (ht _ (hmem _)).2
    · exact le_rfl
  have he : (⋃ x ∈ t, E x) = ⋃ i ∈ Finset.range t.card, E (s i) := by
    ext ω
    simp only [mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨x, hx, hω⟩
      have hex : ∃ i, f i = x := by
        change x ∈ Set.range f
        rw [Finset.range_orderEmbOfFin]
        exact hx
      obtain ⟨i, rfl⟩ := hex
      refine ⟨i.val, i.isLt, ?_⟩
      simpa only [s, dite_eq_left i.isLt] using hω
    · rintro ⟨i, hi, hω⟩
      refine ⟨f ⟨i, hi⟩, hmem _, ?_⟩
      simpa only [s, dite_eq_left hi] using hω
  rw [he]
  exact h s hs hl hu t.card

lemma countable_grid_from_monotone
    {Ω T : Type*} [MeasurableSpace Ω] [LinearOrder T]
    (Q : Measure Ω) (E : T → Set Ω) (v U : T) (hvU : v ≤ U) (c : ℝ≥0∞)
    (h : ∀ s : ℕ → T, Monotone s → (∀ n, v ≤ s n) → (∀ n, s n ≤ U) →
      ∀ N, Q (⋃ i ∈ Finset.range N, E (s i)) ≤ c)
    (s : ℕ → T) (hs : ∀ n, s n ∈ Icc v U) : Q (⋃ n, E (s n)) ≤ c := by
  have hf (N : ℕ) : Q (⋃ i ∈ Finset.range N, E (s i)) ≤ c := by
    have hh := finite_grid_from_monotone Q E v U hvU c h
      ((Finset.range N).image s) (by simpa using (fun i (_ : i ∈ Finset.range N) => hs i))
    simpa using hh
  have he : (⋃ n, E (s n)) = ⋃ N, ⋃ i ∈ Finset.range N, E (s i) := by
    ext ω
    simp only [mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨i+1, i, Nat.lt_succ_self i, hi⟩
    · rintro ⟨N, i, _, hi⟩; exact ⟨i, hi⟩
  have hmono : Monotone (fun N => ⋃ i ∈ Finset.range N, E (s i)) := by
    intro n m hnm ω hω
    obtain ⟨i, hi, hω⟩ := mem_iUnion₂.mp hω
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hnm), hω⟩
  rw [he, hmono.measure_iUnion]
  exact iSup_le hf

end SLEExactGauge
end

 
section

open Set MeasureTheory Classical TopologicalSpace
open scoped ENNReal Topology NNReal
namespace SLEExactGauge

lemma continuous_crossing_from_monotone
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) (K : ℝ≥0 → Ω → ℝ) (live : Set Ω)
    (v w U : ℝ≥0) (hvw : v ≤ w) (hwU : w ≤ U) (δ : ℝ) (c : ℝ≥0∞)
    (hc : ∀ ω ∈ live, ContinuousOn (fun s => K s ω) (Icc v w))
    (hp : ∀ ω ∈ live, ∀ s ∈ Icc v w, 0 < K s ω)
    (h : ∀ s : ℕ → ℝ≥0, Monotone s → (∀ n, v ≤ s n) → (∀ n, s n ≤ U) →
      ∀ N, Q (⋃ i ∈ Finset.range N, {ω | 0 < K (s i) ω ∧ K (s i) ω ≤ δ}) ≤ c) :
    Q {ω | ω ∈ live ∧ ∃ s ∈ Icc v w, K s ω < δ} ≤ c := by
  let T := ↥(Icc v w)
  let : Nonempty T := ⟨⟨v, le_rfl, hvw⟩⟩
  let s (n : ℕ) : ℝ≥0 := (denseSeq T n).val
  have hs (n : ℕ) : s n ∈ Icc v U :=
    ⟨(denseSeq T n).property.1, (denseSeq T n).property.2.trans hwU⟩
  refine (measure_mono (show {ω | ω ∈ live ∧ ∃ s ∈ Icc v w, K s ω < δ} ⊆
    ⋃ n, {ω | 0 < K (s n) ω ∧ K (s n) ω ≤ δ} from ?_)).trans
    (countable_grid_from_monotone Q (fun s => {ω | 0 < K s ω ∧ K s ω ≤ δ})
      v U (hvw.trans hwU) c h s hs)
  intro ω hω
  have hcont : Continuous (fun t : T => K t.val ω) :=
    (hc ω hω.1).domRestrict
  obtain ⟨t, ht, hlt⟩ := hω.2
  obtain ⟨n, hn⟩ := (denseRange_denseSeq T).exists_mem_open
    (isOpen_lt hcont continuous_const) ⟨⟨t, ht⟩, hlt⟩
  exact mem_iUnion.mpr ⟨n, hp ω hω.1 _ (denseSeq T n).property, hn.le⟩

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {ε : ℕ → ℝ}

lemma terminalRadiusKernel_continuousOn
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (p α : ℝ)
    (U : ℝ≥0) (ω : Ω) (hω : localizedRadiusStop (a U) ω < ⊤) :
    ContinuousOn (fun s : ℝ≥0 => limitRadiusKernel (a s) p α s ω) (Icc 0 U) := by
  have he (s : ℝ≥0) (hs : s ∈ Icc 0 U) :
      limitRadiusKernel (a s) p α s ω = limitRadiusKernel (a U) p α s ω :=
    limitRadiusKernel_eq_below (a s) (a U) hε (show (s : ℝ) ≤ U from hs.2) p α s
      s.coe_nonneg le_rfl ω
  have hc := (limitRadiusKernel_continuousOn_of_live (a U) hε hBc p α ω hω).comp
    continuous_subtype_val.continuousOn (show MapsTo (fun s : ℝ≥0 => (s : ℝ)) (Icc 0 U) (Icc 0 (U : ℝ)) from
      fun s hs => ⟨s.coe_nonneg, hs.2⟩)
  exact hc.congr he

lemma terminalRadiusKernel_pos
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (p α : ℝ) (U s : ℝ≥0) (hs : s ≤ U) (ω : Ω)
    (hω : localizedRadiusStop (a U) ω < ⊤) :
    0 < limitRadiusKernel (a s) p α s ω := by
  rw [limitRadiusKernel_eq_below (a s) (a U) hε (show (s : ℝ) ≤ U from hs) p α s
    s.coe_nonneg le_rfl ω]
  exact limitRadiusKernel_pos_of_live (a U) hε p α s ⟨s.coe_nonneg, hs⟩ ω hω

lemma continuous_radius_scaled_crossing
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hz : z ∈ upperHalfPlane)
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (v w U : ℝ≥0) (hv : 1 ≤ (v : ℝ)) (hvw : v ≤ w) (hwU : w ≤ U)
    (L : ℝ) (hL : 0 < L) :
    finiteCenteredLaw P κ B γ G z U
      {ω | localizedRadiusStop (a U) ω < ⊤ ∧ ∃ s ∈ Icc v w,
        limitRadiusKernel (a s) (codimension κ) (greenExponent κ) s ω <
          Real.exp (codimension κ * ((w : ℝ) - Real.log 2 - Real.log z.im)) / L} ≤
      ENNReal.ofReal (uniformInverseAngleConstant κ 1 * Real.exp (codimension κ * ((w : ℝ) - v)) / L) := by
  apply continuous_crossing_from_monotone _ _ _ v w U hvw hwU
  · intro ω hω
    exact (terminalRadiusKernel_continuousOn a hε hBc _ _ U ω hω).mono
      (Icc_subset_Icc (show (0 : ℝ≥0) ≤ v from bot_le) hwU)
  · intro ω hω s hs
    exact terminalRadiusKernel_pos a hε _ _ U s (hs.2.trans hwU) ω hω
  · intro s hs hvs hsU N
    exact finite_radius_scaled_crossing hB hBm hBc hB0 hκ hκ8 γ G F hw hz
      a hε hεlim v U hv s hs hvs hsU w L hL N

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {ε : ℕ → ℝ}

noncomputable def radiusInverseAngle
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (s : ℝ≥0) (ω : Ω) : ℝ :=
  (limitRadiusKernel (a s) 0 2 s ω) ^ (-greenExponent κ / 2)

lemma radiusInverseAngle_product
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (s : ℝ≥0) (ω : Ω) (hω : localizedRadiusStop (a s) ω < ⊤) :
    limitRadiusKernel (a s) (codimension κ) (greenExponent κ) s ω * radiusInverseAngle a s ω =
      Real.exp (codimension κ * ((s : ℝ) - Real.log 2 - Real.log z.im)) := by
  rw [radiusInverseAngle, ← limitRadiusKernel_inverse_factor (a s) hε, sub_self,
    radius_limit_clock_angle (a s) hε (codimension κ) 0 s ⟨s.coe_nonneg, le_rfl⟩ ω hω]
  simp

lemma radiusInverseAngle_large_imp_crossing
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (hκ8 : κ < 8) (s w U : ℝ≥0) (hsw : s ≤ w) (hwU : w ≤ U)
    (L : ℝ) (hL : 0 < L) (ω : Ω) (hω : localizedRadiusStop (a U) ω < ⊤)
    (hV : L < radiusInverseAngle a s ω) :
    limitRadiusKernel (a s) (codimension κ) (greenExponent κ) s ω <
      Real.exp (codimension κ * ((w : ℝ) - Real.log 2 - Real.log z.im)) / L := by
  have hls : localizedRadiusStop (a s) ω < ⊤ :=
    lt_of_le_of_lt (localizedRadiusStop_mono (a s) (a U) (show (s : ℝ) ≤ U from hsw.trans hwU) ω) hω
  have hK := terminalRadiusKernel_pos a hε (codimension κ) (greenExponent κ) U s (hsw.trans hwU) ω hω
  apply (lt_div_iff₀ hL).mpr
  calc
    _ < limitRadiusKernel (a s) (codimension κ) (greenExponent κ) s ω * radiusInverseAngle a s ω :=
      mul_lt_mul_of_pos_left hV hK
    _ = Real.exp (codimension κ * ((s : ℝ) - Real.log 2 - Real.log z.im)) :=
      radiusInverseAngle_product a hε s ω hls
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right (sub_le_sub_right (show (s : ℝ) ≤ w from hsw) _) _) (codimension_pos κ hκ8).le)

lemma inverse_angle_window_bound
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hz : z ∈ upperHalfPlane)
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (v w U : ℝ≥0) (hv : 1 ≤ (v : ℝ)) (hvw : v ≤ w) (hwU : w ≤ U)
    (L : ℝ) (hL : 0 < L) :
    finiteCenteredLaw P κ B γ G z U
      {ω | localizedRadiusStop (a U) ω < ⊤ ∧ ∃ s ∈ Icc v w, L < radiusInverseAngle a s ω} ≤
      ENNReal.ofReal (uniformInverseAngleConstant κ 1 * Real.exp (codimension κ * ((w : ℝ) - v)) / L) := by
  refine (measure_mono (s := {ω | localizedRadiusStop (a U) ω < ⊤ ∧ ∃ s ∈ Icc v w, L < radiusInverseAngle a s ω})
    (t := {ω | localizedRadiusStop (a U) ω < ⊤ ∧ ∃ s ∈ Icc v w,
      limitRadiusKernel (a s) (codimension κ) (greenExponent κ) s ω <
        Real.exp (codimension κ * ((w : ℝ) - Real.log 2 - Real.log z.im)) / L}) ?_).trans
    (continuous_radius_scaled_crossing hB hBm hBc hB0 hκ hκ8 γ G F hw hz a hε hεlim
      v w U hv hvw hwU L hL)
  rintro ω ⟨hω, s, hs, hV⟩
  exact ⟨hω, s, hs, radiusInverseAngle_large_imp_crossing a hε hκ8 s w U hs.2 hwU L hL ω hω hV⟩

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {ε : ℕ → ℝ}

end SLEExactGauge
end
end

end OAI
