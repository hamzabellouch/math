import Mathlib
import OAI.Geometry.CAT0Fillings.Tangent.Coordinates
import OAI.Geometry.CAT0Fillings.Tangent.Kernel

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChartGeometry
open TangentDensity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma chart_kernel_blowup_le (i : ℕ) (U : X → ℝ) (hU : Measurable U)
    (hU0 : ∀ x, 0 ≤ U x) (u : Euc n → ℝ) (hu : ∀ z, 0 ≤ u z)
    (huU : ∀ z ∈ (q.chart i).domain, u z ≤ U ((q.chart i).paramExtended z))
    (z : (q.chart i).domain) {ε β κ : ℝ} (hε : 0 < ε) (hb : 0 ≤ β) :
    let ρ := (q.chart i).domain.indicator (q.density i)
    (∫⁻ h, ENNReal.ofReal ((q.chart i).domain.indicator
      (fun x => (u x)^(2*(n:ℝ)*β)*ρ x /
        (1+κ^2*(dist (chartExtension (q.chart i).param z x) ((q.chart i).param z)/ε)^2*(u x)^(2*β))^n)
      ((z:Euc n)+ε • h))) ≤
    ENNReal.ofReal ((ε^n)⁻¹) * ∫⁻ x, ENNReal.ofReal
      ((U x)^(2*(n:ℝ)*β)/(1+κ^2*(dist x ((q.chart i).param z)/ε)^2*(U x)^(2*β))^n)
        ∂MassMeasure.currentMassMeasure hT := by
  classical
  let ρ := (q.chart i).domain.indicator (q.density i)
  let C := q.chart i
  let F : X → ℝ≥0∞ := fun x => ENNReal.ofReal
    ((U x)^(2*(n:ℝ)*β)/(1+κ^2*(dist x (C.param z)/ε)^2*(U x)^(2*β))^n)
  have hF : Measurable F := ((hU.pow_const _).div
    ((measurable_const.add ((measurable_const.mul
      (((measurable_id.dist measurable_const).div_const ε).pow_const 2)).mul
      (hU.pow_const _))).pow_const n)).ennreal_ofReal
  let g : Euc n → ℝ := fun x => (u x)^(2*(n:ℝ)*β)*ρ x /
    (1+κ^2*(dist (chartExtension C.param z x) (C.param z)/ε)^2*(u x)^(2*β))^n
  change (∫⁻ h, ENNReal.ofReal (C.domain.indicator g ((z:Euc n)+ε • h))) ≤ _
  rw [lintegral_affine volume (fun x => ENNReal.ofReal (C.domain.indicator g x)) (z:Euc n) hε]
  simp only [finrank_euclideanSpace,Fintype.card_fin]
  gcongr 1
  apply le_trans ?_ (q.lintegral_coordinate_le i F hF)
  have hi : (fun x => ENNReal.ofReal (C.domain.indicator g x)) =
      C.domain.indicator (fun x => ENNReal.ofReal (g x)) := by
    ext x
    by_cases hx : x ∈ C.domain <;> simp [hx]
  change (∫⁻ x, ENNReal.ofReal (C.domain.indicator g x)) ≤ _
  rw [hi,lintegral_indicator C.borel]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem C.borel] with x hx
  have he : chartExtension C.param z x = C.paramExtended x := by
    simp only [chartExtension,IntegerChart.paramExtended,dite_eq_left hx]
  have density_nonneg : 0 ≤ q.density i x :=
    mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  change ENNReal.ofReal (g x) ≤ ENNReal.ofReal (q.density i x)*F (C.paramExtended x)
  dsimp only [F]
  have kernel_nonneg : 0 ≤
      (U (C.paramExtended x))^(2*(n:ℝ)*β) /
        (1+κ^2*(dist (C.paramExtended x) (C.param z)/ε)^2*
          (U (C.paramExtended x))^(2*β))^n := by
    apply div_nonneg (Real.rpow_nonneg (hU0 _) _)
    exact pow_nonneg (add_nonneg zero_le_one
      (mul_nonneg (mul_nonneg (sq_nonneg κ) (sq_nonneg _))
        (Real.rpow_nonneg (hU0 _) _))) _
  rw [←ENNReal.ofReal_mul' kernel_nonneg]
  apply ENNReal.ofReal_le_ofReal
  have hm := tangent_kernel_mono (hu x) (huU x hx) hb
    (mul_nonneg (sq_nonneg κ) (sq_nonneg (dist (C.paramExtended x) (C.param z)/ε))) n
  dsimp only [g]
  rw [show ρ x = q.density i x from indicator_of_mem hx _,he]
  convert mul_le_mul_of_nonneg_right hm density_nonneg using 1 <;> first | rfl | ring
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChartGeometry
open TangentDensity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma chart_kernel_aemeasurable (i : ℕ) (u : Euc n → ℝ) (hu : Measurable u)
    (z : (q.chart i).domain) {ε : ℝ} (hε : 0 < ε) (p β κ : ℝ) :
    let ρ := (q.chart i).domain.indicator (q.density i)
    AEMeasurable (fun h : Euc n => ENNReal.ofReal ((q.chart i).domain.indicator
      (fun x => u x^p*ρ x /
        (1+κ^2*(dist (chartExtension (q.chart i).param z x) ((q.chart i).param z)/ε)^2*u x^(2*β))^n)
      ((z:Euc n)+ε • h))) volume := by
  classical
  let C := q.chart i
  let ρ := C.domain.indicator (q.density i)
  let A : Euc n → Euc n := fun h => (z:Euc n)+ε • h
  have hA : Measurable A := by
    dsimp [A]
    fun_prop
  have hρ : Integrable ρ := IntegrableOn.integrable_indicator (q.density_integrable i) C.borel
  have hρA := (integrable_affine volume ρ hρ (z:Euc n) hε.ne').aestronglyMeasurable.aemeasurable
  have huA := hu.comp hA
  have hdA : Measurable (fun h => dist (C.paramExtended (A h)) (C.param z)/ε) :=
    (((C.measurable_paramExtended.comp hA).dist measurable_const).div_const ε)
  have hm : AEMeasurable (fun h => u (A h)^p*ρ (A h) /
      (1+κ^2*(dist (C.paramExtended (A h)) (C.param z)/ε)^2*u (A h)^(2*β))^n) volume :=
    ((huA.pow_const p).aemeasurable.mul hρA).div
    ((measurable_const.add ((measurable_const.mul (hdA.pow_const 2)).mul
      (huA.pow_const (2*β)))).pow_const n).aemeasurable
  have hi := (hm.indicator (C.borel.preimage hA)).ennreal_ofReal
  convert hi using 1
  ext h
  by_cases hh : A h ∈ C.domain
  · dsimp [A,C] at hh
    simp [A,C,ρ,chartExtension,IntegerChart.paramExtended,hh]
  · dsimp [A,C] at hh
    simp [A,C,ρ,hh]
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] {X : Type*} [MetricSpace X] {μ : Measure E}

lemma local_density_bound {s : Set E} {φ : s → X} {z : s} {d : Seminorm ℝ E}
    (hd : MetricDifferentiation.HasCenteredMetricDifferentialWithin s φ d z)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε0 : Tendsto ε atTop (𝓝 0))
    (u ρ : E → ℝ) {κ β p : ℝ} (n : ℕ) (hu₀ : 0 < u z)
    (hu : TendstoInMeasure μ (fun j h => u ((z:E)+ε j • h)) atTop (fun _ => u z))
    (hρ : TendstoInMeasure μ (fun j h => ρ ((z:E)+ε j • h)) atTop (fun _ => ρ z))
    (hχ : TendstoInMeasure μ (fun j h => s.indicator (fun _ => (1:ℝ)) ((z:E)+ε j • h))
      atTop (fun _ => 1))
    (hK : ∀ j, AEMeasurable (fun h => ENNReal.ofReal (s.indicator (fun x => u x^p*ρ x /
      (1+κ^2*(dist (chartExtension φ z x) (φ z)/ε j)^2*u x^(2*β))^n)
      ((z:E)+ε j • h))) μ)
    {B : ℕ → ℝ≥0∞} {L : ℝ≥0∞}
    (hB : ∀ j, (∫⁻ h, ENNReal.ofReal (s.indicator (fun x => u x^p*ρ x /
      (1+κ^2*(dist (chartExtension φ z x) (φ z)/ε j)^2*u x^(2*β))^n)
      ((z:E)+ε j • h)) ∂μ) ≤ B j)
    (hL : Tendsto B atTop (𝓝 L)) :
    (∫⁻ h, ENNReal.ofReal (u z^p*ρ z/(1+κ^2*(d h)^2*u z^(2*β))^n) ∂μ) ≤ L := by
  obtain ⟨σ,hσ,ht⟩ := common_subsequence_three hu hρ hχ
  apply lintegral_limit_le (fun j => hK (σ j)) (B := B ∘ σ) (L := L) ?_
    (fun j => hB (σ j)) (hL.comp hσ.tendsto_atTop)
  filter_upwards [ht] with h hh
  exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (chart_kernel_tendsto hd (fun j => hε (σ j)) (hε0.comp hσ.tendsto_atTop) u ρ n hu₀ h
      hh.1 hh.2.1 hh.2.2)
end CAT0Fillings.TangentDensity
end

end OAI
