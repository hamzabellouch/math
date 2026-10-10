import Mathlib
import OAI.Geometry.CAT0Fillings.Tangent.LocalChart
import OAI.Geometry.CAT0Fillings.Tangent.Quadratic

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] {X : Type*} [MetricSpace X] {μ : Measure E}

lemma global_density_bound {s : Set E} {φ : s → X} {z : s} {d : Seminorm ℝ E}
    (hd : MetricDifferentiation.HasCenteredMetricDifferentialWithin s φ d z)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε0 : Tendsto ε atTop (𝓝 0))
    (u ρ : E → ℝ) {κ β p : ℝ} (n : ℕ) (hu₀ : 0 < u z)
    (hu : ∀ R : ℝ, 0 < R → TendstoInMeasure (μ.restrict (closedBall (0:E) R))
      (fun j h => u ((z:E)+ε j • h)) atTop (fun _ => u z))
    (hρ : ∀ R : ℝ, 0 < R → TendstoInMeasure (μ.restrict (closedBall (0:E) R))
      (fun j h => ρ ((z:E)+ε j • h)) atTop (fun _ => ρ z))
    (hχ : ∀ R : ℝ, 0 < R → TendstoInMeasure (μ.restrict (closedBall (0:E) R))
      (fun j h => s.indicator (fun _ => (1:ℝ)) ((z:E)+ε j • h)) atTop (fun _ => 1))
    (hK : ∀ j, AEMeasurable (fun h => ENNReal.ofReal (s.indicator (fun x => u x^p*ρ x /
      (1+κ^2*(dist (chartExtension φ z x) (φ z)/ε j)^2*u x^(2*β))^n)
      ((z:E)+ε j • h))) μ)
    {B : ℕ → ℝ≥0∞} {L : ℝ≥0∞}
    (hB : ∀ j, (∫⁻ h, ENNReal.ofReal (s.indicator (fun x => u x^p*ρ x /
      (1+κ^2*(dist (chartExtension φ z x) (φ z)/ε j)^2*u x^(2*β))^n)
      ((z:E)+ε j • h)) ∂μ) ≤ B j)
    (hL : Tendsto B atTop (𝓝 L)) :
    (∫⁻ h, ENNReal.ofReal (u z^p*ρ z/(1+κ^2*(d h)^2*u z^(2*β))^n) ∂μ) ≤ L := by
  have hloc {R : ℝ} (hR : 0 < R) :
      (∫⁻ h in closedBall (0:E) R, ENNReal.ofReal (u z^p*ρ z/(1+κ^2*(d h)^2*u z^(2*β))^n) ∂μ) ≤ L :=
    local_density_bound hd hε hε0 u ρ n hu₀ (hu R hR) (hρ R hR) (hχ R hR)
      (fun j => (hK j).mono_measure Measure.restrict_le_self)
      (fun j => (lintegral_mono' Measure.restrict_le_self le_rfl).trans (hB j)) hL
  rw [←Measure.restrict_univ (μ := μ),←iUnion_closedBall_nat (0:E),setLIntegral_iUnion_of_directed]
  · apply iSup_le
    intro j
    exact (lintegral_mono' (Measure.restrict_mono (closedBall_subset_closedBall (show (j:ℝ) ≤ j+1 by linarith)) le_rfl)
      le_rfl).trans (hloc (R := (j:ℝ)+1) (by positivity))
  · intro i j
    exact ⟨max i j,closedBall_subset_closedBall (Nat.cast_le.mpr (le_max_left i j)),
      closedBall_subset_closedBall (Nat.cast_le.mpr (le_max_right i j))⟩

lemma tangent_coefficient_of_bound {n : ℕ} (hn : 2 < n) (d : Seminorm ℝ (Euc n))
    (hd : ∀ h, d h = 0 ↔ h = 0)
    (hpara : ∀ h h', d (h+h')^2+d (h-h')^2 = 2*d h^2+2*d h'^2)
    {u β : ℝ} (hu : 0 < u) {θ : ℤ} (hθ : θ ≠ 0) {L : ℝ≥0∞}
    (hL : (∫⁻ h : Euc n, ENNReal.ofReal (u^(2*(n:ℝ)*β)*
      (|(θ:ℝ)| * Real.sqrt (polarizationMatrix d (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det) /
      (1+(u^β)^2*(d h)^2*u^(2*β))^n)) ≤ L) :
    ENNReal.ofReal (sphereArea n/(2:ℝ)^n) ≤ L := by
  have hc := tangent_density_lower_bound hn d hd hpara (β := β) hu hθ
  apply (ENNReal.ofReal_le_ofReal hc).trans
  apply le_trans ?_ hL
  by_cases hi : Integrable (fun h : Euc n => u^(2*(n:ℝ)*β)*
      (|(θ:ℝ)| * Real.sqrt (polarizationMatrix d (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det) /
      (1+(u^β)^2*(d h)^2*u^(2*β))^n)
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun h => by positivity)]
  · rw [integral_undef hi,ENNReal.ofReal_zero]
    exact bot_le
end CAT0Fillings.TangentDensity
end

section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace CAT0Fillings.ChartGeometry
open TangentDensity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma ae_chart_tangent_density (hn : 2 < n) (i : ℕ) (U : X → ℝ)
    (hU : Measurable U) (hU0 : ∀ x, 0 ≤ U x) {β : ℝ} (hb : 0 ≤ β) :
    ∀ᵐ z ∂q.coordinateMeasure i, 0 < U ((q.chart i).paramExtended z) →
      ∀ (ε : ℕ → ℝ), (∀ j, 0 < ε j) → Tendsto ε atTop (𝓝 0) →
      ∀ (B : ℕ → ℝ≥0∞) (L : ℝ≥0∞),
      (∀ j, ENNReal.ofReal ((ε j^n)⁻¹) *
        ∫⁻ x, ENNReal.ofReal (U x^(2*(n:ℝ)*β)/
          (1+(U ((q.chart i).paramExtended z)^β)^2*
            (dist x ((q.chart i).paramExtended z)/ε j)^2*U x^(2*β))^n)
          ∂MassMeasure.currentMassMeasure hT ≤ B j) →
      Tendsto B atTop (𝓝 L) →
      ENNReal.ofReal (sphereArea n/(2:ℝ)^n) ≤ L := by
  classical
  let C := q.chart i
  let ρ := C.domain.indicator (q.density i)
  let u (N : ℕ) := C.domain.indicator
    (fun z => boundedCoordinate (U (C.paramExtended z)) (N:ℝ))
  have hρ : Integrable ρ := IntegrableOn.integrable_indicator (q.density_integrable i) C.borel
  have hχ : Integrable (C.domain.indicator (fun _ => (1:ℝ))) := by
    exact IntegrableOn.integrable_indicator (integrableOn_const C.bounded.measure_lt_top.ne) C.borel
  have hu (N : ℕ) : Integrable (u N) := integrable_coordinate_truncation C.borel
    C.bounded.measure_lt_top.ne (hU.comp C.measurable_paramExtended) (Nat.cast_nonneg N)
  have hmu (N : ℕ) : Measurable (u N) :=
    (((hU.comp C.measurable_paramExtended).max measurable_const).min measurable_const).indicator C.borel
  have ha : ∀ᵐ z ∂volume, ∀ N : ℕ, ∀ (ε : ℕ → ℝ), (∀ j, 0 < ε j) →
      Tendsto ε atTop (𝓝 0) → ∀ R : ℝ, 0 < R →
      TendstoInMeasure (volume.restrict (closedBall (0:Euc n) R))
        (fun j h => u N (z+ε j • h)) atTop (fun _ => u N z) := by
    exact ae_all_iff.mpr (fun N => ae_all_blowup_inMeasure volume (hu N))
  rw [coordinateMeasure]
  apply (ae_withDensity_iff' (q.density_integrable i).aestronglyMeasurable.aemeasurable.ennreal_ofReal).mpr
  filter_upwards [ha.filter_mono (ae_mono Measure.restrict_le_self),
    (ae_all_blowup_inMeasure volume hρ).filter_mono (ae_mono Measure.restrict_le_self),
    (ae_all_blowup_inMeasure volume hχ).filter_mono (ae_mono Measure.restrict_le_self),
    q.differential i,ae_restrict_mem C.borel] with z hu' hρ' hχ' hd hz
  intro hρ0 hUz ε hε hε0 B L hupper hL
  have hzC : z ∈ C.domain := hz
  obtain ⟨N,hN⟩ := exists_nat_ge (U (C.paramExtended z))
  have huz : u N z = U (C.paramExtended z) := by
    simp only [u,indicator_of_mem hzC]
    exact boundedCoordinate_eq (hU0 _) hN
  have hθ : C.multiplicity z ≠ 0 := by
    intro hh
    apply hρ0
    simp [density,hh,C]
  have hρz : ρ z = q.density i z := indicator_of_mem hz _
  have hχz : C.domain.indicator (fun _ => (1:ℝ)) z = 1 := indicator_of_mem hz _
  have he : C.param ⟨z,hz⟩ = C.paramExtended z := by simp only [IntegerChart.paramExtended,dite_eq_left hzC]
  have heq : (q.chart i).param ⟨z,hz⟩ = (q.chart i).paramExtended z := he
  have hu₀ : ∀ x, 0 ≤ u N x := by
    intro x
    apply indicator_nonneg
    exact fun y hy => boundedCoordinate_nonneg (Nat.cast_nonneg N) _
  have huU : ∀ x ∈ C.domain, u N x ≤ U (C.paramExtended x) := by
    intro x hx
    simp only [u,indicator_of_mem hx]
    exact boundedCoordinate_le (hU0 _)
  have hbound := global_density_bound (κ := U (C.paramExtended z)^β) (β := β)
    (p := 2*(n:ℝ)*β) (μ := volume) (hd.1 hz) hε hε0 (u N) ρ n
    (show 0 < u N z by rw [huz]; exact hUz)
    (hu' N ε hε hε0) (hρ' ε hε hε0)
    (by simpa only [hχz] using hχ' ε hε hε0)
    (fun j => q.chart_kernel_aemeasurable i (u N) (hmu N) ⟨z,hz⟩ (hε j) _ _ _)
    (fun j => (q.chart_kernel_blowup_le i U hU hU0 (u N) hu₀ huU ⟨z,hz⟩
      (κ := U (C.paramExtended z)^β) (hε j) hb).trans (by simpa only [heq] using hupper j))
    hL
  apply tangent_coefficient_of_bound hn (q.field i z) hd.2.2 hd.2.1 hUz hθ
  simpa only [huz,hρz,density,gram,he] using hbound
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity
lemma ae_map_of_ae_on_embedding {E X : Type*} [MeasurableSpace E] [MeasurableSpace X]
    {μ : Measure E} {s : Set E} (hs : MeasurableSet s) {f : E → X} (hf : Measurable f)
    (hfs : MeasurableEmbedding (fun z : s => f z)) (hmem : ∀ᵐ z ∂μ, z ∈ s)
    {P : X → Prop} (hP : ∀ᵐ z ∂μ, P (f z)) : ∀ᵐ x ∂μ.map f, P x := by
  let ν := μ.comap (fun z : s => (z:E))
  have hmap : ν.map (fun z : s => (z:E)) = μ := by
    rw [(MeasurableEmbedding.subtype_coe hs).map_comap]
    simp only [Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem hmem
  have hmap' : ν.map (fun z : s => f z) = μ.map f := by
    change ν.map (f ∘ Subtype.val) = μ.map f
    rw [←Measure.map_map hf measurable_subtype_coe,hmap]
  rw [←hmap']
  apply hfs.ae_map_iff.mpr
  exact ae_of_ae_map (μ := ν) (p := fun z => P (f z))
    measurable_subtype_coe.aemeasurable (by rw [hmap]; exact hP)
end CAT0Fillings.TangentDensity
namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma ae_current_of_ae_coordinates {P : X → Prop}
    (hP : ∀ i, ∀ᵐ z ∂q.coordinateMeasure i, P ((q.chart i).paramExtended z)) :
    ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, P x := by
  rw [q.measure_eq]
  apply Measure.ae_sum_iff.mpr
  intro i
  change ∀ᵐ x ∂(q.coordinateMeasure i).map (q.chart i).paramExtended, P x
  apply TangentDensity.ae_map_of_ae_on_embedding (q.chart i).borel
    (q.chart i).measurable_paramExtended ?_ ?_ (hP i)
  · convert (q.chart i).measurableEmbedding_param using 1
    ext z
    simp [IntegerChart.paramExtended,z.property]
  · exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (q.chart i).borel)
end CAT0Fillings.ChartGeometry
end

end OAI
