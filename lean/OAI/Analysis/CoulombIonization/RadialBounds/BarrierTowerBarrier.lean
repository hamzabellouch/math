import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.PuncturedGreenBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.BarrierObservationTowerBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierSourceTower_barrier_scope

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators Topology

open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterKernel masterWidth scaledRealPacket

def innerSource (R : ℝ) (μ p : TFSpace → ℝ) (x : TFSpace) : ℝ :=
  4*Real.pi*((if ‖x‖ < R then μ x else 0)-p x)

def outerCoefficient (R : ℝ) (x : TFSpace) : ℝ := if R ≤ ‖x‖ then 1 else 0

lemma outerCoefficient_measurable (R : ℝ) : Measurable (outerCoefficient R) :=
  Measurable.ite (measurableSet_le measurable_const continuous_norm.measurable)
    measurable_const measurable_const

lemma outerCoefficient_bound (R : ℝ) (x : TFSpace) : ‖outerCoefficient R x‖ ≤ 1 := by
  unfold outerCoefficient
  split_ifs <;> norm_num

lemma outerCoefficient_nonneg (R : ℝ) (x : TFSpace) : 0 ≤ outerCoefficient R x := by
  unfold outerCoefficient
  split_ifs <;> norm_num

lemma outerCoefficient_zero (R : ℝ) (x : TFSpace) (hx : ‖x‖ < R) :
    outerCoefficient R x = 0 := ite_eq_right (not_le_of_gt hx)

lemma innerSource_measurable {Ω : Type*} [MeasurableSpace Ω]
    {μ p : Ω → TFSpace → ℝ} (hμ : Measurable (Function.uncurry μ))
    (hp : Measurable (Function.uncurry p)) (R : ℝ) :
    Measurable (fun z : Ω × TFSpace => innerSource R (μ z.1) (p z.1) z.2) := by
  exact (Measurable.ite (measurableSet_lt (continuous_norm.measurable.comp measurable_snd)
    measurable_const) hμ measurable_const |>.sub hp).const_mul (4*Real.pi)

lemma innerSource_bound {Ω : Type*} {μ p : Ω → TFSpace → ℝ}
    (hμ : DeterministicLocalBound μ) (hp : DeterministicLocalBound p) (R : ℝ) :
    DeterministicLocalBound (fun sample => innerSource R (μ sample) (p sample)) := by
  intro K hK
  obtain ⟨C,hC⟩ := hμ K hK
  obtain ⟨D,hD⟩ := hp K hK
  refine ⟨|4*Real.pi| *(|C|+|D|),fun sample x hx => ?_⟩
  have hi : ‖if ‖x‖ < R then μ sample x else 0‖ ≤ |C| := by
    split_ifs
    · exact (hC sample x hx).trans (le_abs_self C)
    · simpa only [norm_zero] using abs_nonneg C
  calc
    _ = |4*Real.pi| *‖(if ‖x‖ < R then μ sample x else 0)-p sample x‖ := norm_mul _ _
    _ ≤ |4*Real.pi| *(‖if ‖x‖ < R then μ sample x else 0‖+‖p sample x‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add hi ((hD sample x hx).trans (le_abs_self D))) (abs_nonneg _)

lemma conditionalField_innerSource {Ω D : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace D]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → D)
    {μ p : Ω → TFSpace → ℝ} (hμm : Measurable (Function.uncurry μ))
    (hμb : DeterministicLocalBound μ) (hpm : Measurable (Function.uncurry p))
    (hpb : DeterministicLocalBound p) (R : ℝ) (d : D) (x : TFSpace) :
    conditionalField P X (fun sample => innerSource R (μ sample) (p sample)) d x =
      innerSource R (conditionalField P X μ d) (conditionalField P X p d) x := by
  unfold conditionalField innerSource
  rw [integral_const_mul]
  by_cases hx : ‖x‖ < R
  · simp only [ite_eq_left hx]
    rw [integral_sub (deterministicBound_integrable_section hμm hμb x)
      (deterministicBound_integrable_section hpm hpb x)]
  · simp only [ite_eq_right hx,zero_sub,integral_neg]

theorem original_barrier_source_forgetting {N K : ℕ} (μ : Measure (Configuration N))
    [IsProbabilityMeasure μ] (ell : Fin K → ℝ) {j k : ℕ} (hjk : j ≤ k)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    {u p : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → TFSpace → ℝ}
    (hum : Measurable (Function.uncurry u)) (hub : DeterministicLocalBound u)
    (huc : ∀ᵐ z ∂physicalObservationLaw μ K, Continuous (u z))
    (hpm : Measurable (Function.uncurry p)) (hpb : DeterministicLocalBound p)
    (Z : ℝ) {R κ : ℝ} (hR : 0 < R) (hκ : 0 ≤ κ)
    (hw : ∀ᵐ z ∂physicalObservationLaw μ K, WeakNuclearLowerOn univ Z
      (fun x => nuclearField Z x+u z x)
      (fun x => innerSource R (originalMasterField μ ell j c₁ r₀ s g z) (p z) x+
        outerCoefficient R x*reaction κ (nuclearField Z x+u z x))) :
    ∀ᵐ z ∂physicalObservationLaw μ K, WeakNuclearLowerOn univ Z
      (fun x => nuclearField Z x+conditionalField (physicalObservationLaw μ K)
        (originalDatum ell k) u (originalDatum ell k z) x)
      (fun x => innerSource R (originalMasterField μ ell k c₁ r₀ s g z)
        (conditionalField (physicalObservationLaw μ K) (originalDatum ell k) p (originalDatum ell k z)) x+
        outerCoefficient R x*reaction κ (nuclearField Z x+conditionalField (physicalObservationLaw μ K)
          (originalDatum ell k) u (originalDatum ell k z) x)) := by
  let P := physicalObservationLaw μ K
  have hdm := originalMasterField_measurable μ ell j hc hr hs hg
  have hdb := originalMasterField_deterministicBound μ ell j hc hr hs hrs hg hcg
  have hh := weak_nuclear_conditional P (originalDatum ell k) (originalDatum_measurable ell k) Z
    (g := fun sample => innerSource R (originalMasterField μ ell j c₁ r₀ s g sample) (p sample))
    hum hub huc (innerSource_measurable hdm hpm R) (innerSource_bound hdb hpb R)
    (outerCoefficient_measurable R) (outerCoefficient_bound R) (outerCoefficient_nonneg R)
    hR hκ (outerCoefficient_zero R) hw
  have hh' := ae_of_ae_map (originalDatum_measurable ell k).aemeasurable hh
  filter_upwards [hh',originalMasterField_tower μ ell hjk hc hr hs hrs hg hcg] with z hz ht
  convert hz using 1
  funext x
  rw [conditionalField_innerSource P (originalDatum ell k) hdm hdb hpm hpb R]
  simp only [innerSource,P,ht]

end Work_BarrierSourceTower_barrier_scope

open Set Filter Laplacian InnerProductSpace
open scoped Topology

open CoulombPDE

def outerBarrier (B r : ℝ) (x : Space) : ℝ :=
  B / ‖x‖^4 * (1-r/(8*‖x‖))

lemma radialPower_neg_two (x : Space) : radialPower (-2) x = (‖x‖^4)⁻¹ := by
  unfold radialPower
  rw [Real.rpow_neg (sq_nonneg _),Real.rpow_two]
  congr 1
  ring

lemma radialPower_neg_three (x : Space) : radialPower (-3) x = (‖x‖^6)⁻¹ := by
  unfold radialPower
  rw [Real.rpow_neg (sq_nonneg _),show (3:ℝ) = (3:ℕ) by norm_num,Real.rpow_natCast]
  congr 1
  ring

lemma outerBarrier_eq_combination (B r : ℝ) {x : Space} (hx : x ≠ 0) :
    outerBarrier B r x = radialCombination B (-B*r/8) (1/2) 0 x := by
  rw [radialCombination_factor _ _ _ _ hx,radialPower_half_inv,radialPower_neg_two]
  unfold outerBarrier
  ring

lemma outerBarrier_contDiffAt (B r : ℝ) {x : Space} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (outerBarrier B r) x := by
  apply (radialCombination_contDiffAt B (-B*r/8) (1/2) 0 hx).congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds hx] with y hy
  exact outerBarrier_eq_combination B r hy

lemma outerBarrier_laplacian (B r : ℝ) {x : Space} (hx : x ≠ 0) :
    Δ (outerBarrier B r) x = B/‖x‖^6*(12-20*r/(8*‖x‖)) := by
  have he : outerBarrier B r =ᶠ[𝓝 x] radialCombination B (-B*r/8) (1/2) 0 := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact outerBarrier_eq_combination B r hy
  rw [(laplacian_congr_nhds he).eq_of_nhds,radialCombination_laplacian _ _ _ _ hx,
    radialPower_half_inv,radialPower_neg_three]
  ring

lemma outerBarrier_bounds {B r : ℝ} (hB : 0 ≤ B) (hr : 0 < r)
    {x : Space} (hx : r ≤ ‖x‖) :
    (7*B/8)/‖x‖^4 ≤ outerBarrier B r x ∧ outerBarrier B r x ≤ B/‖x‖^4 := by
  have hd : 0 < ‖x‖ := hr.trans_le hx
  have hq0 : 0 ≤ r/(8*‖x‖) := by positivity
  have hq1 : r/(8*‖x‖) ≤ 1/8 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hb : 0 ≤ B/‖x‖^4 := by positivity
  unfold outerBarrier
  constructor
  · calc
      _ = (B/‖x‖^4)*(7/8) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hb
  · calc
      _ ≤ (B/‖x‖^4)*1 := mul_le_mul_of_nonneg_left (by linarith) hb
      _ = _ := mul_one _

theorem outerBarrier_subsolution {B r k : ℝ} (hB : 0 < B) (hr : 0 < r)
    (hk : 0 ≤ k) (hsmall : 4*Real.pi*k*Real.sqrt B ≤ 19/2)
    {x : Space} (hx : r ≤ ‖x‖) :
    4*Real.pi*k*(max (outerBarrier B r x) 0)^(3/2:ℝ) ≤ Δ (outerBarrier B r) x := by
  have hd : 0 < ‖x‖ := hr.trans_le hx
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp hd.ne'
  obtain ⟨hl,hu⟩ := outerBarrier_bounds hB.le hr hx
  have hn : 0 ≤ outerBarrier B r x := (by positivity : 0 ≤ (7*B/8)/‖x‖^4).trans hl
  have hc : 0 ≤ 4*Real.pi*k := by positivity
  have hreact : (B/‖x‖^4)^(3/2:ℝ) = radialPower (-3) x*B^(3/2:ℝ) := by
    rw [← radial_scaled_reaction hB.le x,radialPower_neg_two]
    congr 1
    ring
  have hq : r/(8*‖x‖) ≤ 1/8 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  calc
    _ ≤ 4*Real.pi*k*(B/‖x‖^4)^(3/2:ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (max_le hu (by positivity)) (by norm_num)) hc
    _ = (4*Real.pi*k*Real.sqrt B)*B/‖x‖^6 := by
      rw [hreact,rpow_three_halves B hB.le,← Real.sqrt_eq_rpow,radialPower_neg_three]
      ring
    _ ≤ (19/2)*B/‖x‖^6 := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsmall hB.le) (by positivity)
    _ ≤ B/‖x‖^6*(12-20*r/(8*‖x‖)) := by
      have hp : 0 ≤ B/‖x‖^6 := by positivity
      have hq' : 20*r/(8*‖x‖) ≤ 5/2 := by
        calc
          _ = 20*(r/(8*‖x‖)) := by ring
          _ ≤ _ := by linarith
      calc
        _ = (B/‖x‖^6)*(19/2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hp
    _ = _ := (outerBarrier_laplacian B r hx0).symm

end CoulombBarrier

end

end OAI
