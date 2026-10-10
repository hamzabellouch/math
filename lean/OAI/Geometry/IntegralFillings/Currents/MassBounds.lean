import Mathlib
import OAI.Geometry.IntegralFillings.Currents.Basic
import OAI.Geometry.IntegralFillings.Currents.Multilinear

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
universe u
section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
lemma IsMetricCurrent.mass_bound {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {μ : Measure X} (hμ : Controls T μ)
    {b : X → ℝ} (hb : BoundedLip b) {π : Fin k → X → ℝ}
    (K : Fin k → ℝ≥0) (hK : ∀ i, LipschitzWith (K i) (π i)) :
    |T b π| ≤ (∏ i, (K i : ℝ)) * ∫ x, |b x| ∂μ := by
  by_cases hzero : ∃ i, K i = 0
  · obtain ⟨i, hi⟩ := hzero
    have hTi := hT.eq_zero_of_zero_lipschitz_coord ⟨hb, fun j => ⟨K j, hK j⟩⟩ i
      (hi ▸ hK i)
    rw [hTi, abs_zero]
    exact mul_nonneg (Finset.prod_nonneg fun j _ => (K j).coe_nonneg)
      (integral_nonneg fun x => abs_nonneg (b x))
  · have hpos : ∀ i, 0 < K i := fun i => pos_iff_ne_zero.mpr (fun hi => hzero ⟨i, hi⟩)
    have hposR : ∀ i, (0 : ℝ) < K i := fun i => hpos i
    let π' : Fin k → X → ℝ := fun i x => (K i : ℝ)⁻¹ * π i x
    have hπ' : ∀ i, LipschitzWith 1 (π' i) := by
      intro i
      apply lipschitzWith_iff_dist_le_mul.mpr
      intro x y
      change dist ((K i : ℝ)⁻¹ * π i x) ((K i : ℝ)⁻¹ * π i y) ≤ 1 * dist x y
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr (hposR i)), one_mul]
      calc (K i : ℝ)⁻¹ * |π i x - π i y| ≤
          (K i : ℝ)⁻¹ * ((K i : ℝ) * dist x y) :=
            mul_le_mul_of_nonneg_left ((hK i).dist_le_mul x y) (inv_nonneg.mpr (hposR i).le)
        _ = dist x y := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (hposR i)), one_mul]
    have heq : (fun i x => (K i : ℝ) * π' i x) = π := by
      funext i x
      dsimp [π']
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (hposR i)), one_mul]
    have hscale := hT.scale_coordinates hb (fun i => ⟨1, hπ' i⟩) (fun i => (K i : ℝ))
    rw [heq] at hscale
    rw [hscale, abs_mul, abs_of_nonneg (Finset.prod_nonneg fun i _ => (K i).coe_nonneg)]
    exact mul_le_mul_of_nonneg_left (hμ b π' hb hπ')
      (Finset.prod_nonneg fun i _ => (K i).coe_nonneg)

open scoped BoundedContinuousFunction

omit [MeasurableSpace X] in
noncomputable def BoundedLip.toBoundedContinuous {b : X → ℝ} (hb : BoundedLip b) :
    X →ᵇ ℝ where
  toFun := b
  continuous_toFun := hb.continuous
  map_bounded' := by
    obtain ⟨M, hM⟩ := hb.2
    refine ⟨M + M, fun x y => ?_⟩
    calc dist (b x) (b y) ≤ dist (b x) 0 + dist 0 (b y) := dist_triangle _ _ _
         _ ≤ M + M := by simpa using add_le_add (hM x) (hM y)

variable [BorelSpace X]

lemma continuous_integral_abs_boundedLip {b : X → ℝ} (hb : BoundedLip b) :
    Continuous (fun μ : FiniteMeasure X => ∫ x, |b x| ∂(μ : Measure X)) := by
  let f : X →ᵇ ℝ :=
    { toFun := fun x => |b x|
      continuous_toFun := continuous_abs.comp hb.continuous
      map_bounded' := by
        obtain ⟨M, hM⟩ := hb.2
        refine ⟨M + M, fun x y => ?_⟩
        calc dist |b x| |b y| ≤ dist |b x| 0 + dist 0 |b y| := dist_triangle _ _ _
             _ ≤ M + M := by simpa using add_le_add (hM x) (hM y) }
  apply continuous_iff_continuousAt.mpr
  intro μ
  exact FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp tendsto_id f

lemma isClosed_controls {k : ℕ} (T : Functional X k) :
    IsClosed {μ : FiniteMeasure X | Controls T (μ : Measure X)} := by
  simp only [Controls, ofPred_forall]
  apply isClosed_iInter
  intro b
  apply isClosed_iInter
  intro π
  apply isClosed_iInter
  intro hb
  apply isClosed_iInter
  intro _
  exact isClosed_le continuous_const (continuous_integral_abs_boundedLip hb)

lemma IsMetricCurrent.exists_controls_mass_eq [CompactSpace X] {k : ℕ}
    {T : Functional X k} (hT : IsMetricCurrent T) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ Controls T μ ∧ mass T = μ.real univ := by
  obtain ⟨μ₀, hμ₀, hTμ₀⟩ := hT.finiteMass
  let ν₀ : FiniteMeasure X := ⟨μ₀, hμ₀⟩
  let C : Set (FiniteMeasure X) := {ν | ν.mass ≤ ν₀.mass} ∩ {ν | Controls T (ν : Measure X)}
  have hC : IsCompact C :=
    (isCompact_setOfPred_finiteMeasure_le_of_compactSpace X ν₀.mass).inter_right (isClosed_controls T)
  have hne : C.Nonempty := by
    refine ⟨ν₀, ?_⟩
    change ν₀.mass ≤ ν₀.mass ∧ Controls T (ν₀ : Measure X)
    exact ⟨le_rfl, hTμ₀⟩
  obtain ⟨ν, hν, hmin⟩ := hC.exists_isMinOn hne
    FiniteMeasure.continuous_mass.continuousOn
  change ν.mass ≤ ν₀.mass ∧ Controls T (ν : Measure X) at hν
  have hmin' (η : FiniteMeasure X) (hη : Controls T (η : Measure X)) : ν.mass ≤ η.mass := by
    by_cases hle : η.mass ≤ ν₀.mass
    · exact hmin ⟨hle, hη⟩
    · exact hν.1.trans (le_of_not_ge hle)
  refine ⟨ν, inferInstance, hν.2, le_antisymm (mass_le_measure inferInstance hν.2) ?_⟩
  apply le_csInf
  · exact ⟨μ₀.real univ, μ₀, hμ₀, hTμ₀, rfl⟩
  · rintro r ⟨η, hη, htη, rfl⟩
    exact hmin' ⟨η, hη⟩ htη

end Foundations
end SharpIntegralFillings
end

end OAI
