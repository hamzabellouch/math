import OAI.Analysis.CircleDomains.Sobolev.GramMetric
import OAI.Analysis.CircleDomains.Topology.ThinCollar

namespace OAI

/-!
# Keeping the original metric near the retained core

The interpolated metric is an actual positive definite matrix field.
Its coordinate energy is the inverse-matrix energy density, rather than
an independently supplied scalar surrogate.
-/

open Matrix Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

abbrev PlanarMetric := Matrix (Fin 2) (Fin 2) ℝ

def matrixEnergy (A g : PlanarMetric) : ℝ :=
  Matrix.trace (g⁻¹ * A) * Real.sqrt g.det

def blendMetric (g : PlanarMetric) (t : ℝ) : PlanarMetric :=
  (1 - t) • 1 + t • g

@[simp] theorem blendMetric_zero (g : PlanarMetric) : blendMetric g 0 = 1 := by
  simp [blendMetric]

@[simp] theorem blendMetric_one (g : PlanarMetric) : blendMetric g 1 = g := by
  simp [blendMetric]

theorem blendMetric_posDef {g : PlanarMetric} (hg : g.PosDef)
    {t : ℝ} (ht : t ∈ Icc 0 1) : (blendMetric g t).PosDef := by
  by_cases hz : t = 0
  · simpa only [hz, blendMetric_zero] using (Matrix.PosDef.one : (1 : PlanarMetric).PosDef)
  · exact Matrix.PosDef.posSemidef_add
      (Matrix.PosSemidef.one.smul (sub_nonneg.mpr ht.2))
      (hg.smul (lt_of_le_of_ne ht.1 (Ne.symm hz)))

theorem continuousOn_matrixEnergy
    {X : Type*} [TopologicalSpace X] {D : Set X}
    {A g : X → PlanarMetric} (hA : Continuous A) (hg : Continuous g)
    (hPD : ∀ x ∈ D, (g x).PosDef) :
    ContinuousOn (fun x => matrixEnergy (A x) (g x)) D := by
  have hi : ContinuousOn (fun x => (g x).det⁻¹) D :=
    hg.matrix_det.continuousOn.inv₀ (fun x hx => (hPD x hx).det_pos.ne')
  have hiMat : ContinuousOn (fun x => (g x).det⁻¹ • (g x).adjugate) D :=
    hi.smul hg.matrix_adjugate.continuousOn
  have hm : ContinuousOn (fun x => ((g x).det⁻¹ • (g x).adjugate) * A x) D :=
    hiMat.mul hA.continuousOn
  have ht : ContinuousOn (fun x => Matrix.trace (((g x).det⁻¹ • (g x).adjugate) * A x)) D :=
    (continuous_id.matrix_trace : Continuous (Matrix.trace : PlanarMetric → ℝ)).comp_continuousOn hm
  simpa only [matrixEnergy, Matrix.inv_def, Ring.inverse_eq_inv, Pi.mul_def] using
    ht.mul hg.matrix_det.sqrt.continuousOn

/-- Replace a smooth positive definite metric by the identity near a compact
core. The change of the actual coordinate energy outside that core is small.
The transition can be confined to any prescribed open neighborhood. -/
theorem exists_core_preserving_metric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    {K S U : Set E} (hK : IsCompact K) (hS : Bornology.IsBounded S)
    (hSm : MeasurableSet S) (hU : IsOpen U) (hKU : K ⊆ U)
    (A g : E → PlanarMetric) (hA : Continuous A) (hg : ContDiff ℝ ∞ g)
    (hPD : ∀ x, (g x).PosDef) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : Set E) (g' : E → PlanarMetric), IsOpen N ∧ K ⊆ N ∧ N ⊆ U ∧
      ContDiff ℝ ∞ g' ∧ (∀ x, (g' x).PosDef) ∧
      (∀ᶠ x in 𝓝ˢ K, g' x = 1) ∧ (∀ x ∉ N, g' x = g x) ∧
      (∫ x in S \ K, |matrixEnergy (A x) (g' x) - matrixEnergy (A x) (g x)| ∂μ) < ε := by
  let H : E × ℝ → ℝ := fun p => matrixEnergy (A p.1) (blendMetric (g p.1) p.2)
  have hblend : Continuous (fun p : E × ℝ => blendMetric (g p.1) p.2) := by
    unfold blendMetric
    fun_prop
  have hH : ContinuousOn H (univ ×ˢ Icc 0 1) :=
    continuousOn_matrixEnergy (hA.comp continuous_fst) hblend
      (fun p hp => blendMetric_posDef (hPD p.1) hp.2)
  obtain ⟨N, χ, hN, hKN, hNU, hχ, hrange, hzero, hone, hchange⟩ :=
    exists_smooth_interpolation_small_change (μ := μ) hK hS hSm hU hKU H hH hε
  let g' : E → PlanarMetric := fun x => blendMetric (g x) (χ x)
  refine ⟨N, g', hN, hKN, hNU, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [g', blendMetric]
    exact (contDiff_const.sub hχ).smul contDiff_const |>.add (hχ.smul hg)
  · exact fun x => blendMetric_posDef (hPD x) (hrange x)
  · filter_upwards [hzero] with x hx
    simp only [g', hx, blendMetric_zero]
  · intro x hx
    simp only [g', hone x hx, blendMetric_one]
  · simpa only [H, g', blendMetric_one] using hchange

theorem continuous_matrixEnergy
    {X : Type*} [TopologicalSpace X] {A g : X → PlanarMetric}
    (hA : Continuous A) (hg : Continuous g) (hPD : ∀ x, (g x).PosDef) :
    Continuous (fun x => matrixEnergy (A x) (g x)) :=
  continuousOn_univ.mp (continuousOn_matrixEnergy hA hg (fun x _ => hPD x))

theorem integral_lt_of_abs_sub_lt
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) {ε b : ℝ}
    (hchange : (∫ x, |f x - g x| ∂μ) < ε)
    (hbase : (∫ x, g x ∂μ) < b) :
    (∫ x, f x ∂μ) < b + ε := by
  have hle : (∫ x, f x ∂μ) - (∫ x, g x ∂μ) ≤ ∫ x, |f x - g x| ∂μ := by
    rw [← integral_sub hf hg]
    exact integral_mono (hf.sub hg) (hf.sub hg).abs (fun x => le_abs_self _)
  linarith

/-- The complete local metric step: small pairwise wedges give one smooth
positive definite metric with the prescribed total energy bound, equal to
the original identity metric on a full neighborhood of the retained core.
The constant regularization and the transition region are both constructed.
-/
theorem exists_smooth_core_gramMetric
    (x y : ℕ → (ℝ × ℝ) → ℝ) (n : ℕ)
    (hx : ∀ i, ContDiff ℝ ∞ (x i)) (hy : ∀ i, ContDiff ℝ ∞ (y i))
    {K S U : Set (ℝ × ℝ)} (hK : IsCompact K) (hS : Bornology.IsBounded S)
    (hSm : MeasurableSet S) (hU : IsOpen U) (hKU : K ⊆ U) {ε : ℝ}
    (hε : (∫ z in S \ K, 2 * covectorWedges (fun i => x i z) (fun i => y i z) n) < ε) :
    ∃ (τ : ℝ) (N : Set (ℝ × ℝ)) (g : (ℝ × ℝ) → PlanarMetric),
      0 < τ ∧ IsOpen N ∧ K ⊆ N ∧ N ⊆ U ∧ ContDiff ℝ ∞ g ∧
      (∀ z, (g z).PosDef) ∧ (∀ᶠ z in 𝓝ˢ K, g z = 1) ∧
      (∀ z ∉ N, g z = gramTensor (fun i => x i z) (fun i => y i z) n + τ • 1) ∧
      (∫ z in S \ K, matrixEnergy (gramTensor (fun i => x i z) (fun i => y i z) n) (g z)) < ε := by
  let A := fun z => gramTensor (fun i => x i z) (fun i => y i z) n
  obtain ⟨τ, hτ, hreg, hPD, henergy⟩ := exists_smooth_gramMetric_on_bounded x y n hx hy
    (hS.subset sdiff_subset) hε
  let g₀ := fun z => A z + τ • 1
  change ContDiff ℝ ∞ g₀ at hreg
  change (∫ z in S \ K, matrixEnergy (A z) (g₀ z)) < ε at henergy
  have hAc : Continuous A := by
    have h := hreg.continuous.sub (continuous_const (y := τ • (1 : PlanarMetric)))
    change Continuous (fun z => A z + τ • 1 - τ • 1) at h
    simpa only [add_sub_cancel_right] using h
  have hci := continuous_matrixEnergy hAc hreg.continuous hPD
  let I := ∫ z in S \ K, matrixEnergy (A z) (g₀ z)
  obtain ⟨N, g, hN, hKN, hNU, hg, hgPD, hcore, hout, hchange⟩ :=
    exists_core_preserving_metric (μ := volume) hK hS hSm hU hKU A g₀ hAc hreg hPD
      (sub_pos.mpr henergy)
  have hgi := continuous_matrixEnergy hAc hg.continuous hgPD
  have hbasei : IntegrableOn (fun z => matrixEnergy (A z) (g₀ z)) (S \ K) :=
    (hci.continuousOn.integrableOn_compact hS.isCompact_closure).mono_set
      (sdiff_subset.trans subset_closure)
  have hnewi : IntegrableOn (fun z => matrixEnergy (A z) (g z)) (S \ K) :=
    (hgi.continuousOn.integrableOn_compact hS.isCompact_closure).mono_set
      (sdiff_subset.trans subset_closure)
  refine ⟨τ, N, g, hτ, hN, hKN, hNU, hg, hgPD, hcore, hout, ?_⟩
  have hle : (∫ z in S \ K, matrixEnergy (A z) (g z)) - I ≤
      ∫ z in S \ K, |matrixEnergy (A z) (g z) - matrixEnergy (A z) (g₀ z)| := by
    dsimp only [I]
    rw [← integral_sub hnewi hbasei]
    exact integral_mono (hnewi.sub hbasei) (hnewi.sub hbasei).abs
      (fun _ => le_abs_self _)
  change (∫ z in S \ K, |matrixEnergy (A z) (g z) - matrixEnergy (A z) (g₀ z)|) < ε - I
    at hchange
  linarith

end CircleDomainRigidity.FiniteTransfer

end

end OAI
