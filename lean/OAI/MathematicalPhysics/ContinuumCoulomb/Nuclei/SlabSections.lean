import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabRegularization

namespace OAI

/-! Finite product sections of the actual rectangular slab measure. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace ContinuumCoulomb

def slabSide (H S : ℝ) (i : Fin 3) : ℝ := if i = 2 then S else H

def slabAxisMeasure (H S : ℝ) (i : Fin 3) : Measure ℝ :=
  volume.restrict (Set.Icc (-slabSide H S i) (slabSide H S i))

def slabProductMeasure (H S : ℝ) : Measure (Fin 3 → ℝ) :=
  Measure.pi (slabAxisMeasure H S)

def slabProductDomain (H S : ℝ) : Set (Fin 3 → ℝ) :=
  Set.univ.pi (fun i => Set.Icc (-slabSide H S i) (slabSide H S i))

theorem slabProductDomain_preimage (H S : ℝ) :
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm ⁻¹' slabProductDomain H S = slabDomain H S := by
  ext x
  change (∀ i : Fin 3, i ∈ Set.univ → -slabSide H S i ≤ x i ∧ x i ≤ slabSide H S i) ↔
    |x 0| ≤ H ∧ |x 1| ≤ H ∧ |x 2| ≤ S
  simp only [Set.mem_univ, true_implies, abs_le]
  constructor
  · intro h
    exact ⟨by simpa [slabSide] using h 0,
      by simpa [slabSide] using h 1, by simpa [slabSide] using h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · simpa [slabSide] using h0
    · simpa [slabSide] using h1
    · simpa [slabSide] using h2

theorem slabProductMeasure_eq (H S : ℝ) :
    slabProductMeasure H S = (volume : Measure (Fin 3 → ℝ)).restrict (slabProductDomain H S) := by
  exact (Measure.restrict_pi_pi (fun _ : Fin 3 => (volume : Measure ℝ))
    (fun i => Set.Icc (-slabSide H S i) (slabSide H S i))).symm

theorem slabProduct_measurePreserving (H S : ℝ) :
    MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
      (slabProductMeasure H S) (volume.restrict (slabDomain H S)) := by
  have hm := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).restrict_preimage
    (s := slabProductDomain H S)
    (MeasurableSet.univ_pi (fun i => measurableSet_Icc))
  rw [slabProductDomain_preimage, ← slabProductMeasure_eq] at hm
  exact MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm hm

theorem slabProduct_integral (H S : ℝ) (f : Position → ℝ) :
    (∫ x, f (WithLp.toLp 2 x) ∂slabProductMeasure H S) =
      ∫ y in slabDomain H S, f y := by
  exact (slabProduct_measurePreserving H S).integral_comp' f

theorem slabProduct_integrable (H S : ℝ) (f : Position → ℝ) :
    Integrable (fun x => f (WithLp.toLp 2 x)) (slabProductMeasure H S) ↔
      IntegrableOn f (slabDomain H S) :=
  (slabProduct_measurePreserving H S).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding

theorem regularizedKernel_eq_sqrt (epsilon : ℝ) (x : Position) :
    NeutralAtom.regularizedKernel epsilon x = (Real.sqrt (‖x‖^2+epsilon^2))⁻¹ := by
  rw [NeutralAtom.regularizedKernel, Real.sqrt_eq_rpow]
  convert Real.rpow_neg (add_nonneg (sq_nonneg ‖x‖) (sq_nonneg epsilon)) (1/2:ℝ) using 1
  norm_num

theorem regularizedKernel_section (epsilon : ℝ) (y : Position) (i : Fin 3)
    (t : ℝ) (v : Fin 2 → ℝ) :
    NeutralAtom.regularizedKernel epsilon (y-WithLp.toLp 2 (i.insertNth t v)) =
      coulombLineKernel
        (epsilon^2+∑ j : Fin 2, (y (i.succAbove j)-v j)^2) (y i-t) := by
  rw [regularizedKernel_eq_sqrt]
  unfold coulombLineKernel
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succAbove _ i]
  simp only [PiLp.sub_apply, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove]
  ring

instance slabAxisMeasure_finite (H S : ℝ) (i : Fin 3) :
    IsFiniteMeasure (slabAxisMeasure H S i) := by
  unfold slabAxisMeasure
  infer_instance

def zeroPositionCoordinate (i : Fin 3) (y : Position) : Position :=
  WithLp.toLp 2 (Function.update (WithLp.ofLp y) i 0)

theorem zeroPositionCoordinate_same (i : Fin 3) (y : Position) :
    zeroPositionCoordinate i y i = 0 := by simp [zeroPositionCoordinate]

theorem zeroPositionCoordinate_other (i : Fin 3) (y : Position) (j : Fin 2) :
    zeroPositionCoordinate i y (i.succAbove j) = y (i.succAbove j) := by
  simp [zeroPositionCoordinate, Fin.succAbove_ne]

private theorem regularizedProduct_integrable {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) :
    Integrable (fun x : Fin 3 → ℝ => NeutralAtom.regularizedKernel epsilon
      (y-WithLp.toLp 2 x)) (slabProductMeasure H S) :=
  (slabProduct_integrable H S _).mpr (regularizedSlab_integrableOn hepsilon hH hS y)

private theorem regularizedSection_integrable {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    Integrable (fun p : ℝ × (Fin 2 → ℝ) => NeutralAtom.regularizedKernel epsilon
      (y-WithLp.toLp 2 (i.insertNth p.1 p.2)))
      ((slabAxisMeasure H S i).prod
        (Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j)))) := by
  have hp := (measurePreserving_piFinSuccAbove (slabAxisMeasure H S) i).symm
  have h := (hp.integrable_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm.measurableEmbedding).mpr
    (regularizedProduct_integrable hepsilon hH hS y)
  exact h

theorem regularizedSlab_sectionIntegral {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    (∫ x in slabDomain H S, NeutralAtom.regularizedKernel epsilon (y-x)) =
      ∫ v : Fin 2 → ℝ, ∫ t : ℝ,
        NeutralAtom.regularizedKernel epsilon (y-WithLp.toLp 2 (i.insertNth t v))
        ∂slabAxisMeasure H S i
        ∂Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j)) := by
  rw [← slabProduct_integral H S (fun x => NeutralAtom.regularizedKernel epsilon (y-x))]
  change (∫ x : Fin 3 → ℝ, NeutralAtom.regularizedKernel epsilon (y-WithLp.toLp 2 x)
    ∂Measure.pi (slabAxisMeasure H S)) = _
  rw [← ((measurePreserving_piFinSuccAbove (slabAxisMeasure H S) i).symm).integral_comp']
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  exact integral_prod_symm _ (regularizedSection_integrable hepsilon hH hS y i)

private theorem coulombLine_setIntegral_le_center {A H : ℝ} (hA : 0 < A) (hH : 0 ≤ H)
    (x : ℝ) :
    (∫ t in Set.Icc (-H) H, coulombLineKernel A (x-t)) ≤
      ∫ t in Set.Icc (-H) H, coulombLineKernel A (0-t) := by
  have h := coulombLineIntegral_le_center hA hH x
  simp only [centeredLineIntegral_translate,
    intervalIntegral.integral_of_le (show -H ≤ H by linarith),
    ← integral_Icc_eq_integral_Ioc] at h
  exact h

/-- Centering one coordinate increases the attractive Coulomb integral.
The statement holds for the actual finite slab, before taking the singular limit. -/
theorem regularizedSlab_coordinate_max {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    (∫ x in slabDomain H S, NeutralAtom.regularizedKernel epsilon (y-x)) ≤
      ∫ x in slabDomain H S, NeutralAtom.regularizedKernel epsilon
        (zeroPositionCoordinate i y-x) := by
  rw [regularizedSlab_sectionIntegral hepsilon hH hS y i,
    regularizedSlab_sectionIntegral hepsilon hH hS (zeroPositionCoordinate i y) i]
  apply integral_mono
    (regularizedSection_integrable hepsilon hH hS y i).integral_prod_right
    (regularizedSection_integrable hepsilon hH hS (zeroPositionCoordinate i y) i).integral_prod_right
  intro v
  simp_rw [regularizedKernel_section, zeroPositionCoordinate_same, zeroPositionCoordinate_other]
  have hA : 0 < epsilon^2+∑ j : Fin 2, (y (i.succAbove j)-v j)^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hepsilon)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hside : 0 ≤ slabSide H S i := by unfold slabSide; split <;> assumption
  exact coulombLine_setIntegral_le_center hA hside (y i)

/-- The actual singular finite-slab potential is minimized in each centered
coordinate. The regularized comparison passes through a dominated limit. -/
theorem slabPotential_coordinate_min {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    slabPotential rho H S (zeroPositionCoordinate i y) ≤ slabPotential rho H S y := by
  let epsilon : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hep (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have heps : Tendsto epsilon atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  apply le_of_tendsto_of_tendsto
    (regularizedSlabPotential_tendsto hep heps rho hH hS (zeroPositionCoordinate i y))
    (regularizedSlabPotential_tendsto hep heps rho hH hS y)
  exact Filter.Eventually.of_forall (fun n =>
    mul_le_mul_of_nonpos_left (regularizedSlab_coordinate_max (hep n).ne' hH hS y i)
      (neg_nonpos.mpr hrho))

theorem slabPotential_minimum {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) :
    slabPotential rho H S 0 ≤ slabPotential rho H S y := by
  have h0 := slabPotential_coordinate_min hrho hH hS y 0
  have h1 := slabPotential_coordinate_min hrho hH hS (zeroPositionCoordinate 0 y) 1
  have h2 := slabPotential_coordinate_min hrho hH hS
    (zeroPositionCoordinate 1 (zeroPositionCoordinate 0 y)) 2
  have he : zeroPositionCoordinate 2 (zeroPositionCoordinate 1 (zeroPositionCoordinate 0 y)) = 0 := by
    ext j
    fin_cases j <;> simp [zeroPositionCoordinate]
  rw [he] at h2
  exact h2.trans (h1.trans h0)

theorem slabPotential_nonpositive {rho : ℝ} (hrho : 0 ≤ rho) (H S : ℝ) (y : Position) :
    slabPotential rho H S y ≤ 0 := by
  rw [slabPotential_eq_setIntegral]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hrho)
    (integral_nonneg (fun x => inv_nonneg.mpr (norm_nonneg (y-x))))

end ContinuumCoulomb

end

end OAI
