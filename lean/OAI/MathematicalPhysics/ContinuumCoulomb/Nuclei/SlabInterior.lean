import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabConfinement
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabLineFlatness

namespace OAI

/-! Interior horizontal flatness and the full finite-slab approximation. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

private theorem coulombLine_setIntegral_variation {A H x : ℝ} (hA : 0 < A)
    (hH : 0 < H) (hx : |x| ≤ H/2) :
    |(∫ t in Set.Icc (-H) H, coulombLineKernel A (x-t))-
      (∫ t in Set.Icc (-H) H, coulombLineKernel A (0-t))| ≤ 16*x^2/H^2 := by
  have h := coulombLineIntegral_quadratic_variation hA hH hx
  simp only [centeredLineIntegral_translate,
    intervalIntegral.integral_of_le (show -H ≤ H by linarith),
    ← integral_Icc_eq_integral_Ioc] at h
  exact h

private theorem slabOtherMeasure_mass {H S : ℝ} (hH : 0 ≤ H) (hS : 0 ≤ S)
    (i : Fin 3) (hi : i ≠ 2) :
    (Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j))).real Set.univ = 4*H*S := by
  rw [Measure.real, Measure.pi_univ, Fin.prod_univ_two, ENNReal.toReal_mul]
  simp only [slabAxisMeasure, Measure.restrict_apply_univ, Real.volume_Icc]
  fin_cases i
  · norm_num [slabSide, Fin.succAbove, ENNReal.toReal_ofReal, hH, hS]
    ring
  · norm_num [slabSide, Fin.succAbove, ENNReal.toReal_ofReal, hH, hS]
    ring
  · exact (hi rfl).elim

private theorem slabInteriorSection_integrable {epsilon H S : ℝ} (hepsilon : epsilon ≠ 0)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) :
    Integrable (fun v : Fin 2 → ℝ => ∫ t : ℝ,
      NeutralAtom.regularizedKernel epsilon (y-WithLp.toLp 2 (i.insertNth t v))
      ∂slabAxisMeasure H S i)
      (Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j))) := by
  have hp := (measurePreserving_piFinSuccAbove (slabAxisMeasure H S) i).symm
  have hi := (hp.integrable_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm.measurableEmbedding).mpr
      ((slabProduct_integrable H S _).mpr (regularizedSlab_integrableOn hepsilon hH hS y))
  exact hi.integral_prod_right

private theorem regularizedSlab_coordinate_variation {epsilon rho H S : ℝ}
    (hepsilon : epsilon ≠ 0) (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 ≤ S)
    (y : Position) (i : Fin 3) (hi : i ≠ 2) (hy : |y i| ≤ H/2) :
    |regularizedSlabPotential epsilon rho H S y-
      regularizedSlabPotential epsilon rho H S (zeroPositionCoordinate i y)| ≤
        64*rho*S*(y i)^2/H := by
  let mu := Measure.pi (fun j : Fin 2 => slabAxisMeasure H S (i.succAbove j))
  let F := fun (v : Fin 2 → ℝ) => ∫ t : ℝ,
    NeutralAtom.regularizedKernel epsilon (y-WithLp.toLp 2 (i.insertNth t v))
    ∂slabAxisMeasure H S i
  let G := fun (v : Fin 2 → ℝ) => ∫ t : ℝ,
    NeutralAtom.regularizedKernel epsilon (zeroPositionCoordinate i y-
      WithLp.toLp 2 (i.insertNth t v)) ∂slabAxisMeasure H S i
  have hF : Integrable F mu := slabInteriorSection_integrable hepsilon hH.le hS y i
  have hG : Integrable G mu :=
    slabInteriorSection_integrable hepsilon hH.le hS (zeroPositionCoordinate i y) i
  have hb (v : Fin 2 → ℝ) : ‖F v-G v‖ ≤ 16*(y i)^2/H^2 := by
    dsimp only [F, G]
    simp_rw [regularizedKernel_section, zeroPositionCoordinate_same, zeroPositionCoordinate_other]
    have hA : 0 < epsilon^2+∑ j : Fin 2, (y (i.succAbove j)-v j)^2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hepsilon)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    rw [Real.norm_eq_abs]
    change |(∫ t in Set.Icc (-slabSide H S i) (slabSide H S i),
      coulombLineKernel _ (y i-t))-(∫ t in Set.Icc (-slabSide H S i) (slabSide H S i),
      coulombLineKernel _ (0-t))| ≤ _
    rw [show slabSide H S i = H by simp [slabSide, hi]]
    exact coulombLine_setIntegral_variation hA hH hy
  have hI : |(∫ v, F v ∂mu)-(∫ v, G v ∂mu)| ≤ (16*(y i)^2/H^2)*(4*H*S) := by
    rw [← integral_sub hF hG, ← Real.norm_eq_abs]
    have h := norm_integral_le_of_norm_le_const (μ := mu) (f := fun v => F v-G v)
      (Filter.Eventually.of_forall hb)
    simpa only [mu, slabOtherMeasure_mass hH.le hS i hi] using h
  unfold regularizedSlabPotential
  rw [regularizedSlab_sectionIntegral hepsilon hH.le hS y i,
    regularizedSlab_sectionIntegral hepsilon hH.le hS (zeroPositionCoordinate i y) i,
    ← mul_sub, abs_mul, abs_neg, abs_of_nonneg hrho]
  change rho*|(∫ v, F v ∂mu)-(∫ v, G v ∂mu)| ≤ _
  apply (mul_le_mul_of_nonneg_left hI hrho).trans_eq
  field_simp
  ring

theorem slabPotential_coordinate_variation {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 < H) (hS : 0 ≤ S) (y : Position) (i : Fin 3) (hi : i ≠ 2)
    (hy : |y i| ≤ H/2) :
    |slabPotential rho H S y-slabPotential rho H S (zeroPositionCoordinate i y)| ≤
      64*rho*S*(y i)^2/H := by
  let epsilon : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hep (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have heps : Tendsto epsilon atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hlim := ((regularizedSlabPotential_tendsto hep heps rho hH.le hS y).sub
    (regularizedSlabPotential_tendsto hep heps rho hH.le hS (zeroPositionCoordinate i y))).abs
  exact le_of_tendsto hlim (Filter.Eventually.of_forall (fun n =>
    regularizedSlab_coordinate_variation (hep n).ne' hrho hH hS y i hi hy))

theorem slabPotential_horizontal_variation {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 < H) (hS : 0 ≤ S) (y : Position)
    (hy0 : |y 0| ≤ H/2) (hy1 : |y 1| ≤ H/2) :
    |slabPotential rho H S y-slabPotential rho H S (slabAxisPoint (y 2))| ≤
      64*rho*S*((y 0)^2+(y 1)^2)/H := by
  have h0 := slabPotential_coordinate_variation hrho hH hS y 0 (by decide) hy0
  have h1 := slabPotential_coordinate_variation hrho hH hS (zeroPositionCoordinate 0 y) 1
    (by decide) (by simpa [zeroPositionCoordinate] using hy1)
  have he : zeroPositionCoordinate 1 (zeroPositionCoordinate 0 y) = slabAxisPoint (y 2) := by
    ext j
    fin_cases j <;> simp [zeroPositionCoordinate, slabAxisPoint]
  rw [he] at h1
  have hcoord : zeroPositionCoordinate 0 y 1 = y 1 := by simp [zeroPositionCoordinate]
  rw [hcoord] at h1
  calc
    _ ≤ |slabPotential rho H S y-slabPotential rho H S (zeroPositionCoordinate 0 y)|+
        |slabPotential rho H S (zeroPositionCoordinate 0 y)-slabPotential rho H S (slabAxisPoint (y 2))| :=
      abs_sub_le _ _ _
    _ ≤ 64*rho*S*(y 0)^2/H+64*rho*S*(y 1)^2/H := add_le_add h0 h1
    _ = _ := by ring

/-- The finite slab approximates the harmonic potential throughout its
central horizontal half-box and vertical thickness. -/
theorem slabPotential_interior_error {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 < H) (hS : 0 ≤ S) (y : Position)
    (hy0 : |y 0| ≤ H/2) (hy1 : |y 1| ≤ H/2) (hy2 : |y 2| ≤ S) :
    |slabPotential rho H S y-slabPotential rho H S 0-2*Real.pi*rho*(y 2)^2| ≤
      64*rho*S*((y 0)^2+(y 1)^2)/H+6*Real.pi*rho*S^3/H := by
  have h0 := slabPotential_horizontal_variation hrho hH hS y hy0 hy1
  have h1 := slabPotential_axis_error hrho hH hS hy2
  calc
    _ = |(slabPotential rho H S y-slabPotential rho H S (slabAxisPoint (y 2)))+
        (slabPotential rho H S (slabAxisPoint (y 2))-slabPotential rho H S 0-
          2*Real.pi*rho*(y 2)^2)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add h0 h1)

end ContinuumCoulomb

end

end OAI
