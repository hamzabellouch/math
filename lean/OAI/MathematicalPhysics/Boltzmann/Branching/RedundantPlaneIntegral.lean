import OAI.MathematicalPhysics.Boltzmann.Branching.FiveGainRank
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

section

/-! # A nonsingular three-dimensional coordinate map for a collision plane

The third coordinate is the coefficient of the normal, rather than distance
along the unit normal. This normalization cancels the length of the normal in
the redundant-parameter density. The transverse normal must be nonzero, just
as in the graph chart used by the actual gain kernel.
-/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix ENNReal

namespace BoltzmannNonuniqueness.RedundantPlane

abbrev V := Fin 3 → ℝ

def normSq (n : V) : ℝ := n 0^2+n 1^2+n 2^2

def coordinateMatrix (n : V) (r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-n 1, n 0, 0;
      n 0*n 2/r, n 1*n 2/r, -(n 0^2+n 1^2)/r;
      n 0/normSq n, n 1/normSq n, n 2/normSq n]

def coordinates (n : V) (r : ℝ) : V →ₗ[ℝ] V := (coordinateMatrix n r).toLin'

theorem normSq_pos {n : V} {r : ℝ} (hr : 0 < r)
    (hrsq : r^2 = n 0^2+n 1^2) : 0 < normSq n := by
  unfold normSq
  nlinarith [sq_nonneg (n 2),sq_pos_of_pos hr]

theorem coordinateMatrix_det {n : V} {r : ℝ} (hr : 0 < r)
    (hrsq : r^2 = n 0^2+n 1^2) : (coordinateMatrix n r).det = -r := by
  have hD := (normSq_pos hr hrsq).ne'
  simp [coordinateMatrix,Matrix.det_fin_three]
  field_simp
  unfold normSq at *
  linear_combination (n 0^2+n 1^2+n 2^2)*hrsq

theorem coordinates_apply (n L : V) (r : ℝ) :
    coordinates n r L = ![n 0*L 1-n 1*L 0,
      (n 2*(n 0*L 0+n 1*L 1)-(n 0^2+n 1^2)*L 2)/r,
      (n 0*L 0+n 1*L 1+n 2*L 2)/normSq n] := by
  ext i
  fin_cases i <;> simp [coordinates,coordinateMatrix,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail] <;> ring

theorem cross_coordinates {n L : V} {r : ℝ} (hr : 0 < r)
    (hrsq : r^2 = n 0^2+n 1^2) :
    n ⨯₃ L = ![-n 0*n 2/r^2*(coordinates n r L) 0-n 1/r*(coordinates n r L) 1,
      -n 1*n 2/r^2*(coordinates n r L) 0+n 0/r*(coordinates n r L) 1,
      (coordinates n r L) 0] := by
  rw [coordinates_apply]
  ext i
  fin_cases i <;> simp [cross_apply]
  · field_simp
    nlinarith [congrArg (fun x : ℝ => x*(n 1*L 2-n 2*L 1)) hrsq]
  · field_simp
    nlinarith [congrArg (fun x : ℝ => x*(n 2*L 0-n 0*L 2)) hrsq]

theorem coordinates_map_volume {n : V} {r : ℝ} (hr : 0 < r)
    (hrsq : r^2 = n 0^2+n 1^2) :
    Measure.map (coordinates n r) volume = ENNReal.ofReal r⁻¹ • volume := by
  have hd := coordinateMatrix_det hr hrsq
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi (hd.trans_ne (neg_ne_zero.mpr hr.ne'))
  simpa only [coordinates,hd,inv_neg,abs_neg,abs_of_pos (inv_pos.mpr hr)] using h

end BoltzmannNonuniqueness.RedundantPlane

end

end

section

/-! # Bounded redundant parameters for bounded collision increments -/

noncomputable section

open Matrix MeasureTheory Set
open scoped Matrix ENNReal

namespace BoltzmannNonuniqueness.RedundantPlane

def normalDensity : ℝ → ℝ≥0∞ := (Icc 0 1).indicator (fun _ => 1)

theorem measurable_normalDensity : Measurable normalDensity :=
  measurable_const.indicator measurableSet_Icc

theorem normalDensity_le_one (x : ℝ) : normalDensity x ≤ 1 :=
  indicator_le_self' (fun _ _ => bot_le) x

theorem normalDensity_support {x : ℝ} (hx : normalDensity x ≠ 0) : x ∈ Icc 0 1 := by
  by_contra h
  exact hx (indicator_of_notMem h _)

theorem lintegral_normalDensity : ∫⁻ x, normalDensity x = 1 := by
  rw [normalDensity,lintegral_indicator_const measurableSet_Icc]
  simp

theorem normSq_nonneg (n : V) : 0 ≤ normSq n := by
  unfold normSq
  positivity

theorem cross_normSq_identity (n L : V) :
    normSq n * normSq L = normSq (n ⨯₃ L)+(n ⬝ᵥ L)^2 := by
  simp [normSq,cross_apply,vec3_dotProduct]
  ring

theorem coordinates_last (n L : V) (r : ℝ) :
    coordinates n r L 2 = (n ⬝ᵥ L)/normSq n := by
  simp [coordinates_apply,vec3_dotProduct]

theorem normSq_decomposition {n L : V} {r : ℝ} (hD : normSq n ≠ 0) :
    normSq L = normSq (n ⨯₃ L)/normSq n+
      normSq n*(coordinates n r L 2)^2 := by
  rw [coordinates_last]
  field_simp
  nlinarith only [cross_normSq_identity n L]

theorem normSq_parameter_bound {n L : V} {r δ R R₁ : ℝ}
    (hδ : 0 < δ) (hnlow : δ^2 ≤ normSq n) (hnhigh : normSq n ≤ R^2)
    (hk : normSq (n ⨯₃ L) ≤ R₁^2)
    (hcoef : |coordinates n r L 2| ≤ 1) :
    normSq L ≤ R₁^2/δ^2+R^2 := by
  have hD : 0 < normSq n := (sq_pos_of_pos hδ).trans_le hnlow
  rw [normSq_decomposition hD.ne']
  have hcoefsq : (coordinates n r L 2)^2 ≤ 1 := by
    nlinarith [sq_abs (coordinates n r L 2),abs_nonneg (coordinates n r L 2)]
  apply add_le_add
  · exact (div_le_div_of_nonneg_right hk hD.le).trans
      (div_le_div_of_nonneg_left (sq_nonneg R₁) (sq_pos_of_pos hδ) hnlow)
  · exact (mul_le_of_le_one_right hD.le hcoefsq).trans hnhigh

end BoltzmannNonuniqueness.RedundantPlane

end

end

section

/-! # Integrating the redundant coordinate in the collision plane -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix ENNReal

namespace BoltzmannNonuniqueness.RedundantPlane

def splitThree : V ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)))

theorem splitThree_apply (q : V) : splitThree q = (q 0,(q 1,q 2)) := by
  rfl

theorem splitThree_measurePreserving : MeasurePreserving splitThree := by
  exact (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurePreserving.id volume).prod (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)))

theorem lintegral_redundant {ζ : ℝ → ℝ≥0∞} (hζ : Measurable ζ)
    (hζone : ∫⁻ u, ζ u = 1) {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q : V, ζ (q 2)*F (q 0,q 1)) = ∫⁻ z : ℝ, ∫⁻ s : ℝ, F (z,s) := by
  let g : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun q => ζ q.2.2 * F (q.1,q.2.1)
  have hg : Measurable g := (hζ.comp measurable_snd.snd).mul
    (hF.comp (measurable_fst.prodMk measurable_snd.fst))
  have he : (fun q : V => ζ (q 2)*F (q 0,q 1)) = g ∘ splitThree := rfl
  rw [he]
  change (∫⁻ q : V, g (splitThree q)) = _
  rw [splitThree_measurePreserving.lintegral_comp hg]
  change (∫⁻ q, g q ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume))) = _
  rw [lintegral_prod _ hg.aemeasurable]
  apply lintegral_congr
  intro z
  change (∫⁻ q, g (z,q) ∂((volume : Measure ℝ).prod volume)) = _
  have hz : Measurable (fun q : ℝ × ℝ => g (z,q)) := hg.comp measurable_prodMk_left
  rw [lintegral_prod _ hz.aemeasurable]
  apply lintegral_congr
  intro s
  change (∫⁻ u : ℝ, ζ u * F (z,s)) = F (z,s)
  rw [lintegral_mul_const _ hζ,hζone,one_mul]

theorem redundant_coordinates_integral {n : V} {r : ℝ} (hr : 0 < r)
    (hrsq : r^2 = n 0^2+n 1^2) {ζ : ℝ → ℝ≥0∞} (hζ : Measurable ζ)
    (hζone : ∫⁻ u, ζ u = 1) {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ L : V, ζ (coordinates n r L 2)*F (coordinates n r L 0,coordinates n r L 1)) =
      ENNReal.ofReal r⁻¹ * ∫⁻ z : ℝ, ∫⁻ s : ℝ, F (z,s) := by
  let g : V → ℝ≥0∞ := fun q => ζ (q 2)*F (q 0,q 1)
  have hg : Measurable g := (hζ.comp (measurable_pi_apply 2)).mul
    (hF.comp ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1)))
  have hA : Measurable (coordinates n r) := (coordinates n r).continuous_of_finiteDimensional.measurable
  have he := lintegral_map (μ := (volume : Measure V)) hg hA
  rw [coordinates_map_volume hr hrsq,lintegral_smul_measure] at he
  simpa only [g,Function.comp_def,smul_eq_mul,lintegral_redundant hζ hζone hF] using he.symm

end BoltzmannNonuniqueness.RedundantPlane

end

end

end OAI
