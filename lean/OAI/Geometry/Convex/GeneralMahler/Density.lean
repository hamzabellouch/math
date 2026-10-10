import OAI.Geometry.Convex.GeneralMahler.Cone
import OAI.Geometry.Convex.GeneralMahler.Growth

namespace OAI
/-! The Gaussian integrations in §§02--06: Lebesgue density and
translation/scaling dictionary. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real WithLp ProbabilityTheory
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace GeneralMahler

abbrev normal (n : ℕ) := stdGaussian (Rn n)

abbrev gamma : Measure ℝ := gaussianReal 0 1
def phi := gaussianPDFReal 0 1
variable {n : ℕ}

lemma phi_apply (t : ℝ) : phi t = (√(2 * π))⁻¹ * Real.exp (-(t ^ 2)/2) := by
  simp [phi, gaussianPDFReal]

lemma phi_pos (t : ℝ) : 0 < phi t := gaussianPDFReal_pos _ _ _ one_ne_zero

def nDensity (x : Rn n) := (√(2 * π))⁻¹ ^ n * Real.exp (-(‖x‖^2)/2)
lemma nDensity_pos (x : Rn n) : 0 < nDensity x := by
  unfold nDensity; positivity

@[fun_prop] lemma continuous_nDensity : Continuous (@nDensity n) := by
  unfold nDensity; fun_prop

lemma nDensity_prod (x : Fin n → ℝ) :
    nDensity (WithLp.toLp 2 x) = ∏ i, phi (x i) := by
  simp_rw [phi_apply, Finset.prod_mul_distrib, ← Real.exp_sum]
  simp only [nDensity, EuclideanSpace.real_norm_sq_eq, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Finset.sum_div, Finset.sum_neg_distrib]

lemma gaussian_pi_density :
    Measure.pi (fun _ : Fin n => gamma) =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, phi (x i))) := by
  have hf : Integrable phi := integrable_gaussianPDFReal _ _
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  let u := fun (i : Fin n) => (volume : Measure ℝ).restrict (s i)
  change (∫⁻ x in _, _ ∂Measure.pi _) = _
  rw [Measure.restrict_pi_pi]
  have h : Integrable (fun x : Fin n → ℝ => ∏ i, phi (x i)) (Measure.pi u) :=
    Integrable.fintype_prod (E := ℝ) (fun _ => hf.integrableOn)
  let v := fun i : Fin n => ∫ x, phi x ∂u i
  have Hv (i : Fin n) : 0 ≤ v i := integral_nonneg fun x => (phi_pos _).le
  change (∫⁻ x, _ ∂Measure.pi u) = _
  rw [← ofReal_integral_eq_lintegral_ofReal h (ae_of_all _ fun x =>
      Finset.prod_nonneg (fun i _ => (phi_pos _).le)), integral_fintype_prod_eq_prod]
  change ENNReal.ofReal (∏ i, v i) = _
  rw [ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro i _
    exact (gaussianReal_apply_eq_integral _ one_ne_zero _).symm
  · exact fun i _ => Hv i

theorem normal_density :
    normal n = volume.withDensity (fun x => ENNReal.ofReal (nDensity x)) := by
  let T := MeasurableEquiv.toLp 2 (Fin n → ℝ)
  have hT : MeasurePreserving T := PiLp.volume_preserving_toLp _
  have he : normal n = (Measure.pi (fun _ : Fin n => gamma)).map T :=
    ProbabilityTheory.map_pi_eq_stdGaussian.symm
  rw [he, gaussian_pi_density]
  ext s hs
  rw [Measure.map_apply T.measurable hs, withDensity_apply _ hs, withDensity_apply _ (T.measurable hs)]

  have hsd := setLIntegral_map (μ := volume) (g := (T : _ → Rn n)) hs
    (show Measurable (fun x:Rn n => ENNReal.ofReal (nDensity x)) by fun_prop) T.measurable
  rw [hT.map_eq] at hsd
  rw [hsd]
  apply lintegral_congr
  intro x
  change ENNReal.ofReal _ = ENNReal.ofReal (nDensity (WithLp.toLp 2 x))
  rw [nDensity_prod]

theorem normal_ac : normal n ≪ (volume : Measure (Rn n)) := by
  rw [normal_density]; exact withDensity_absolutelyContinuous _ _

theorem ac_normal : (volume : Measure (Rn n)) ≪ normal n := by
  rw [normal_density]
  apply withDensity_absolutelyContinuous' (by fun_prop)
  exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (nDensity_pos x)).ne'

section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem normal_integral (f : Rn n → F) : ∫ x, f x ∂(normal n) = ∫ x, nDensity x • f x := by
  rw [normal_density, integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
  simp only [ENNReal.toReal_ofReal (nDensity_pos _).le]

lemma normal_integrable_iff {f : Rn n → F} :
    Integrable f (normal n) ↔ Integrable (fun x => nDensity x • f x) := by
  rw [normal_density, integrable_withDensity_iff_integrable_smul' (by fun_prop) (by simp)]
  simp only [ENNReal.toReal_ofReal (nDensity_pos _).le]
end
end GeneralMahler

end

end OAI
