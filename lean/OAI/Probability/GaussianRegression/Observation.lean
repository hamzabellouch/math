import OAI.Probability.GaussianRegression.Blocks
import OAI.Probability.GaussianRegression.Sphere

namespace OAI

/-!
Absolute continuity of noiseless spherical observation laws.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section ObservationAC
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma projectionLaw_absolutelyContinuous {ν : Measure E} [IsFiniteMeasure ν]
    {a m n : ℕ} {C : ℝ≥0∞} (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (hn : 1 ≤ n) (hmargin : n+m ≤ a) :
    projectionLaw ν m ≪ matrixLabelReference (E := E) m := by
  let ν' := C⁻¹ • ν
  have hCi : C⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hC
  let : IsFiniteMeasure ν' := ⟨by simp only [ν', Measure.smul_apply, smul_eq_mul]; finiteness⟩
  have hlocal : HasLocalMassBound ν' (a : ℝ) := by
    intro z _ r hr
    have hh := mul_le_mul' (le_rfl : C⁻¹ ≤ C⁻¹) (hν z r hr)
    simpa only [ν', Measure.smul_apply, smul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel hC hCt, one_mul, Real.rpow_natCast] using hh
  have hs : ν'.support ⊆ Metric.closedBall 0 1 :=
    (Measure.smul_absolutelyContinuous.support_mono).trans hsupport
  have hbound (S : Set ((Fin m → E) × (Fin m → ℝ))) :=
    projectionLaw_set_bound hlocal hs m n hn (by exact_mod_cast hmargin) S
  have he : projectionLaw ν' m = C⁻¹ • projectionLaw ν m := by
    simp only [projectionLaw, ν', Measure.prod_smul_right]
    exact Measure.map_smul _ (by fun_prop)
  intro S hS
  have h := hbound S
  rw [hS, ENNReal.zero_rpow_of_pos (by
    have : (1 : ℝ) < n+1 := by exact_mod_cast (by omega : 1 < n+1)
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr this)), mul_zero, he,
    Measure.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp (le_antisymm h bot_le)).resolve_left (ENNReal.inv_ne_zero.mpr hCt)

lemma sphere_observation_quasi [Nontrivial E] (hd : 3 ≤ Module.finrank ℝ E) :
    Measure.QuasiMeasurePreserving
      (fun z : (Metric.sphere (0 : E) 1) × E => (z.2, ⟪z.1.val,z.2⟫))
      ((sphereLaw (E := E)).prod (stdGaussian E)) ((stdGaussian E).prod volume) := by
  have hac : projectionLaw (ambientSphereLaw (E := E)) 1 ≪ matrixLabelReference (E := E) 1 := by
    apply projectionLaw_absolutelyContinuous (a := 2) (n := 1)
      (C := ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E))
    · intro z r hr
      exact ambientSphereLaw_closedBall z hr 2 (by omega)
    · positivity
    · exact ENNReal.ofReal_ne_top
    · exact ambientSphereLaw_support.trans Metric.sphere_subset_closedBall
    · omega
    · omega
  have hp : Measure.QuasiMeasurePreserving
      (fun z : (Fin 1 → E) × E => (z.1, fun j => ⟪z.2,z.1 j⟫))
      ((Measure.pi (fun _ : Fin 1 => stdGaussian E)).prod (ambientSphereLaw (E := E)))
      (matrixLabelReference (E := E) 1) := ⟨by fun_prop, hac⟩
  have h1 := ((measurePreserving_funUnique (stdGaussian E) (Fin 1)).symm
      (MeasurableEquiv.funUnique (Fin 1) E)).prod
    (measurable_subtype_coe.measurePreserving (sphereLaw (E := E)))
  have h2 := (measurePreserving_funUnique (stdGaussian E) (Fin 1)).prod
    (volume_preserving_funUnique (Fin 1) ℝ)
  have h3 := h2.quasiMeasurePreserving.comp (hp.comp (h1.quasiMeasurePreserving.comp
    Measure.measurePreserving_swap.quasiMeasurePreserving))
  convert h3 using 1
  ext z <;> simp [MeasurableEquiv.funUnique]

end ObservationAC

end NoiselessRegression

end

end OAI
