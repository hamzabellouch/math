import OAI.MeasureTheory.Falconer.Fourier.FourierSlice
import Mathlib.Analysis.SpecialFunctions.PolarCoord

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

theorem periodic_lintegral_interval {T : ℝ} (hT : 0 < T)
    (f : ℝ → ℝ≥0∞) (hf : Function.Periodic f T) (a : ℝ) :
    (∫⁻ θ in Ioc a (a+T), f θ) = ∫⁻ θ in Ioc 0 T, f θ := by
  let : Fact (0 < T) := ⟨hT⟩
  have h₁ := AddCircle.lintegral_preimage T a hf.lift
  have h₂ := AddCircle.lintegral_preimage T 0 hf.lift
  simpa using h₁.trans h₂.symm

theorem periodic_lintegral_shift {T : ℝ} (hT : 0 < T)
    (f : ℝ → ℝ≥0∞) (hf : Function.Periodic f T) (c : ℝ) :
    (∫⁻ θ in Ioc 0 T, f (θ+c)) = ∫⁻ θ in Ioc 0 T, f θ := by
  let : Fact (0 < T) := ⟨hT⟩
  have h₁ := AddCircle.lintegral_preimage T 0
    (fun θ : AddCircle T => hf.lift (θ+(c : AddCircle T)))
  have h₂ := AddCircle.lintegral_preimage T 0 hf.lift
  have h₃ := lintegral_add_right_eq_self (μ := (volume : Measure (AddCircle T))) hf.lift (c : AddCircle T)
  simpa only [zero_add, ← QuotientAddGroup.mk_add, Function.Periodic.lift_coe] using h₁.trans (h₃.trans h₂.symm)

noncomputable def sourceDirection (θ : ℝ) : Plane :=
  Complex.orthonormalBasisOneI.repr (Real.cos θ + Real.sin θ * Complex.I)

theorem normal_eq_direction (θ : ℝ) :
    sourceNormal θ = sourceDirection (θ+Real.pi/2) := by
  ext i
  fin_cases i <;> simp [sourceNormal, sourceDirection,
    Complex.orthonormalBasisOneI_repr_apply, Real.cos_add, Real.sin_add, -Complex.ofReal_sin, -Complex.ofReal_cos]

@[fun_prop] theorem continuous_sourceDirection : Continuous sourceDirection := by
  unfold sourceDirection
  fun_prop

theorem sourceDirection_periodic : Function.Periodic sourceDirection (2*Real.pi) := by
  intro θ
  simp [sourceDirection]

theorem plane_polar_lintegral (f : Plane → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ θ in Ioc 0 (2*Real.pi), ∫⁻ r in Ioi (0:ℝ),
      ENNReal.ofReal r * f (r • sourceDirection θ)) = ∫⁻ z : Plane, f z := by
  have h := Complex.lintegral_comp_polarCoord_symm
    (fun z => f (Complex.orthonormalBasisOneI.repr z))
  have hμ := (LinearIsometryEquiv.measurePreserving
    Complex.orthonormalBasisOneI.repr).lintegral_comp_emb
      Complex.orthonormalBasisOneI.repr.toHomeomorph.measurableEmbedding f
  rw [hμ] at h
  change (∫⁻ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal p.1 * f (Complex.orthonormalBasisOneI.repr
      (Complex.polarCoord.symm p))) = _ at h
  have he (r θ : ℝ) : Complex.orthonormalBasisOneI.repr
      (Complex.polarCoord.symm (r,θ)) = r • sourceDirection θ := by
    rw [Complex.polarCoord_symm_apply]
    change Complex.orthonormalBasisOneI.repr (r • (Real.cos θ + Real.sin θ * Complex.I)) = _
    exact Complex.orthonormalBasisOneI.repr.map_smul r _
  simp_rw [he] at h
  change (∫⁻ p : ℝ × ℝ, ENNReal.ofReal p.1 * f (p.1 • sourceDirection p.2)
    ∂(volume.prod volume).restrict (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi)) = _ at h
  rw [← Measure.prod_restrict, lintegral_prod _ (by fun_prop)] at h
  have hm : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * f (p.1 • sourceDirection p.2)) := by fun_prop
  rw [lintegral_lintegral_swap hm.aemeasurable] at h
  rw [restrict_Ioo_eq_restrict_Ioc] at h
  let F : ℝ → ℝ≥0∞ := fun θ => ∫⁻ r in Ioi (0:ℝ),
    ENNReal.ofReal r * f (r • sourceDirection θ)
  have hF : Function.Periodic F (2*Real.pi) := by
    intro θ
    simp only [F,sourceDirection_periodic θ]
  have ha := periodic_lintegral_interval (by positivity : 0 < 2*Real.pi) F hF (-Real.pi)
  have hend : -Real.pi+2*Real.pi = Real.pi := by ring
  rw [hend] at ha
  exact ha.symm.trans h

theorem norm_sourceDirection (θ : ℝ) : ‖sourceDirection θ‖ = 1 := by
  have h := Complex.norm_polarCoord_symm (1,θ)
  rw [sourceDirection,LinearIsometryEquiv.norm_map]
  simpa only [Complex.polarCoord_symm_apply,Prod.fst,Prod.snd,Complex.ofReal_one,one_mul,abs_one] using h

theorem plane_polar_weighted_lintegral (f : Plane → ℝ≥0∞) (hf : Measurable f) (s : ℝ) :
    (∫⁻ θ in Ioc 0 (2*Real.pi), ∫⁻ r in Ioi (0:ℝ),
      f (r • sourceDirection θ) * ENNReal.ofReal (r^(s-1))) =
        ∫⁻ z : Plane, f z * ENNReal.ofReal (‖z‖^(s-2)) := by
  rw [← plane_polar_lintegral _ (by fun_prop)]
  apply lintegral_congr
  intro θ
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  rw [norm_smul, norm_sourceDirection, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  have hpow : r * r^(s-2) = r^(s-1) := by
    nth_rw 1 [← Real.rpow_one r]
    rw [← Real.rpow_add hr]
    congr 1
    ring
  rw [mul_left_comm, ← ENNReal.ofReal_mul hr.le, hpow]

theorem normal_polar_weighted_lintegral (f : Plane → ℝ≥0∞) (hf : Measurable f) (s : ℝ) :
    (∫⁻ θ in Ioc 0 (2*Real.pi), ∫⁻ r in Ioi (0:ℝ),
      f (r • sourceNormal θ) * ENNReal.ofReal (r^(s-1))) =
        ∫⁻ z : Plane, f z * ENNReal.ofReal (‖z‖^(s-2)) := by
  simp_rw [normal_eq_direction]
  let F : ℝ → ℝ≥0∞ := fun θ => ∫⁻ r in Ioi (0:ℝ),
    f (r • sourceDirection θ) * ENNReal.ofReal (r^(s-1))
  have hF : Function.Periodic F (2*Real.pi) := by
    intro θ
    simp only [F,sourceDirection_periodic θ]
  exact (periodic_lintegral_shift (by positivity) F hF (Real.pi/2)).trans
    (plane_polar_weighted_lintegral f hf s)

theorem even_lintegral_real (f : ℝ → ℝ≥0∞) (he : ∀ x, f (-x) = f x) :
    (∫⁻ r : ℝ, f r) = 2 * ∫⁻ r in Ioi (0:ℝ), f r := by
  have h := lintegral_neg_eq_self (μ := (volume : Measure ℝ)) ((Ioi (0:ℝ)).indicator f)
  have hi (x : ℝ) : (Ioi (0:ℝ)).indicator f (-x) = (Iio (0:ℝ)).indicator f x := by
    by_cases hx : x < 0 <;> simp [Set.indicator, hx, he]
  simp_rw [hi] at h
  rw [lintegral_indicator measurableSet_Iio,lintegral_indicator measurableSet_Ioi] at h
  rw [← lintegral_add_compl f measurableSet_Ioi,compl_Ioi,
    ← restrict_Iio_eq_restrict_Iic,h,two_mul]

theorem even_polar_slice_average (f : Plane → ℝ≥0∞) (hf : Measurable f)
    (he : ∀ z, f (-z) = f z) (s : ℝ) :
    (∫⁻ θ in Ioc 0 (2*Real.pi), ∫⁻ r : ℝ,
      f (r • sourceNormal θ) * ENNReal.ofReal (|r|^(s-1))) =
        2 * ∫⁻ z : Plane, f z * ENNReal.ofReal (‖z‖^(s-2)) := by
  have h (θ : ℝ) : (∫⁻ r : ℝ,
      f (r • sourceNormal θ) * ENNReal.ofReal (|r|^(s-1))) =
      2 * ∫⁻ r in Ioi (0:ℝ), f (r • sourceNormal θ) * ENNReal.ofReal (r^(s-1)) := by
    rw [even_lintegral_real _ (by intro r; simp only [neg_smul, he,abs_neg])]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    rw [abs_of_pos hr]
  simp_rw [h]
  rw [lintegral_const_mul' _ _ (by norm_num),normal_polar_weighted_lintegral f hf s]

noncomputable def sourceSliceEnergy (μ : Measure Plane) (s θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ r : ℝ, ENNReal.ofReal (‖sourceFourier μ (r • sourceNormal θ)‖^2) *
    ENNReal.ofReal (|r|^(s-1))

theorem source_slice_average (μ : Measure Plane) [IsFiniteMeasure μ] (s : ℝ) :
    (∫⁻ θ in Ioc 0 (2*Real.pi), sourceSliceEnergy μ s θ) =
      2 * ∫⁻ z : Plane, ENNReal.ofReal (‖sourceFourier μ z‖^2) *
        ENNReal.ofReal (‖z‖^(s-2)) := by
  unfold sourceSliceEnergy
  refine even_polar_slice_average (fun z => ENNReal.ofReal (‖sourceFourier μ z‖^2))
    (by unfold sourceFourier; fun_prop) ?_ s
  intro z
  simp [sourceFourier,smul_neg,charFun_neg]

theorem source_slice_average_energy (μ : Measure Plane) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    ENNReal.ofReal (sourceEnergyConstant 2 s) *
      (∫⁻ θ in Ioc 0 (2*Real.pi), sourceSliceEnergy μ s θ) = 2 * rieszEnergy μ s := by
  rw [source_slice_average,planar_fourier_energy_identity μ hs hs2,mul_left_comm]

@[fun_prop] theorem measurable_sourceSliceEnergy (μ : Measure Plane) [IsFiniteMeasure μ]
    (s : ℝ) : Measurable (sourceSliceEnergy μ s) := by
  unfold sourceSliceEnergy
  have h : Measurable (fun p : ℝ × ℝ =>
    ENNReal.ofReal (‖sourceFourier μ (p.2 • sourceNormal p.1)‖^2) *
      ENNReal.ofReal (|p.2|^(s-1))) := by
    unfold sourceFourier sourceNormal
    fun_prop
  exact h.lintegral_prod_right

theorem finite_slice_average_of_ball_bound (μ : Measure Plane) [IsFiniteMeasure μ]
    {d C s : ℝ} (hs : 0 < s) (hs2 : s < 2) (hsd : s < d) (hb : BallBound μ d C) :
    (∫⁻ θ in Ioc 0 (2*Real.pi), sourceSliceEnergy μ s θ) < ∞ := by
  rw [source_slice_average]
  exact ENNReal.mul_lt_top (by norm_num) (finite_fourier_energy_of_ball_bound μ hs hs2 hsd hb)

end PlanarFalconer

end OAI
