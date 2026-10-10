import OAI.Analysis.FreeEntropy.GaussianRegularity

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory Set
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem smoothedPolynomial_integrable (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (m : ℕ) :
    Integrable (fun x => (1+‖x‖^2)^m*smoothedDensity μ s x) := by
  let D := |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)|
  let A := Real.exp (D+K^2/(2*s))
  have hi := (polynomial_gaussian_integrable (E := EuclideanSpace ℝ ι) (c := 1/(4*s)) (by positivity) m).const_mul A
  apply hi.mono' (((continuous_const.add (continuous_norm.pow 2)).pow m).mul (smoothedDensity_continuous μ hs)).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    simp only [Pi.mul_apply,Pi.add_apply,Pi.pow_apply]
    have hp := smoothedDensity_pos μ hs x
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (1+‖x‖^2)^m*smoothedDensity μ s x)]
    have h := (smoothedDensity_bounds μ hs (show s∈Icc s s from ⟨le_rfl,le_rfl⟩) (show |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D from le_rfl) hK hμ x).2
    have he : -‖x‖^2/(4*s)=-(1/(4*s))*‖x‖^2 := by ring
    rw [he] at h
    simpa only [A,mul_assoc,mul_left_comm] using mul_le_mul_of_nonneg_left h (show 0 ≤ (1+‖x‖^2)^m by positivity))
 theorem smoothedIntegrable_of_bound {F : Type u2} [NormedAddCommGroup F]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K)
    {f : EuclideanSpace ℝ ι → F} (hf : AEStronglyMeasurable f) (C : ℝ) (m : ℕ)
    (hb : ∀x,‖f x‖ ≤ C*(1+‖x‖^2)^m*smoothedDensity μ s x) : Integrable f := by
  apply ((smoothedPolynomial_integrable μ hs hK hμ m).const_mul C).mono' hf
  exact ae_of_all _ (fun x => by simpa only [mul_assoc] using hb x)
 theorem smoothedLog_continuous (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0<s) : Continuous (fun x => Real.log (smoothedDensity μ s x)) :=
  (smoothedDensity_continuous μ hs).log (fun x => (smoothedDensity_pos μ hs x).ne')
 theorem smoothedLog_constant (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) :
    ∃ L : ℝ,0 ≤ L ∧ ∀x,|1+Real.log (smoothedDensity μ s x)| ≤ L*(1+‖x‖^2) := by
  let D := |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)|
  refine ⟨1+D+(1+K^2)/s,by dsimp [D]; positivity,?_⟩
  intro x
  have h := smoothedLog_polynomial_bound μ hs (show s∈Icc s s from ⟨le_rfl,le_rfl⟩) (abs_nonneg _) (show |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D from le_rfl) hK hμ x
  have h' := abs_add_le (1:ℝ) (Real.log (smoothedDensity μ s x))
  norm_num only [abs_one] at h'
  dsimp [D]
  nlinarith [sq_nonneg ‖x‖]
 theorem smoothedEntropy_integrable (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) :
    Integrable (fun x => smoothedDensity μ s x*Real.log (smoothedDensity μ s x)) := by
  let D := |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)|
  apply smoothedIntegrable_of_bound μ hs hK hμ
    (((smoothedDensity_continuous μ hs).mul (smoothedLog_continuous μ hs)).aestronglyMeasurable)
    (D+(1+K^2)/s) 1
  intro x
  simp only [Pi.mul_apply]
  simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (smoothedDensity_pos μ hs x),pow_one]
  have h := smoothedLog_polynomial_bound μ hs (show s∈Icc s s from ⟨le_rfl,le_rfl⟩) (abs_nonneg _) (show |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D from le_rfl) hK hμ x
  nlinarith [mul_le_mul_of_nonneg_left h (smoothedDensity_pos μ hs x).le]
 theorem smoothedLog_mul_integrable (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K)
    {g : EuclideanSpace ℝ ι → ℝ} (hg : StronglyMeasurable g) (C : ℝ) (_hC : 0 ≤ C)
    (hb : ∀x,|g x| ≤ C*(1+‖x‖^2)*smoothedDensity μ s x) :
    Integrable (fun x => (1+Real.log (smoothedDensity μ s x))*g x) := by
  obtain ⟨L,hL,hlog⟩ := smoothedLog_constant μ hs hK hμ
  apply smoothedIntegrable_of_bound μ hs hK hμ
    (((continuous_const.add (smoothedLog_continuous μ hs)).stronglyMeasurable.mul hg).aestronglyMeasurable) (L*C) 2
  intro x
  simp only [Pi.mul_apply,Pi.add_apply]
  rw [Real.norm_eq_abs,abs_mul]
  calc _ ≤ (L*(1+‖x‖^2))*(C*(1+‖x‖^2)*smoothedDensity μ s x) :=
          mul_le_mul (hlog x) (hb x) (abs_nonneg _) (by positivity)
       _ = _ := by ring
 theorem smoothedScore_integrable (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (i : ι) :
    Integrable (fun x => (smoothedGradient μ s x i)^2/smoothedDensity μ s x) := by
  let C := (1+K)/s
  apply smoothedIntegrable_of_bound μ hs hK hμ
    (((smoothedGradient_measurable μ s i).pow 2).div (smoothedDensity_continuous μ hs).stronglyMeasurable).aestronglyMeasurable (C^2) 2
  intro x
  simp only [Pi.pow_apply,Pi.div_apply]
  have hp := smoothedDensity_pos μ hs x
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hp).mpr
  have hb := smoothedGradient_polynomial_bound μ hs le_rfl hK hμ x i
  have hh := pow_le_pow_left₀ (abs_nonneg _) hb 2
  simp only [sq_abs] at hh
  dsimp only [C]
  nlinarith
end FiniteEntropySeparation

end

end OAI
