import OAI.Analysis.Mahler.StripJacobian
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace OAI

namespace SymmetricMahler
open Real Complex Set Finset MeasureTheory
open scoped Topology ENNReal Pointwise
open MahlerConformal
variable {n N : ℕ}

noncomputable def stripSublevel (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) := stripDomain A ∩ {z | stripTau A m z < 1}

lemma isOpen_stripDomain (A : Matrix (Fin N) (Fin n) ℝ) : IsOpen (stripDomain A) := by
  have he : stripDomain A = ⋂ j, (stripCoordinateCLM A j) ⁻¹' Omega := by
    ext z
    simp only [stripDomain, mem_ofPred_eq, mem_iInter, Set.mem_preimage,stripCoordinateCLM_apply]
  rw [he]
  exact isOpen_iInter_of_finite (fun j => isOpen_Omega.preimage (stripCoordinateCLM A j).continuous)

lemma continuousOn_stripTau (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) :
    ContinuousOn (stripTau A m) (stripDomain A) := by
  have hc : ∀ j, ContinuousOn (fun z => ‖inverseF (stripCoordinate A z j)‖^(2*m : ℕ)) (stripDomain A) := by
    intro j
    have hi : ContinuousOn (fun z => inverseF (stripCoordinate A z j)) (stripDomain A) := by
      apply differentiableOn_inverseF.continuousOn.comp
      · have h : ContinuousOn (stripCoordinateCLM A j) (stripDomain A) := (stripCoordinateCLM A j).continuous.continuousOn
        exact h.congr (fun z _ => (stripCoordinateCLM_apply A j z).symm)
      · intro z hz
        exact hz j
    exact hi.norm.pow _
  have h := continuousOn_finsetSum (univ : Finset (Fin N)) (fun j _ => hc j)
  convert h using 1
  funext z
  unfold stripTau
  apply sum_congr rfl
  intro j _
  rw [show 2*(m : ℝ) = ((2*m : ℕ) : ℝ) by norm_cast,Real.rpow_natCast]

lemma isOpen_stripSublevel (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) :
    IsOpen (stripSublevel A m) :=
  (continuousOn_stripTau A m).isOpen_inter_preimage (isOpen_stripDomain A) isOpen_Iio

noncomputable def stripHessianDet (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (weightedGram A (fun j => hessianWeight m (inverseF (stripCoordinate A z j))
    (deriv inverseF (stripCoordinate A z j)))).det

/-- Change of variables for the literal finite-strip map, allowing vanishing
Jacobian values. Neither local invertibility nor a change-of-variables premise
is assumed. -/
theorem stripMap_volume_eq (A : Matrix (Fin N) (Fin n) ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 2 ≤ m) :
    volume (stripMap A m '' stripSublevel A m) =
      ∫⁻ z in stripSublevel A m,
        ENNReal.ofReal ((4/(Real.pi*(m : ℝ)))^n*stripHessianDet A m z) := by
  let : (volume : Measure ((Fin n → ℝ) × (Fin n → ℝ))).IsAddHaarMeasure := by
    simpa only [Measure.volume_eq_prod] using!
      (Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin n → ℝ)) (volume : Measure (Fin n → ℝ)))
  have hder : ∀ z ∈ stripSublevel A m,
      HasFDerivWithinAt (stripMap A m) (stripDerivative A m z) (stripSublevel A m) z :=
    fun z hz => (hasFDerivAt_stripMap A m hz.1).hasFDerivWithinAt
  have hinj : InjOn (stripMap A m) (stripSublevel A m) :=
    (stripMap_injOn A hA (show 0 < m by omega)).mono inter_subset_left
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume (isOpen_stripSublevel A m).measurableSet hder hinj]
  apply setLIntegral_congr_fun (isOpen_stripSublevel A m).measurableSet
  intro z hz
  dsimp only
  rw [abs_det_stripDerivative A hm hz.1]
  rfl

/-- Pointwise containment in K times a scaled polar body. -/
theorem stripMap_image_subset_product (A : Matrix (Fin N) (Fin n) ℝ)
    {m : ℕ} (hm : 2 ≤ m) :
    stripMap A m '' stripSublevel A m ⊆ stripBody A ×ˢ
      ((1+(N : ℝ)*planarError m) • coordinatePolar (stripBody A)) := by
  rintro _ ⟨z,hz,rfl⟩
  refine ⟨?_,?_⟩
  · exact stripDomain_realPart A (z := z) hz.1
  · have hc : 0 < 1+(N : ℝ)*planarError m := by
      have := planarError_nonneg (m : ℝ)
      positivity
    refine ⟨fun i => (stripMap A m z).2 i/(1+(N : ℝ)*planarError m),?_,?_⟩
    · simpa only [Fintype.card_fin] using normalized_stripMap_mem_polar A hm hz.1 hz.2
    · funext i
      simp only [Pi.smul_apply,smul_eq_mul]
      field_simp
/-- The image-volume upper bound from the actual polar containment. -/
theorem stripMap_volume_le_product (A : Matrix (Fin N) (Fin n) ℝ)
    {m : ℕ} (hm : 2 ≤ m) :
    volume (stripMap A m '' stripSublevel A m) ≤
      volume (stripBody A) * (ENNReal.ofReal ((1+(N : ℝ)*planarError m)^n)*
        volume (coordinatePolar (stripBody A))) := by
  have hc : 0 ≤ 1+(N : ℝ)*planarError m := by
    have := planarError_nonneg (m : ℝ)
    positivity
  have h := measure_mono (μ := volume) (stripMap_image_subset_product A hm)
  rw [Measure.volume_eq_prod,Measure.prod_prod,
    Measure.addHaar_smul_of_nonneg volume hc] at h
  simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,mul_one, ← Measure.volume_eq_prod] using! h

end SymmetricMahler

end OAI
