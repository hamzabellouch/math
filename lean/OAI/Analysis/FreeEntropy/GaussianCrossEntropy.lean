import OAI.Analysis.FreeEntropy.MatrixFlow

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory Set
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem smoothedSecond_integrable (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) :
    Integrable (fun x => smoothedDensity μ s x*‖x‖^2) := by
  have hi := (smoothedPolynomial_integrable μ hs hK hμ 1).sub (smoothedDensity_integrable μ hs)
  convert hi using 1
  funext x
  simp only [pow_one,Pi.sub_apply]
  ring
 theorem normalCross_integrable (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (v : ℝ) :
    Integrable (fun x => smoothedDensity μ s x*Real.log (normalKernel v x)) := by
  have he x : smoothedDensity μ s x*Real.log (normalKernel v x)=
      smoothedDensity μ s x*(-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*v))-
      (smoothedDensity μ s x*‖x‖^2)/(2*v) := by rw [normalKernel,Real.log_exp]; ring
  simp only [he]
  exact ((smoothedDensity_integrable μ hs).mul_const _).sub ((smoothedSecond_integrable μ hs hK hμ).div_const _)
 theorem normalCross_integral (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (v : ℝ) :
    -(∫x,smoothedDensity μ s x*Real.log (normalKernel v x))=
      (Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*v)+(∫x,smoothedDensity μ s x*‖x‖^2)/(2*v) := by
  have he x : smoothedDensity μ s x*Real.log (normalKernel v x)=
      smoothedDensity μ s x*(-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*v))-
      (smoothedDensity μ s x*‖x‖^2)/(2*v) := by rw [normalKernel,Real.log_exp]; ring
  simp only [he]
  rw [integral_sub ((smoothedDensity_integrable μ hs).mul_const _)
    ((smoothedSecond_integrable μ hs hK hμ).div_const _),integral_mul_const,integral_div,smoothedDensity_integral μ hs]
  ring
 theorem density_event_toReal {Ω : Type u2} [MeasurableSpace Ω] (ν : Measure Ω)
    (f : Ω → ℝ) (hf : Integrable f ν) (hf0 : ∀x,0≤f x) (E : Set Ω) (hE : MeasurableSet E) :
    ((ν.withDensity (fun x => ENNReal.ofReal (f x))) E).toReal=∫x in E,f x ∂ν := by
  rw [withDensity_apply _ hE,← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_of_all _ hf0),
    ENNReal.toReal_ofReal (integral_nonneg hf0)]
 theorem classicalEntropy_event_gaussian (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K v z : ℝ} (hs : 0<s) (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (hv : 0<v) (hz : 0≤z)
    (E : Set (EuclideanSpace ℝ ι)) (hE : MeasurableSet E)
    (hα : ENNReal.ofReal (1/2:ℝ)≤(volume.withDensity (fun x => ENNReal.ofReal (smoothedDensity μ s x))) E)
    (hβ : normalLaw v E≤ENNReal.ofReal (Real.exp (-z))) :
    classicalEntropy μ s≤(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*v)+
      (∫x,smoothedDensity μ s x*‖x‖^2)/(2*v)-z/2+Real.log 2 := by
  have hfi := smoothedDensity_integrable μ hs
  have hgi := normalKernel_integrable (ι := ι) hv
  have hfm : (volume.withDensity (fun x => ENNReal.ofReal (smoothedDensity μ s x))) univ=1 := by
    rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ (fun x => (smoothedDensity_pos μ hs x).le)),smoothedDensity_integral μ hs]
    simp
  have hfE : (volume.withDensity (fun x => ENNReal.ofReal (smoothedDensity μ s x))) E≠⊤ :=
    ne_top_of_le_ne_top (by simp) ((measure_mono (subset_univ E)).trans_eq hfm)
  have ha := (ENNReal.ofReal_le_iff_le_toReal hfE).mp hα
  rw [density_event_toReal volume _ hfi (fun x => (smoothedDensity_pos μ hs x).le) E hE] at ha
  have hb := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hβ
  rw [normalLaw,density_event_toReal volume _ hgi (fun x => (normalKernel_pos v x).le) E hE,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] at hb
  have he := entropy_event_bound volume (smoothedDensity μ s) (normalKernel v)
    (smoothedDensity_pos μ hs) (normalKernel_pos v) hfi hgi (smoothedEntropy_integrable μ hs hK hμ)
    (normalCross_integrable μ hs hK hμ v) (smoothedDensity_integral μ hs) (normalKernel_integral hv) E hE hz ha hb
  rwa [normalCross_integral μ hs hK hμ v] at he
variable {n d : ℕ}
 theorem integral_heatLaw_totalSecond (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) :
    (∫x,totalSecond (matrixMoment x) ∂matrixHeatLaw μ s)=(d:ℝ)⁻¹*(∫x,smoothedDensity μ (s/d) x*‖x‖^2) := by
  rw [integral_matrixHeatLaw μ hs hd]
  simp only [totalSecond_matrix,mul_left_comm _ (d:ℝ)⁻¹,integral_const_mul]
 theorem normalizedEntropy_event_gaussian (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsProbabilityMeasure μ]
    {s K v : ℝ} (hs : 0<s) (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (hv : 0<v)
    (E : Set (MatrixCoordinates n d)) (hE : MeasurableSet E)
    (hα : ENNReal.ofReal (1/2:ℝ)≤ matrixHeatLaw μ s E)
    (hβ : normalLaw (v/d) E≤ENNReal.ofReal (Real.exp (-4*(d:ℝ)^2))) :
    normalizedMatrixEntropy μ s≤(n:ℝ)/2*Real.log (2*Real.pi*v)+
      (∫x,totalSecond (matrixMoment x) ∂matrixHeatLaw μ s)/(2*v)-2+Real.log 2/(d:ℝ)^2 := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have he := classicalEntropy_event_gaussian μ (div_pos hs hd') hK hμ (div_pos hv hd')
    (show 0≤4*(d:ℝ)^2 by positivity) E hE hα (by simpa only [neg_mul] using hβ)
  have hlog : Real.log (2*Real.pi*(v/d))=Real.log (2*Real.pi*v)-Real.log d := by
    rw [show 2*Real.pi*(v/d)=(2*Real.pi*v)/d by ring,Real.log_div (by positivity) hd'.ne']
  rw [hlog] at he
  rw [integral_heatLaw_totalSecond hd μ hs]
  unfold normalizedMatrixEntropy
  have hh := div_le_div_of_nonneg_right he (sq_nonneg (d:ℝ))
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] at hh
  convert add_le_add hh (le_refl ((n:ℝ)/2*Real.log d)) using 1 ; first | rfl | (field_simp; ring)
end FiniteEntropySeparation

end

end OAI
