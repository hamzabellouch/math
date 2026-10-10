import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.L2MultiplierDistribution
import OAI.Analysis.CoulombRadii.FormDomain.WeakSchwartzDerivative

namespace OAI

section
open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology SchwartzMap LineDeriv FourierTransform ComplexConjugate ContDiff
noncomputable section
namespace Coulomb
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma l2_weakDeriv_fourier {u d : Lp ℂ 2 (volume:Measure E)} (a:E)
    (hw : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*u x)=-(∫ x,(φ x:ℂ)*d x)) :
    (𝓕 d : Lp ℂ 2 (volume:Measure E)) =ᵐ[volume]
      fun ξ => (2*Real.pi*Complex.I)*(inner ℝ ξ a:ℂ)*(𝓕 u : Lp ℂ 2 (volume:Measure E)) ξ := by
  have H := congrArg (fun T:𝓢'(E,ℂ) => 𝓕 T) (l2_weakDeriv_tempered a hw)
  rw [TemperedDistribution.fourier_lineDerivOp_eq,Lp.fourier_toTemperedDistribution_eq,
    Lp.fourier_toTemperedDistribution_eq] at H
  have hg : Continuous (fun ξ:E => (2*Real.pi*Complex.I)*(inner ℝ ξ a:ℂ)) := by fun_prop
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 d : Lp ℂ 2 (volume:Measure E))).locallyIntegrable (by norm_num))
    (((Lp.memLp (𝓕 u : Lp ℂ 2 (volume:Measure E))).locallyIntegrable (by norm_num)).continuous_mul hg)
  intro φ hφ hc
  let χ : E → ℂ := fun x => (φ x:ℂ)
  have hχ : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp hφ
  have hχc : HasCompactSupport χ := hc.comp_left (g:=fun r:ℝ => (r:ℂ)) (by simp)
  let Φ : 𝓢(E,ℂ) := hχc.toSchwartzMap hχ
  have ht : (fun ξ:E => (inner ℝ ξ a:ℂ)).HasTemperateGrowth := by fun_prop
  have HH := congrArg (fun T:𝓢'(E,ℂ) => T Φ) H
  simp only [smul_apply,smul_eq_mul,
    TemperedDistribution.smulLeftCLM_apply_apply,Lp.toTemperedDistribution_apply] at HH
  change (2*Real.pi*Complex.I)*(∫ x,
    (SchwartzMap.smulLeftCLM ℂ (fun ξ:E => (inner ℝ ξ a:ℂ)) Φ) x * (𝓕 u : Lp ℂ 2 (volume:Measure E)) x)=
      ∫ x,Φ x*(𝓕 d : Lp ℂ 2 (volume:Measure E)) x at HH
  rw [←integral_const_mul] at HH
  calc
    _=∫ x,Φ x*(𝓕 d : Lp ℂ 2 (volume:Measure E)) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Φ,χ,HasCompactSupport.toSchwartzMap_toFun,Complex.real_smul]
    _= _ := HH.symm
    _= _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [SchwartzMap.smulLeftCLM_apply ht,smul_eq_mul,Φ,χ,
        HasCompactSupport.toSchwartzMap_toFun,Complex.real_smul]
      ring

lemma l2_weakDeriv_fourier_energy {u d : Lp ℂ 2 (volume:Measure E)} (a:E)
    (hw : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*u x)=-(∫ x,(φ x:ℂ)*d x)) :
    Integrable (fun ξ => (2*Real.pi*inner ℝ ξ a)^2*
      ‖(𝓕 u : Lp ℂ 2 (volume:Measure E)) ξ‖^2) ∧
    (∫ ξ,(2*Real.pi*inner ℝ ξ a)^2*‖(𝓕 u : Lp ℂ 2 (volume:Measure E)) ξ‖^2)=‖d‖^2 := by
  have h := l2_weakDeriv_fourier a hw
  have he : (fun ξ => ‖(𝓕 d : Lp ℂ 2 (volume:Measure E)) ξ‖^2) =ᵐ[volume]
      fun ξ => (2*Real.pi*inner ℝ ξ a)^2*‖(𝓕 u : Lp ℂ 2 (volume:Measure E)) ξ‖^2 := by
    filter_upwards [h] with ξ hξ
    rw [hξ,fourierMultiplier_norm_sq]
  refine ⟨((Lp.memLp (𝓕 d : Lp ℂ 2 (volume:Measure E))).integrable_norm_pow (by norm_num)).congr he,?_⟩
  rw [←integral_congr_ae he,←l2_norm_sq_fourier]
  exact congrArg (fun t:ℝ => t^2) ((Lp.fourierTransformₗᵢ E ℂ).norm_map d)
end Coulomb
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal Topology ComplexConjugate
noncomputable section
namespace Coulomb
variable {X:Type*} [MeasurableSpace X] {μ:Measure X}
def cutL2 (s:Set X) (hs:MeasurableSet s) (u:Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ((Lp.memLp u).indicator hs).toLp (s.indicator u)
lemma cutL2_ae (s:Set X) (hs:MeasurableSet s) (u:Lp ℂ 2 μ) :
    cutL2 s hs u =ᵐ[μ] s.indicator u := MemLp.coeFn_toLp _
lemma cutL2_norm_le (s:Set X) (hs:MeasurableSet s) (u:Lp ℂ 2 μ) :
    ‖cutL2 s hs u‖≤‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [cutL2_ae s hs u] with x hx
  rw [hx]
  by_cases hx:x∈s <;> simp [hx]
lemma cutL2_sub (s:Set X) (hs:MeasurableSet s) (u v:Lp ℂ 2 μ) :
    cutL2 s hs (u-v)=cutL2 s hs u-cutL2 s hs v := by
  apply Lp.ext
  filter_upwards [cutL2_ae s hs (u-v),cutL2_ae s hs u,cutL2_ae s hs v,
    Lp.coeFn_sub u v,Lp.coeFn_sub (cutL2 s hs u) (cutL2 s hs v)] with x h h1 h2 huv h3
  rw [h,h3]
  simp only [Pi.sub_apply]
  rw [h1,h2]
  by_cases hx:x∈s
  · simp only [Set.indicator_of_mem hx,huv,Pi.sub_apply]
  · simp only [Set.indicator_of_notMem hx,sub_self]
lemma cutL2_add_compl (s:Set X) (hs:MeasurableSet s) (u:Lp ℂ 2 μ) :
    cutL2 s hs u+cutL2 sᶜ hs.compl u=u := by
  apply Lp.ext
  filter_upwards [cutL2_ae s hs u,cutL2_ae sᶜ hs.compl u,
    Lp.coeFn_add (cutL2 s hs u) (cutL2 sᶜ hs.compl u)] with x h1 h2 h3
  rw [h3]
  simp only [Pi.add_apply]
  rw [h1,h2]
  by_cases hx:x∈s <;> simp [hx]
lemma l2_norm_sq_integral (u:Lp ℂ 2 μ) : ‖u‖^2=∫ x,‖u x‖^2 ∂μ := by
  have h := congrArg Complex.re (L2.inner_def u u (𝕜:=ℂ))
  rw [inner_self_eq_norm_sq_to_K] at h
  change ((‖u‖:ℂ)^2).re=(∫ x,inner ℂ (u x) (u x) ∂μ).re at h
  rw [←Complex.ofReal_pow,Complex.ofReal_re] at h
  rw [h]
  change RCLike.re (∫ x,inner ℂ (u x) (u x) ∂μ)=_
  rw [←integral_re (L2.integrable_inner (𝕜:=ℂ) u u)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [inner_self_eq_norm_sq_to_K,←Complex.ofReal_pow]
lemma cutL2_norm_sq (s:Set X) (hs:MeasurableSet s) (u:Lp ℂ 2 μ) :
    ‖cutL2 s hs u‖^2=∫ x in s,‖u x‖^2 ∂μ := by
  rw [l2_norm_sq_integral,←integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [cutL2_ae s hs u] with x hx
  rw [hx]
  by_cases h:x∈s <;> simp [h]
lemma cutL2_mono_norm {s t:Set X} (hs:MeasurableSet s) (ht:MeasurableSet t)
    (hst:s⊆t) (u:Lp ℂ 2 μ) : ‖cutL2 s hs u‖≤‖cutL2 t ht u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [cutL2_ae s hs u,cutL2_ae t ht u] with x hx hy
  rw [hx,hy]
  by_cases h:x∈s
  · simp [h,hst h]
  · simp [h]
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform BigOperators ContDiff
noncomputable section
namespace Coulomb
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
lemma l2_gradient_fourier_moment
    (u:Lp ℂ 2 (volume:Measure (EuclideanSpace ℝ ι)))
    (d:ι → Lp ℂ 2 (volume:Measure (EuclideanSpace ℝ ι)))
    (hw:∀ i (φ:EuclideanSpace ℝ ι → ℝ),ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x (EuclideanSpace.single i 1):ℂ)*u x)=-(∫ x,(φ x:ℂ)*d i x)) :
    Integrable (fun ξ => (2*Real.pi)^2*‖ξ‖^2*‖(𝓕 u:Lp ℂ 2 volume) ξ‖^2) ∧
    (∫ ξ,(2*Real.pi)^2*‖ξ‖^2*‖(𝓕 u:Lp ℂ 2 volume) ξ‖^2)=∑ i,‖d i‖^2 := by
  have H i := l2_weakDeriv_fourier_energy (EuclideanSpace.single i 1) (hw i)
  have he (ξ:EuclideanSpace ℝ ι) :
      (∑ i,(2*Real.pi*inner ℝ ξ (EuclideanSpace.single i 1))^2*‖(𝓕 u:Lp ℂ 2 volume) ξ‖^2)=
        (2*Real.pi)^2*‖ξ‖^2*‖(𝓕 u:Lp ℂ 2 volume) ξ‖^2 := by
    simp only [EuclideanSpace.inner_single_right,conj_trivial,one_mul,mul_pow]
    rw [←Finset.sum_mul,←Finset.mul_sum,←EuclideanSpace.real_norm_sq_eq]
  have hi := integrable_finsetSum Finset.univ (fun i _ => (H i).1)
  refine ⟨hi.congr (Filter.Eventually.of_forall he),?_⟩
  rw [←integral_congr_ae (Filter.Eventually.of_forall he),integral_finsetSum _ (fun i _ => (H i).1)]
  exact Finset.sum_congr rfl (fun i _ => (H i).2)

lemma l2_fourier_tail_bound
    (u:Lp ℂ 2 (volume:Measure (EuclideanSpace ℝ ι)))
    (d:ι → Lp ℂ 2 (volume:Measure (EuclideanSpace ℝ ι)))
    (hw:∀ i (φ:EuclideanSpace ℝ ι → ℝ),ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x (EuclideanSpace.single i 1):ℂ)*u x)=-(∫ x,(φ x:ℂ)*d i x))
    {R:ℝ} (hR:0<R) :
    (2*Real.pi)^2*R^2*‖cutL2 (Metric.ball (0:EuclideanSpace ℝ ι) R)ᶜ
      measurableSet_ball.compl (𝓕 u)‖^2 ≤ ∑ i,‖d i‖^2 := by
  obtain ⟨hi,he⟩ := l2_gradient_fourier_moment u d hw
  rw [cutL2_norm_sq,←he,←integral_const_mul]
  apply (integral_mono_ae
    (((Lp.memLp (𝓕 u:Lp ℂ 2 volume)).integrable_norm_pow (by norm_num)).restrict.const_mul _)
    hi.restrict ?_).trans
  · exact setIntegral_le_integral hi (Filter.Eventually.of_forall fun ξ => by positivity)
  · filter_upwards [ae_restrict_mem measurableSet_ball.compl] with ξ hξ
    have hξR : R≤‖ξ‖ := by simpa [Metric.mem_ball,dist_zero_right,not_lt] using hξ
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hξR 2) (sq_nonneg _)) (sq_nonneg _)

lemma bounded_gradient_frequency_tight
    (u:ℕ → Lp ℂ 2 (volume:Measure (EuclideanSpace ℝ ι)))
    (d:ℕ → ι → Lp ℂ 2 (volume:Measure (EuclideanSpace ℝ ι)))
    (hw:∀ n i (φ:EuclideanSpace ℝ ι → ℝ),ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x (EuclideanSpace.single i 1):ℂ)*u n x)=-(∫ x,(φ x:ℂ)*d n i x))
    (K:ℝ) (hK:∀ n,∑ i,‖d n i‖^2≤K) (ε:ℝ) (hε:0<ε) :
    ∃ R:ℝ,0<R ∧ ∀ n,‖cutL2 (Metric.ball (0:EuclideanSpace ℝ ι) R)ᶜ
      measurableSet_ball.compl (𝓕 (u n))‖≤ε := by
  have hKn:0≤K := (Finset.sum_nonneg fun i _ => sq_nonneg ‖d 0 i‖).trans (hK 0)
  let R:ℝ := (Real.sqrt K+1)/(2*Real.pi*ε)
  have hR:0<R := by dsimp [R]; positivity
  refine ⟨R,hR,?_⟩
  intro n
  have h := (l2_fourier_tail_bound (u n) (d n) (hw n) hR).trans (hK n)
  have he : (2*Real.pi)^2*R^2*ε^2=(Real.sqrt K+1)^2 := by
    dsimp [R]
    field_simp
  have hlt:K<(Real.sqrt K+1)^2 := by
    have hh:=Real.sq_sqrt hKn
    have hp:=Real.sqrt_nonneg K
    nlinarith
  have hc : 0<(2*Real.pi)^2*R^2 := by positivity
  by_contra hn
  have hp : ε<‖cutL2 (Metric.ball (0:EuclideanSpace ℝ ι) R)ᶜ measurableSet_ball.compl (𝓕 (u n))‖ := lt_of_not_ge hn
  have hs := sq_lt_sq₀ hε.le (norm_nonneg _) |>.mpr hp
  nlinarith
end Coulomb
end

end

end OAI
