import Mathlib
import OAI.Analysis.Conductivity.Fourier.TorusPoissonContinuous
import OAI.Analysis.Conductivity.Fourier.EndPoissonRepresentative

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma poissonMultiplier_sub_one_bound {m t : ℝ} (hm : 0≤ m) (ht : 0≤t) :
    ‖(Real.exp (-m*t):ℂ)-1‖≤ m*t := by
  rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr (by nlinarith : -m*t≤0)))]
  linarith [Real.add_one_le_exp (-m*t)]

lemma torusPoissonFlow_trace_rate (s : Fin 3 → ℝ) {t : ℝ} (ht : 0≤t)
    (f : TorusL2) (g : SpectralL2 (Fin 2 → ℤ))
    (hg : ∀ h,g h=(torusRate s h:ℂ)*mFourierCoeff f h) :
    ‖torusPoissonFlow s t f-f‖≤t*‖g‖ := by
  let F := (mFourierBasis (d:=Fin 2)).repr
  have hb : ‖F (torusPoissonFlow s t f-f)‖≤‖t • g‖ := by
    apply lp.norm_mono (p:=2) (by norm_num)
    intro h
    change ‖mFourierBasis.repr (torusPoissonFlow s t f-f) h‖≤‖(t • g) h‖
    rw [map_sub,lp.coeFn_sub,Pi.sub_apply,mFourierBasis_repr,mFourierBasis_repr,
      torusPoissonFlow_coeff,abs_of_nonneg ht,←sub_one_mul]
    change ‖((Real.exp (-torusRate s h*t):ℂ)-1)*mFourierCoeff f h‖≤‖t • g h‖
    rw [norm_mul,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht,hg,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (show 0≤torusRate s h from Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_right
      (poissonMultiplier_sub_one_bound (Real.sqrt_nonneg _) ht) (norm_nonneg _)).trans_eq (by dsimp [torusRate]; ring)
  simpa only [F,LinearIsometryEquiv.norm_map,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht] using hb

lemma torusRate_sq_polynomial_bound (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) :
    (torusRate s h)^2 ≤ (|s 0|+|s 1|+|s 2|)*((h 0:ℝ)^2+(h 1:ℝ)^2) := by
  let B := (h 0:ℝ)^2+(h 1:ℝ)^2
  have hB : 0≤B := by dsimp [B]; positivity
  have hab : 2*|(h 0:ℝ)| * |(h 1:ℝ)|≤B := by
    dsimp [B]
    nlinarith [sq_nonneg (|(h 0:ℝ)|-|(h 1:ℝ)|),sq_abs (h 0:ℝ),sq_abs (h 1:ℝ)]
  have hcross : 2*s 1*(h 0:ℝ)*(h 1:ℝ)≤|s 1| * B := by
    calc
      _ ≤ |2*s 1*(h 0:ℝ)*(h 1:ℝ)| := le_abs_self _
      _ = |s 1| * (2*|(h 0:ℝ)| * |(h 1:ℝ)|) := by
        rw [abs_mul,abs_mul,abs_mul]; norm_num; ring
      _ ≤ |s 1| * B := mul_le_mul_of_nonneg_left hab (abs_nonneg _)
  have hx := mul_le_mul_of_nonneg_right (le_abs_self (s 0)) (sq_nonneg (h 0:ℝ))
  have hy := mul_le_mul_of_nonneg_right (le_abs_self (s 2)) (sq_nonneg (h 1:ℝ))
  have hx' : |s 0| * (h 0:ℝ)^2≤|s 0| * B := mul_le_mul_of_nonneg_left
    (by dsimp [B]; nlinarith [sq_nonneg (h 1:ℝ)]) (abs_nonneg _)
  have hy' : |s 2| * (h 1:ℝ)^2≤|s 2| * B := mul_le_mul_of_nonneg_left
    (by dsimp [B]; nlinarith [sq_nonneg (h 0:ℝ)]) (abs_nonneg _)
  by_cases hq : 0≤torusQuadratic s h
  · rw [torusRate,Real.sq_sqrt hq]
    dsimp [torusQuadratic,B] at *
    nlinarith
  · rw [torusRate,Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hq),zero_pow (by decide)]
    positivity

lemma sourceAngularTrace_H1_summable (t : ℝ) {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    Summable (fun h : Fin 2 → ℤ => (1+(h 0:ℝ)^2+(h 1:ℝ)^2)*
      ‖mFourierCoeff (fun x => (f (sourceAngularCollar t x):ℂ)) h‖^2) := by
  let G : (Fin 4 → ℝ) → ℂ := fun z => (f (sourceAngularPolynomial t z):ℂ)
  have hG : ContDiff ℝ (↑(⊤ : ℕ∞)) G :=
    Complex.ofRealCLM.contDiff.comp (hf.comp (contDiff_sourceAngularPolynomial t))
  obtain ⟨K,hK⟩ := hG.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_Icc _ _) isCompact_Icc
  let F : C(UnitAddTorus (Fin 2),ℂ) :=
    ⟨fun x => G (sourceRayCoordinates x),hG.continuous.comp continuous_sourceRayCoordinates⟩
  have hdiff (j : Fin 2) (u : ℝ) (x : UnitAddTorus (Fin 2)) :
      ‖F (x+torusCoordinateShift j u)-F x‖≤((K:ℝ)*sourceRayConstant)*|u| := by
    have hh := hK.dist_le_mul _ (sourceRayCoordinates_mem (x+torusCoordinateShift j u))
      _ (sourceRayCoordinates_mem x)
    rw [dist_eq_norm,dist_eq_norm] at hh
    apply hh.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (sourceRayCoordinates_difference j u x) K.coe_nonneg
  exact torus_coordinate_H1_summable F (fun _ => (K:ℝ)*sourceRayConstant)
    (fun _ => mul_nonneg K.coe_nonneg sourceRayConstant_nonneg) hdiff

lemma sourceAngularTrace_rate_sq_summable (s : Fin 3 → ℝ) (t : ℝ)
    {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    Summable (fun h : Fin 2 → ℤ => (torusRate s h)^2*
      ‖mFourierCoeff (fun x => (f (sourceAngularCollar t x):ℂ)) h‖^2) := by
  refine ((sourceAngularTrace_H1_summable t hf).mul_left
    (|s 0|+|s 1|+|s 2|)).of_nonneg_of_le (fun h => by positivity) (fun h => ?_)
  rw [←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (torusRate_sq_polynomial_bound s h).trans
    (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

lemma centralTrace_rate_sq_summable (s : Fin 3 → ℝ)
    (f : centralSmoothFunctions) (i : Fin 3) :
    Summable (fun h => (torusRate s h)^2*‖centralTraceFourier f i h‖^2) := by
  simp only [centralTraceFourier_apply]
  have hf : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : Fin 3 → ℝ => f (sourcePairCoordinates y)) :=
    (central_smooth f).comp sourcePairCLE.contDiff
  fin_cases i
  · simpa [centralBoundary] using sourceAngularTrace_rate_sq_summable s centralThickness hf
  · simpa [centralBoundary,Function.comp_def] using
      sourceAngularTrace_rate_sq_summable s (-centralThickness) (hf.comp (sourceChildCoordinates_contDiff 1))
  · simpa [centralBoundary,Function.comp_def] using
      sourceAngularTrace_rate_sq_summable s (-centralThickness) (hf.comp (sourceChildCoordinates_contDiff (-1)))

lemma centralTrace_rate_memℓp (s : Fin 3 → ℝ) (f : centralSmoothFunctions) (i : Fin 3) :
    Memℓp (fun h => (torusRate s h:ℂ)*centralTraceFourier f i h) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).mpr
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,norm_mul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs] using centralTrace_rate_sq_summable s f i

end

open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma complexL2_norm_sq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : Lp ℂ 2 μ) : ‖f‖^2=∫ x,‖f x‖^2 ∂μ := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma continuousMap_L2_sq (f : C(UnitAddTorus (Fin 2),ℂ)) :
    (∫ θ,‖f θ‖^2)=‖f.toLp 2 volume ℂ‖^2 := by
  rw [complexL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (μ:=volume) (p:=2) (𝕜:=ℂ) f] with θ hθ
  rw [hθ]

lemma torusPoissonContinuous_trace_sq {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {t : ℝ} (ht : 0<t) (f : C(UnitAddTorus (Fin 2),ℂ))
    (g : SpectralL2 TorusModes)
    (hg : ∀ h,g h=(torusRate s h:ℂ)*mFourierCoeff (f.toLp 2 volume ℂ) h) :
    (∫ θ,‖torusPoissonContinuous s t (f.toLp 2 volume ℂ) θ-f θ‖^2)≤t^2*‖g‖^2 := by
  change (∫ θ,‖(torusPoissonContinuous s t (f.toLp 2 volume ℂ)-f) θ‖^2)≤_
  rw [continuousMap_L2_sq,map_sub,torusPoissonContinuous_toLp hs ht]
  have hh := torusPoissonFlow_trace_rate s ht.le (f.toLp 2 volume ℂ) g hg
  nlinarith [norm_nonneg (torusPoissonFlow s t (f.toLp 2 volume ℂ)-f.toLp 2 volume ℂ),
    mul_nonneg ht.le (norm_nonneg g)]

lemma endPoissonField_trace_sq {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {t : ℝ} (ht : 0<t)
    (f : spectralTraceGraph (torusRate s)) (q : C(UnitAddTorus (Fin 2),ℂ))
    (hq : ∀ h,f.val 0 h=mFourierCoeff (q.toLp 2 volume ℂ) h)
    (g : SpectralL2 TorusModes) (hg : ∀ h,g h=(torusRate s h:ℂ)*f.val 0 h) :
    (∫ θ,‖endPoissonField s f 0 (t,θ)-q θ‖^2)≤t^2*‖g‖^2 := by
  have he (θ : UnitAddTorus (Fin 2)) :
      endPoissonField s f 0 (t,θ)=torusPoissonContinuous s t (q.toLp 2 volume ℂ) θ := by
    rw [torusPoissonContinuous_apply hs ht]
    unfold endPoissonField
    apply tsum_congr
    intro h
    simp [endPoissonModeField,endModeCoefficient,hq]
  simp_rw [he]
  exact torusPoissonContinuous_trace_sq hs ht q g (fun h => by rw [hg,hq])

end ScalarConductivity

end

end OAI
